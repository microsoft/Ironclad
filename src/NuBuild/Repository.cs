//--
// <copyright file="Repository.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;
    using System.Text;

    /// <summary>
    /// Tracker of BuildObjects, in their various forms.
    /// For virtual build objects, also provides the content store.
    /// </summary>
    /// <remarks>
    /// There is only one instance of this class in the system.
    /// This class includes functionality from the old ResultCache and
    /// NuObjContents classes.
    /// Old NuObjContents comment:
    /// This class keeps track of the data we've stored into nuobj/.
    /// The invariant is that we never read data out of nuobj/ if it's
    /// not data we put there ourselves this execution (perhaps by
    /// fetching it from the cache). Data from the cache is safe,
    /// because it is tracked by concreteIdentifier. But data in
    /// nuobj/ may be stale, leading us to build the wrong thing.
    /// (A wrong thing would be correctly labeled, so it won't poison
    /// the cache, but it wouldn't be the output the user asked for.)
    /// </remarks>
    internal class Repository
    {
        /// <summary>
        /// Collection of information about build objects.
        /// </summary>
        private Dictionary<BuildObject, RepositoryEntry> entries;

        /// <summary>
        /// Record of the verbs for which we've already added the
        /// output objects resulting from their (cached) execution.
        /// </summary>
        /// <remarks>
        /// This avoids re-adding the entire set if we ask for another object
        /// in the same verb's output list.  Note that this ignores the hash
        /// value of the verb; it assumes that the hash values don't change
        /// across a run of this process.
        /// </remarks>
        private HashSet<IVerb> alreadyAddedVerbs;

        /// <summary>
        /// The item cache we're using.
        /// </summary>
        private IItemCache itemCache;

        /// <summary>
        /// Initializes a new instance of the Repository class.
        /// </summary>
        /// <param name="itemCache">The item cache we're using.</param>
        public Repository(IItemCache itemCache)
        {
            this.itemCache = itemCache;

            this.entries = new Dictionary<BuildObject, RepositoryEntry>();
            this.alreadyAddedVerbs = new HashSet<IVerb>();
        }

        /// <summary>
        /// Reads a build object from the local filesystem and stores it in the
        /// cache.
        /// </summary>
        /// <param name="workingDirectory">
        /// Private directory for verb execution.
        /// </param>
        /// <param name="obj">The build object to store in the cache.</param>
        /// <param name="disposition">
        /// Disposition of verb which created this object (if known).
        /// </param>
        /// <returns>A BuildObjectValuePointer describing the object.</returns>
        public BuildObjectValuePointer Store(WorkingDirectory workingDirectory, BuildObject obj, Disposition disposition)
        {
            string contentHash = Util.hashFilesystemPath(workingDirectory.PathTo(obj));
            this.itemCache.StoreItemFromFile(ItemCacheContainer.Objects, contentHash, workingDirectory.PathTo(obj));
            this.Add(obj, disposition, contentHash, null);

            return new BuildObjectValuePointer(contentHash, obj.getRelativePath());
        }

        /// <summary>
        /// Fetches a build object and stores it in the local filesystem.
        /// </summary>
        /// <param name="workingDirectory">
        /// Directory under which to store the fetched object.
        /// </param>
        /// <param name="obj">The object to fetch.</param>
        public void Fetch(WorkingDirectory workingDirectory, BuildObject obj)
        {
            RepositoryEntry entry = this.FetchFresh(obj);

            // REVIEW: best way to determine this is a source file?
            ItemCacheContainer container;
            if (obj is SourcePath)
            {
                container = ItemCacheContainer.Sources;
            }
            else
            {
                container = ItemCacheContainer.Objects;
            }

            this.itemCache.FetchItemToFile(container, entry.Hash, workingDirectory.PathTo(obj));
        }

        /// <summary>
        /// Gets a readable stream for the given build object contents.
        /// </summary>
        /// <param name="obj">The object in question.</param>
        /// <returns>An open, readable stream to the contents.</returns>
        public TextReader OpenRead(BuildObject obj)
        {
            RepositoryEntry entry = this.FetchFresh(obj);

            // REVIEW: best way to determine this is a source file?
            ItemCacheContainer container;
            if (obj is SourcePath)
            {
                container = ItemCacheContainer.Sources;
            }
            else
            {
                container = ItemCacheContainer.Objects;
            }

            byte[] contents = this.itemCache.FetchItem(container, entry.Hash);
            MemoryStream stream = new MemoryStream(contents, false);
            return new StreamReader(stream);
        }

        /// <summary>
        /// Stores a result record in the cache.
        /// </summary>
        /// <param name="inputHash">
        /// Item cache hash key to store result under.
        /// </param>
        /// <param name="result">The result record to store.</param>
        public void StoreResult(string inputHash, ResultSummaryRecord result)
        {
            ItemCacheContainer container;
            if (result.IsVerificationTimeout || (result.Disposition is Failed))
            {
                container = ItemCacheContainer.FailedResults;
            }
            else
            {
                container = ItemCacheContainer.Results;
            }

            using (MemoryStream outStream = new MemoryStream())
            {
                using (StreamWriter outWriter = new StreamWriter(outStream))
                {
                    outWriter.Write(result.ToXml());
                }

                this.itemCache.StoreItem(container, inputHash, outStream.ToArray());
            }
        }

        /// <summary>
        /// Fetches a result record from the cache.
        /// </summary>
        /// <param name="inputHash">
        /// Item cache hash key the result is stored under.
        /// </param>
        /// <param name="includeFailedResults">
        /// Whether to return cached failures as well as successes.
        /// </param>
        /// <returns>
        /// The result record requested if available, otherwise returns a
        /// summary record with Stale disposition.
        /// </returns>
        public ResultSummaryRecord FetchResult(string inputHash, bool includeFailedResults = false)
        {
            byte[] result = this.itemCache.FetchItem(ItemCacheContainer.Results, inputHash);
            if ((result == null) && includeFailedResults)
            {
                result = this.itemCache.FetchItem(ItemCacheContainer.FailedResults, inputHash);
            }

            if (result != null)
            {
                MemoryStream resultStream = new MemoryStream(result);
                try
                {
                    using (StreamReader inReader = new StreamReader(resultStream))
                    {
                        string xmlSummary = inReader.ReadToEnd();
                        return ResultSummaryRecord.FromXml(xmlSummary);
                    }
                }
                catch (System.Xml.XmlException ex)
                {
                    throw new ObjectMissingFromCacheException(inputHash, "Malformed xml: " + ex.ToString());
                }
                finally
                {
                    resultStream.Dispose();
                }
            }
            else
            {
                return new ResultSummaryRecord(new Stale(), new BuildObjectValuePointer[] { }, false);
            }
        }

        /// <summary>
        /// Add information about a virtual object to the Repository,
        /// including its contents.
        /// </summary>
        /// <param name="obj">The object in question.</param>
        /// <param name="disposition">
        /// Disposition of the verb which created this object.
        /// </param>
        /// <param name="contents">Contents of the object.</param>
        public void StoreVirtual(BuildObject obj, Disposition disposition, VirtualContents contents)
        {
            Util.Assert(obj is VirtualBuildObject);
            this.Add(obj, disposition, null, contents);
        }

        /// <summary>
        /// Retrieves the virtual content referenced by the given build object.
        /// </summary>
        /// <param name="obj">The object in question.</param>
        /// <returns>The virtual contents of the object.</returns>
        public VirtualContents FetchVirtual(BuildObject obj)
        {
            return this.FetchFresh(obj).VirtualContents;
        }

        /// <summary>
        /// Gets the disposition of the verb that generated a build object.
        /// </summary>
        /// <param name="obj">The object in question.</param>
        /// <returns>Disposition of the object.</returns>
        public Disposition GetDisposition(BuildObject obj)
        {
            RepositoryEntry value = this.GetValue(obj);
            if (value != null)
            {
                return value.Disposition;
            }

            return new Stale();
        }

        /// <summary>
        /// Gets the hash of an object registered with this Repository.
        /// </summary>
        /// <param name="obj">The object in question.</param>
        /// <returns>
        /// The hash of the object (if known), otherwise null.
        /// </returns>
        public string GetHash(BuildObject obj)
        {
            string hash = null;

            RepositoryEntry value = this.GetValue(obj);
            if (value != null)
            {
                if (value.Disposition is Failed)
                {
                    hash = null;
                }
                else if (obj is VirtualBuildObject)
                {
                    hash = "virtual";
                }
                else
                {
                    hash = value.Hash;
                }
            }

            return hash;
        }

        /// <summary>
        /// Adds the output objects from a cached verb execution to the
        /// repository, and ensures they are present in the item cache.
        /// </summary>
        /// <param name="verb">The verb whose outputs to add.</param>
        /// <param name="resultRecord">
        /// The result summary record of the verb execution.
        /// </param>
        /// <remarks>
        /// Call only when output objects are known to be cached
        /// (i.e. because FetchResult returned non-Stale).
        /// REVIEW: This function probably shouldn't be in this file.
        /// It does something similar for cached verb results that
        /// the scheduler's recordResult method does for new verb
        /// executions.  Move this there and/or refactor?
        /// </remarks>
        public void AddVerbResults(IVerb verb, ResultSummaryRecord resultRecord)
        {
            if (this.alreadyAddedVerbs.Contains(verb))
            {
                // We only need to add a cached verb execution's outputs once.
                return;
            }

            Disposition disposition = resultRecord.Disposition;

            // REVIEW: In the below, some of these IEnumerables should be
            // HashSets, and the HashSet should be a simple List.

            // Create a collection of the potential outputs.
            IEnumerable<BuildObject> outputs = verb.getOutputs();
            IEnumerable<BuildObject> failureOutputs = verb.getFailureOutputs();
            outputs = outputs.Concat(failureOutputs);
            Dictionary<string, BuildObject> potentialOutputs = new Dictionary<string, BuildObject>();
            foreach (BuildObject obj in outputs)
            {
                potentialOutputs.Add(obj.getRelativePath(), obj);
            }

            // Compare the actual outputs with the potential outputs,
            // and add the actual ones to the repository.
            HashSet<BuildObject> recorded = new HashSet<BuildObject>();
            foreach (BuildObjectValuePointer actualOutput in resultRecord.Outputs)
            {
                if (potentialOutputs.ContainsKey(actualOutput.RelativePath))
                {
                    BuildObject obj = potentialOutputs[actualOutput.RelativePath];
                    // TODO: Verify that the object exists in the item cache!
                    this.AddObject(obj, disposition, actualOutput.ObjectHash);
                    recorded.Add(obj);

                    // Store a copy of this verb output as a file in the real nuobj directory.
                    Util.Assert(actualOutput.RelativePath.StartsWith(BuildEngine.theEngine.getObjRoot(), StringComparison.Ordinal));
                    this.itemCache.FetchItemToFile(ItemCacheContainer.Objects, actualOutput.ObjectHash, IronRootDirectory.PathTo(actualOutput.RelativePath));
                }
                else
                {
                    // Complain if we find interloping outputs.
                    throw new Exception("Distressing: some actual verb outputs aren't in the verb's list of potential outputs");
                }
            }

            // Create a collection of missing outputs.
            IEnumerable<BuildObject> unrecorded = outputs.Except(recorded).Except(failureOutputs);

            // For non-Failed verb runs, complain if all expected outputs don't
            // show up in the actual outputs.
            Util.Assert(unrecorded.Count() == 0 || disposition is Failed);

            // For cached verb runs with permanent failures (i.e. disposition
            // is Failed), we want to mark all of the expected outputs as Failed
            // even if no corresponding actual output was produced during the
            // failed verb run.
            foreach (BuildObject obj in unrecorded)
            {
                this.AddObject(obj, disposition, null);
            }

            // Remember that we've already added this verb's outputs.
            this.alreadyAddedVerbs.Add(verb);
        }

        /// <summary>
        /// Add information about an object to the Repository.
        /// The object path must be under the object root.
        /// </summary>
        /// <param name="obj">The object in question.</param>
        /// <param name="disposition">
        /// Disposition of the verb which created this object.
        /// </param>
        /// <param name="hash">Hash of the object's contents.</param>
        public void AddObject(BuildObject obj, Disposition disposition, string hash)
        {
            Util.Assert(obj.getRelativePath().StartsWith(BuildEngine.theEngine.getObjRoot(), StringComparison.Ordinal));
            this.Add(obj, disposition, hash, null);
        }

        /// <summary>
        /// Gets the number of entries in this repository, for debugging.
        /// </summary>
        /// <returns>Number of objects recorded in this repository.</returns>
        internal int DbgCacheSize()
        {
            return this.entries.Count();
        }

        /// <summary>
        /// Fetches information about the given object in this repository.
        /// </summary>
        /// <param name="obj">The object to fetch.</param>
        /// <returns>Information about the object.</returns>
        private RepositoryEntry FetchFresh(BuildObject obj)
        {
            RepositoryEntry value = this.GetValue(obj);
            if (value == null)
            {
                throw new ObjectNotReadyException(obj);
            }

            if (value.Disposition is Failed)
            {
                throw new ObjectFailedException(obj, (Failed)value.Disposition);
            }

            Util.Assert(value.Disposition is Fresh); // This isn't really a 'not ready' condition; we shouldn't be here.  REVIEW: What is meant by this comment?
            return value;
        }

        /// <summary>
        /// Gets information about an object in this repository.
        /// Will add missing source objects to the repository as needed.
        /// </summary>
        /// <param name="obj">The object to look up.</param>
        /// <returns>Information about the object.</returns>
        /// <remarks>
        /// Returns null if obj isn't in this run's cache.
        /// Cannot return value.disposition==Stale, I guess?
        /// </remarks>
        private RepositoryEntry GetValue(BuildObject obj)
        {
            if (this.entries.ContainsKey(obj))
            {
                return this.entries[obj];
            }
            else
            {
                SourcePath src = obj as SourcePath;
                if (src != null)
                {
                    // Special case to get local source files into the
                    // repository (and the item cache).
                    // REVIEW: Should we require that source files are explicitly added?
                    try
                    {
                        // Complain if someone uses tabs or non-CRLF line endings in a source file.
                        // Visual Studio is pretty insistent on using tabs in solution (.sln) files, so we let it.
                        if ((src.Type == SourcePath.SourceType.Src) && (src.getExtension() != ".sln"))
                        {
                            if (!Util.CheckSourceFileForBadCharacters(IronRootDirectory.PathTo(obj)))
                            {
                                throw new SourceConfigurationError("Bad characters (tabs?) or non-CRLF line endings in source file " + obj.getRelativePath());
                            }
                        }

                        string hash = Util.hashFilesystemPath(IronRootDirectory.PathTo(obj));
                        this.itemCache.StoreItemFromFile(ItemCacheContainer.Sources, hash, IronRootDirectory.PathTo(obj));
                        this.Add(obj, new Fresh(), hash, null);
                    }
                    catch (IOException)
                    {
                        throw new SourceConfigurationError("Cannot find source path " + obj.getRelativePath());
                    }

                    return this.entries[obj];
                }
                else
                {
                    return null;
                }
            }
        }

        /// <summary>
        /// Add information about an object to the Repository.
        /// </summary>
        /// <param name="obj">The object to add.</param>
        /// <param name="disposition">
        /// Disposition of the verb which created this object.
        /// </param>
        /// <param name="hash">Hash of the object's contents.</param>
        /// <param name="contents">Contents of the object (if virtual).</param>
        private void Add(BuildObject obj, Disposition disposition, string hash, VirtualContents contents)
        {
            // Every object in the repository should either have a hash value
            // or virtual contents, but not both.
            Util.Assert((string.IsNullOrEmpty(hash) && contents != null) ||
                (!string.IsNullOrEmpty(hash) && (contents == null)));

            // Check to see if the object is already in this repository.
            if (this.entries.ContainsKey(obj))
            {
                // We shouldn't be adding conflicting information for
                // the same object during the same build run.
                RepositoryEntry entry = this.entries[obj];
                Util.Assert(entry.Disposition.GetType() == disposition.GetType());
                Util.Assert(entry.Hash.Equals(hash, StringComparison.Ordinal));
                Util.Assert(entry.VirtualContents == contents);

                // Don't replace existing entry with equivalent.
                return;
            }

            this.entries[obj] = new RepositoryEntry(disposition, hash, contents);
        }

        /// <summary>
        /// Information we keep about build objects in our collection.
        /// </summary>
        private class RepositoryEntry
        {
            /// <summary>
            /// Disposition of the verb that created this object.
            /// </summary>
            private Disposition disposition;

            /// <summary>
            /// Hash of the object's contents (if non-virtual).
            /// </summary>
            private string hash;

            /// <summary>
            /// For objects not stored in the item cache or the filesystem,
            /// here's the computed value.
            /// </summary>
            private VirtualContents virtualContents;

            /// <summary>
            /// Initializes a new instance of the RepositoryEntry class.
            /// </summary>
            /// <param name="disposition">
            /// Disposition of the verb that created this object.
            /// </param>
            /// <param name="hash">Hash of the object's contents.</param>
            /// <param name="virtualContents">
            /// Computed value of the object (if virtual, null otherwise).
            /// </param>
            public RepositoryEntry(Disposition disposition, string hash, VirtualContents virtualContents)
            {
                this.hash = hash;
                this.disposition = disposition;
                this.virtualContents = virtualContents;
            }

            /// <summary>
            /// Gets the hash of the object's contents.
            /// </summary>
            public string Hash
            {
                get { return this.hash; }
            }

            /// <summary>
            /// Gets the disposition of the verb that created this object.
            /// </summary>
            public Disposition Disposition
            {
                get { return this.disposition; }
            }

            /// <summary>
            /// Gets the computed value of the object (if a virtual object,
            /// returns null otherwise).
            /// </summary>
            public VirtualContents VirtualContents
            {
                get { return this.virtualContents; }
            }
        }
    }
}
