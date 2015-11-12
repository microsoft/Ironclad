//--
// <copyright file="Scheduler.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Diagnostics;
    using System.IO;
    using System.Linq;
    using System.Security.Cryptography;
    using System.Text;
    using System.Threading.Tasks;

    /// <summary>
    /// Mechanism for determining which verbs need to be run and in what order.
    /// </summary>
    internal class Scheduler
    {
        /// <summary>
        /// Whether to produce conditional debug output in the scheduler and
        /// some of its components.
        /// </summary>
        internal const bool Debug = false;

        /// <summary>
        /// Where to write scheduler progress information (for debugging).
        /// </summary>
        private const string DbgProgressFileName = "nubuild.progress";

        /// <summary>
        /// REVIEW: Not used.  Remove?
        /// </summary>
        private const string DispositionFileExtension = ".disp";

        /// <summary>
        /// The second-order verb sorter we use.
        /// </summary>
        private VerbToposorter verbToposorter;

        /// <summary>
        /// Collection of initial output targets.
        /// </summary>
        private HashSet<BuildObject> targets;

        /// <summary>
        /// Waiting verb tracker?
        /// </summary>
        private WaitIndex waitIndex;

        /// <summary>
        /// Tracker of build objects.
        /// </summary>
        private Repository repository;

        /// <summary>
        /// The component of the scheduler that runs verbs for us.
        /// </summary>
        private VerbRunner verbRunner;

        /// <summary>
        /// Count of verbs submitted to the verbRunner for running during
        /// this round?
        /// </summary>
        private int submittedCount;

        /// <summary>
        /// Map of build objects to the verb that creates them.
        /// </summary>
        private Dictionary<BuildObject, IVerb> outputToVerbMap;

        /// <summary>
        /// Verbs in the outputToVerbMap.
        /// REVIEW: These verbs should be equivalent to those in
        /// outputToVerbMap.Values.  Worth keeping this separate HashSet
        /// for performance reasons?
        /// </summary>
        private HashSet<IVerb> knownVerbs;

        /// <summary>
        /// Cache of verb dependencies.
        /// </summary>
        private DependencyCache depCache;

        /// <summary>
        /// Verbs that have been submitted for execution or failed,
        /// and need not be further considered.
        /// </summary>
        private HashSet<IVerb> resolvedVerbs;

        /// <summary>
        /// Verbs that have been completed, and hence can't contribute
        /// to resolving any pending dependencies.
        /// (If it's resolved and not completed, it must be submitted
        /// for asynchronous execution.)
        /// </summary>
        private HashSet<IVerb> completedVerbs;

        /// <summary>
        /// Our general strategy is to record the outcome of every verb in
        /// a persistent result cache, and then to evaluate each downstream
        /// BuildObject by querying that cache. But when one verb fails,
        /// it may make the downstream verb unable to even compute its input
        /// set, and hence its concreteIdentifier (the key to a persistent
        /// cache). If we don't record the outcome somehow, we'll loop
        /// forever trying to learn the outcome of the downstream failure.
        /// So we record it here in-process, keyed by abstractIdentifier
        /// (which is assumed to be stable over a single run of NuBuild).
        /// Invariant: all values in this dictionary are Faileds. (We store
        /// them because they might (someday) propagate information about
        /// what failed for an error message.)
        /// </summary>
        private Dictionary<IVerb, Disposition> unrecordableFailures;

        /// <summary>
        /// Whether to reject cached failures, apparently.
        /// Value comes from a command-line argument.
        /// </summary>
        private bool rejectCachedFailures;

        /// <summary>
        /// Verbs that are (still) required to be run to build our target(s).
        /// Verbs are removed from this collection as they are completed.
        /// </summary>
        private HashSet<IVerb> requiredVerbs;

        /// <summary>
        /// Verbs to look at on next pass through parallelSchedule's main loop?
        /// Serves as a method for passing a collection of verbs between
        /// parallelSchedule and disposeCurrentVerbs.
        /// </summary>
        private HashSet<IVerb> nextVerbs;

        ////private DbgVerbCounter dbgVerbCounter = new DbgVerbCounter();

        /// <summary>
        /// Initializes a new instance of the Scheduler class.
        /// </summary>
        /// <param name="jobParallelism">
        /// Degree of parallel execution to allow.
        /// </param>
        /// <param name="rejectCachedFailures">
        /// Whether to reject cached failures.
        /// </param>
        public Scheduler(int jobParallelism)
        {
            this.targets = new HashSet<BuildObject>();
            this.waitIndex = new WaitIndex();
            this.repository = BuildEngine.theEngine.Repository;
            this.unrecordableFailures = new Dictionary<IVerb, Disposition>();
            this.verbToposorter = new VerbToposorter();
            this.verbRunner = new VerbRunner(this.verbToposorter, jobParallelism);
            this.resolvedVerbs = new HashSet<IVerb>();
            this.completedVerbs = new HashSet<IVerb>();
            this.outputToVerbMap = new Dictionary<BuildObject, IVerb>();
            this.knownVerbs = new HashSet<IVerb>();
            this.depCache = new DependencyCache();
            this.rejectCachedFailures = true;    // this is now permanent. The code path for caching Failure results has rotted.
        }

        /// <summary>
        /// Adds one or more build objects to our collection of targets.
        /// </summary>
        /// <review>
        /// REVIEW: Make this private (or inline into addVerbTargets)?
        /// </review>
        /// <param name="newTargets">Build objects to add.</param>
        public void addTargets(IEnumerable<BuildObject> newTargets)
        {
            this.targets.UnionWith(newTargets);
        }

        /// <summary>
        /// Schedules the verbs for execution.
        /// This is the top-level method driving the build.
        /// </summary>
        public void parallelSchedule()
        {
            // Convert our collection of initial targets into a
            // collection of verbs we need to run to create them.
            this.requiredVerbs = new HashSet<IVerb>();
            foreach (BuildObject target in this.targets)
            {
                this.requiredVerbs.Add(this.getParent(target));
            }

            // The set of verbs we're evaluating now.
            HashSet<IVerb> currentVerbs = new HashSet<IVerb>(this.requiredVerbs);

            // A set into which we accumulate verbs to evaluate on the next pass.
            this.nextVerbs = new HashSet<IVerb>();

            // Loop until we've run all the verbs we need to run.
            while (this.requiredVerbs.Count() > 0)
            {
                this.disposeCurrentVerbs(currentVerbs);
                currentVerbs = null;    // Just to be obvious.

                // Okay, now we wait around for some deps to finish, freeing up new targets.
                while (this.nextVerbs.Count() == 0 && this.requiredVerbs.Count() > 0)
                {
                    this.Say(string.Format("scheduler waits, having submitted {0} verbs", this.submittedCount));
                    ////Util.Assert(submittedCount > 0);  // False because we might be waiting for other stuff to complete.

                    List<VerbRunner.TaskCompletion> taskCompletions;
                    taskCompletions = this.verbRunner.scheduleAndWait(this);
                    this.Say("received " + taskCompletions.Count() + " taskCompletions");

                    Util.Assert(this.requiredVerbs.Count() == 0 || taskCompletions.Count() > 0);
                    this.processTaskCompletions(taskCompletions);

                    currentVerbs = this.nextVerbs;
                    this.nextVerbs = new HashSet<IVerb>();
                    if (currentVerbs.Count() > 0 || this.requiredVerbs.Count() == 0)
                    {
                        // Hey, something changed that we could reschedule on,
                        // or we're actually all done.
                        break;
                    }

                    // Hmm, we've got no opportunity to schedule new stuff,
                    // so the VerbRunner better not return empty-handed the
                    // next time through.
                    // We've got an assert taskCompletions.Count()>0 to check
                    // for that.
                    this.Say("Scheduler waiting for more results.");
                }
            }
        }

        /// <summary>
        /// Display various debugging information.
        /// </summary>
        public void dbgDisplayCounts()
        {
            ////dbgVerbCounter.dbgDisplayCounts();
            this.depCache.dbgPrintStats();
        }

        /// <summary>
        /// Display various debugging information.
        /// </summary>
        internal void dbgDumpWaitIndex()
        {
            this.waitIndex.dbgDisplayIndex(this);
        }

        /// <summary>
        /// Determine the status of a verb (for debugging purposes).
        /// </summary>
        /// <param name="verb">Verb being examined.</param>
        /// <returns>A string containing the verb's current status.</returns>
        internal string dbgGetVerbStatus(IVerb verb)
        {
            if (this.completedVerbs.Contains(verb))
            {
                return "completed";
            }

            if (this.resolvedVerbs.Contains(verb))
            {
                return "submitted";
            }

            return "pending";
        }

        /// <summary>
        /// Adds a verb to the mapping of build objects to the verb which
        /// creates them.
        /// </summary>
        /// <remarks>
        /// TODO: Make this private.
        /// </remarks>
        /// <param name="verb">The verb to add.</param>
        internal void addVerb(IVerb verb)
        {
            if (!this.knownVerbs.Add(verb))
            {
                // We've already added this verb.
                return;
            }

            // Add all verb outputs to the output-to-verb map.
            foreach (BuildObject obj in verb.getOutputs())
            {
                if (this.outputToVerbMap.ContainsKey(obj))
                {
                    Util.Assert(this.outputToVerbMap[obj].Equals(verb));
                }
                else
                {
                    this.outputToVerbMap[obj] = verb;
                }
            }

            // Recursively add all the verbs this verb is dependent upon,
            // so that we have a complete index of outputs back to the
            // verbs that generate them.
            foreach (IVerb dependentVerb in verb.getVerbs())
            {
                this.addVerb(dependentVerb);
            }
        }

        /// <summary>
        /// Adds a collection of verbs (or rather their outputs) as
        /// targets for this build.
        /// </summary>
        /// <param name="verbs">A list of verbs to run.</param>
        internal void addTargetVerbs(List<IVerb> verbs)
        {
            foreach (IVerb verb in verbs)
            {
                this.addVerb(verb);
                this.addTargets(verb.getOutputs());
            }
        }

        /// <summary>
        /// Gets a list of target objects for this build.
        /// </summary>
        /// <returns>A list of target objects for this build.</returns>
        internal IEnumerable<BuildObject> getTargets()
        {
            return this.targets;
        }

        /// <summary>
        /// Gets the verb that created the given object.
        /// </summary>
        /// <remarks>
        /// Would like to rename this to "GetCreator" or "GetCreatorVerb"
        /// as it seems strange to call something a parent when it is a
        /// completely different object type, but the terminology seems
        /// to be widely used in the system.
        /// </remarks>
        /// <param name="obj">The object in question.</param>
        /// <returns>The verb that creates the given object.</returns>
        internal IVerb getParent(BuildObject obj)
        {
            IVerb result;
            this.outputToVerbMap.TryGetValue(obj, out result);
            return result;
        }

        /// <summary>
        /// Gets the disposition of the verb that created the given object.
        /// </summary>
        /// <param name="obj">The object in question.</param>
        /// <returns>The disposition of the verb that created the given object.</returns>
        internal Disposition getObjectDisposition(BuildObject obj)
        {
            return this.repository.GetDisposition(obj);
        }

        /// <summary>
        /// Updates the "progress" output file with current status information.
        /// </summary>
        /// <param name="runnableVerbsCount">
        /// Count of verbs currently able to be run.
        /// </param>
        /// <param name="runningVerbsCount">
        /// Count of verbs currently running.
        /// </param>
        internal void dbgUpdateProgress(int runnableVerbsCount, int runningVerbsCount)
        {
            StringBuilder sb = new StringBuilder();
            sb.AppendLine("completedVerbs: " + this.completedVerbs.Count());
            sb.AppendLine("resolvedVerbs:  " + this.resolvedVerbs.Count());
            sb.AppendLine("runnableVerbs:  " + runnableVerbsCount);
            sb.AppendLine("runningVerbs:   " + runningVerbsCount);
            sb.AppendLine("waitingVerbs:   " + this.waitIndex.Count());
            File.WriteAllText(DbgProgressFileName, sb.ToString());
        }

        /// <summary>
        /// Computes a concrete identifier for a verb operation and its
        /// specific inputs.
        /// </summary>
        /// <param name="verb">The verb to compute the hash for.</param>
        /// <param name="assertHashAvailable">
        /// Whether to assert if we can't compute the hash.
        /// </param>
        /// <returns>
        /// A concrete identifier for a verb operation and its specific inputs.
        /// </returns>
        private string computeInputHash(IVerb verb, bool assertHashAvailable)
        {
            StringBuilder sb = new StringBuilder();
            sb.Append(verb.getAbstractIdentifier().getConcreteId());
            DependencyDisposition ddisp;
            foreach (BuildObject obj in this.depCache.getDependencies(verb, out ddisp))
            {
                sb.Append(",");
                string hash = this.repository.GetHash(obj);
                Util.Assert(!assertHashAvailable || (hash != null));
                sb.Append(hash);
            }

            if (ddisp == DependencyDisposition.Failed)
            {
                // This happens when we're trying to markFailed,
                // but the upstream has failed and we can't compute
                // our dependencies. In that case, markFailed
                // settles for noting the failure in-process,
                // but not caching the result. (Okay, since this
                // failure propagation is cheap to rediscover.)
                Util.Assert(!assertHashAvailable);
                return null;
            }

            Util.Assert(ddisp == DependencyDisposition.Complete);
            string rc = Util.hashString(sb.ToString());
            return rc;
        }

        /// <summary>
        /// Finds some verbs that could possibly complete in the future and help
        /// resolve one of these dependencies.
        /// </summary>
        /// <param name="staleDeps">A list of unresolved dependencies.</param>
        /// <returns>
        /// A list of verbs that could possibly create one or more of the
        /// missing dependencies.
        /// </returns>
        private List<IVerb> robustDiscoverReadyDeps(IEnumerable<BuildObject> staleDeps)
        {
            List<IVerb> newParents = new List<IVerb>();
            foreach (BuildObject dep in staleDeps)
            {
                IVerb parent = this.getParent(dep);
                if (parent != null)
                {
                    if (this.completedVerbs.Contains(parent))
                    {
                        // Wait, if the parent is completed, why is the child a stale dependency?
                        Util.Assert(false);
                    }

                    newParents.Add(parent);
                }
            }

            return newParents;
        }

        /// <summary>
        /// Push each potential target somewhere else: replace it with its
        /// dependencies, or mark its outputs failed, or mark it runnable and
        /// give it to the verb runner.
        /// </summary>
        /// <param name="currentVerbs">Set of verbs to process.</param>
        private void disposeCurrentVerbs(HashSet<IVerb> currentVerbs)
        {
            this.submittedCount = 0;
            this.Say("disposeCurrentVerbs");
            while (currentVerbs.Count() > 0)
            {
                foreach (IVerb verb in currentVerbs)
                {
                    this.Say("disposeCurrentVerbs considering " + verb);
                    ////dbgVerbCounter.consider(verb, DbgVerbCounter.DbgVerbCondition.DVWake);

                    if (this.resolvedVerbs.Contains(verb))
                    {
                        // Enthusiastic wakeup?
                        continue;
                    }

                    if (this.waitIndex.isWaiting(verb))
                    {
                        // He's already waiting for something else.
                        continue;
                    }

                    DependencyDisposition ddisp;
                    List<BuildObject> knownDeps = new List<BuildObject>(this.depCache.getDependencies(verb, out ddisp));

                    List<BuildObject> staleDeps = new List<BuildObject>();
                    List<BuildObject> failedDeps = new List<BuildObject>();
                    foreach (BuildObject dep in knownDeps)
                    {
                        Disposition disp = this.repository.GetDisposition(dep);
                        if (disp is Stale)
                        {
                            staleDeps.Add(dep);
                        }
                        else if (disp is Failed)
                        {
                            failedDeps.Add(dep);
                        }
                    }

                    if (staleDeps.Count() > 0 || ddisp == DependencyDisposition.Incomplete)
                    {
                        // Some inputs aren't yet available, so we can prompt one of those verbs
                        // instead, and wake this one up when those are done.
                        Util.Assert(staleDeps.Count() > 0);

// REVIEW: Clean this up post SOSP.
#if false
                        List<IVerb> newParents = this.robustDiscoverReadyDeps(staleDeps);
                        if (newParents.Count() == 0)
                        {
                            this.reexamineVerb(verb);
                            newParents = this.robustDiscoverReadyDeps(staleDeps);
                            Util.Assert(newParents.Count() > 0);
                        }
#else
                        this.reexamineVerb(verb);
                        List<IVerb> newParents = this.robustDiscoverReadyDeps(staleDeps);
                        Util.Assert(newParents.Count() > 0);
#endif

                        this.nextVerbs.UnionWith(newParents);
                        this.Say(
                            string.Format(
                                "disposeCurrentVerbs waits {0}   dependent on {1}   liberating {2}",
                                verb,
                                string.Join(",", staleDeps),
                                string.Join(",", newParents)));
                        this.waitIndex.insert(verb, staleDeps);
                    }
                    else if (ddisp == DependencyDisposition.Failed || failedDeps.Count() > 0)
                    {
                        this.Say(string.Format("disposeCurrentVerbs marks {0} failed", verb));
                        this.markFailed(verb);
                        this.resolvedVerbs.Add(verb);
                        ////dbgVerbCounter.consider(verb, DbgVerbCounter.DbgVerbCondition.DVDepsNonstale);
                    }
                    else
                    {
                        // All inputs are available, so we can compute concrete identifier
                        // to retrieve from cache...
                        string inputHash = this.computeInputHash(verb, true);
                        Util.Assert(inputHash != null);

                        if (!this.fetchFromCache(verb, inputHash))
                        {
                            ////if (verb is BoogieAsmVerificationObligationListVerb) { System.Environment.Exit(0); }
                            this.Say(string.Format("disposeCurrentVerbs submits {0}", verb));

                            // Or if it's not in cache, we can execute.
                            // Verb's inputs are ready, and output is stale: mark verb runnable.
                            ////Say(string.Format("  {0} submitted", verb));
                            this.verbRunner.submitVerb(verb);
                            this.submittedCount += 1;
                        }

                        this.resolvedVerbs.Add(verb);
                        ////dbgVerbCounter.consider(verb, DbgVerbCounter.DbgVerbCondition.DVDepsNonstale);
                    }
                }

                // We've disposed all the current verbs. But maybe we found some more
                // we can pop loose right now.
                currentVerbs = this.nextVerbs;
                this.nextVerbs = new HashSet<IVerb>();
            }
        }

        /// <summary>
        /// Checks the cache for a previous execution of this verb operating on
        /// the same inputs; updates our state with the cached results if so.
        /// </summary>
        /// <param name="verb">The verb to check for prior execution.</param>
        /// <param name="inputHash">
        /// An identifier for this verb operating on a specific set of inputs.
        /// </param>
        /// <returns>
        /// True if usable previous execution was found, false otherwise.
        /// </returns>
        private bool fetchFromCache(IVerb verb, string inputHash)
        {
            try
            {
                ResultSummaryRecord summary = this.repository.FetchResult(inputHash);
                if (summary.Disposition is Stale)
                {
                    return false;
                }

                // REVIEW: Since we aren't asking FetchResult to return failures,
                // this check is no longer needed.  Or at least it won't be once
                // the "Results" cache is cleared of all existing failure records.
                if (this.rejectCachedFailures
                    && (summary.Disposition is Failed || summary.IsVerificationTimeout))
                {
                    Logger.WriteLine(string.Format(
                        "NOTE: rejecting failure from cache {0}", verb));
                    return false;
                }

                this.Say(string.Format("disposeCurrentVerbs pulls {0} from cache", verb));

                // Hey, this verb is already computed! Nothing to do.
                // Add the verb execution's results to the repository.
                this.repository.AddVerbResults(verb, summary);

                this.verbIsComplete(verb, summary.Disposition);

                return true;
            }
            catch (ObjectMissingFromCacheException ex)
            {
                Logger.WriteLine(string.Format(
                    "WARNING: expected object {0} missing from cache; discarding cached result {1}",
                    ex,
                    verb));
                return false;
            }
        }

        /// <summary>
        /// Reexamines a verb to see if it now knows more regarding what other
        /// verbs need to run first in order to create its dependencies.
        /// </summary>
        /// <param name="verb">The verb to reexamine.</param>
        private void reexamineVerb(IVerb verb)
        {
            foreach (IVerb parentVerb in verb.getVerbs())
            {
                this.addVerb(parentVerb);
            }
        }

        /// <summary>
        /// Processes task completion messages.
        /// </summary>
        /// <param name="taskCompletions">
        /// A list of task completion messages.
        /// </param>
        private void processTaskCompletions(List<VerbRunner.TaskCompletion> taskCompletions)
        {
            foreach (VerbRunner.TaskCompletion tc in taskCompletions)
            {
                // We may record a Failure if the verb didn't output
                // everything it promised to.
                Disposition recordedDisposition = this.recordResult(tc);

                this.Say(string.Format("  {0} completed with disposition {1}", tc.verb, tc.disposition));
            }

            // Waking process may have shaken some verbs loose for us to evaluate next time around.
        }

        /// <summary>
        /// Conditionally debug print a message.
        /// </summary>
        /// <param name="s">The message to print.</param>
        private void Say(string s)
        {
            if (Debug)
            {
#pragma warning disable 162
                Logger.WriteLine("[sched] " + s);
#pragma warning restore 162
            }
        }

        /// <summary>
        /// Logs output regarding a verb's execution disposition.
        /// </summary>
        /// <param name="verb">The verb in question.</param>
        /// <param name="disposition">Disposition of the verb execution.</param>
        private void emitRealtimeReport(IVerb verb, Disposition disposition)
        {
            Presentation pr = verb.getRealtimePresentation(disposition);
            ASCIIPresentater ascii = new ASCIIPresentater();
            pr.format(ascii);
            Logger.Write(ascii.ToString());
        }

        /// <summary>
        /// Mark a verb as completed, and adjust our schedule accordingly.
        /// </summary>
        /// <param name="verb">The verb that completed.</param>
        /// <param name="disp">The disposition of the verb's execution.</param>
        private void verbIsComplete(IVerb verb, Disposition disp)
        {
            ////Say(string.Format("  {0} is complete: {1}", verb, dbgDisposition));
            ////if (disp is Failed)
            ////{
            ////    // Failures can be hard to debug, since they don't leave any
            ////    // output in nuobj/. So report these even if they aren't
            ////    // built this run.
            ////    emitRealtimeReport(verb, disp);
            ////}

            // Invariant: all of this verb's objs are non-Stale.
            foreach (BuildObject obj in verb.getOutputs())
            {
                ////Say(string.Format("  waking {0}", obj));
                IEnumerable<IVerb> wokenSet = this.waitIndex.awaken(obj);
                ////foreach (IVerb wokenVerb in wokenSet)
                ////{
                ////    //Say(string.Format("  {0} woken", wokenVerb));
                ////}
                this.nextVerbs.UnionWith(wokenSet);
            }

            this.emitRealtimeReport(verb, disp);

            this.requiredVerbs.Remove(verb);
            this.completedVerbs.Add(verb);
        }

        /// <summary>
        /// Record how each output of a task appeared.
        /// </summary>
        /// <param name="completion">The task completion notification.</param>
        /// <returns>Overall result of the verb execution.</returns>
        private Disposition recordResult(VerbRunner.TaskCompletion completion)
        {
            WorkingDirectory workingDirectory = completion.workingDirectory;
            IVerb verb = completion.verb;
            Disposition executionDisposition = completion.disposition;

            List<BuildObjectValuePointer> outputs = new List<BuildObjectValuePointer>();
            List<string> missingOutputs = new List<string>();
            IEnumerable<BuildObject> expectedOutputs = verb.getOutputs();

            if (executionDisposition is Failed)
            {
                expectedOutputs = expectedOutputs.Concat(verb.getFailureOutputs());
            }

            bool hasVirtualOutputs = false;
            foreach (BuildObject outobj in expectedOutputs)
            {
                if (!(outobj is VirtualBuildObject))
                {
                    // For expected file outputs, check for existence in working directory.
                    // REVIEW: Add method to WorkingDirectory which does this?
                    if (File.Exists(workingDirectory.PathTo(outobj)))
                    {
                        // Try to catch accidental case mismatches that would burn us when we
                        // try to fetch the file back in.
                        ////string fsname = PathNormalizer.dbg_normalizePath_nocache(outobj.deprecatedGetFilesystemPath(), false);
                        ////Util.Assert(Path.GetFileName(fsname).Equals(outobj.getFileName()));
                        // REVIEW: Do we need to worry about case mismatches anymore?  See comments above.
                        outputs.Add(this.repository.Store(workingDirectory, outobj, executionDisposition));

                        // Store a copy of this verb output as a file in the real nuobj directory.
                        Util.Assert(outobj.getRelativePath().StartsWith(BuildEngine.theEngine.getObjRoot(), StringComparison.Ordinal));
                        string nuobjPath = IronRootDirectory.PathTo(outobj);
                        Directory.CreateDirectory(Path.GetDirectoryName(nuobjPath));
                        File.Copy(workingDirectory.PathTo(outobj), nuobjPath, true);
                    }
                    else
                    {
                        missingOutputs.Add(string.Format("Missing expected output {0}", outobj.getRelativePath()));
                    }
                }
                else
                {
                    hasVirtualOutputs = true;
                    if (this.repository.GetDisposition(outobj) is Fresh)
                    {
                        // Nothing to cache; virtual objects only survive in the Repository, the in-process store.
                    }
                    else
                    {
                        missingOutputs.Add(string.Format("Missing expected virtual {0}", outobj.getRelativePath()));
                    }
                }
            }

            if (!(executionDisposition is Failed) && missingOutputs.Count() > 0)
            {
                executionDisposition = new Failed(missingOutputs);
            }

            ResultSummaryRecord summary = new ResultSummaryRecord(verb, executionDisposition, outputs);
            string inputHash = this.computeInputHash(verb, true);
            Util.Assert(inputHash != null);
            if (!hasVirtualOutputs)
            {
                this.repository.StoreResult(inputHash, summary);
            }
            else
            {
                this.Say("Not caching verb persistently: " + verb);
            }

            this.verbIsComplete(verb, executionDisposition);
            return executionDisposition;
        }

        /// <summary>
        /// Mark a verb as having failed.
        /// </summary>
        /// <param name="verb">The verb that failed.</param>
        private void markFailed(IVerb verb)
        {
            // At least one of verb's inputs has a permanent failure, so we didn't
            // even try to execute it.
            Disposition disposition = new Failed("upstream failure");
            ResultSummaryRecord summary = new ResultSummaryRecord(verb, disposition, new BuildObjectValuePointer[] { });

            // NB never store upstream failures to the persistent cache, because
            // they depend on our knowledge this run that the upstream verb failed.
            // If, in another run, the verb or its inputs are modified, produce the
            // same outputs, but returns success, we'll be stuck pulling this
            // upstream failure out of cache but calling this verb a failure.
            ////string inputHash = computeInputHash(verb, false);
            ////if (inputHash != null)
            ////{
            ////    Util.Assert(false);
            ////    // "Upstream failures" will never have a computable inputHash, because their inputs
            ////    // can't be considered known. Even if the upstream verb wrote something to disk,
            ////    // what if the upstream verb changes to no longer fail but still emit the same thing?
            ////    // We wouldn't want to conclude that, because the inputs hadn't changed, this
            ////    // verb still had an upstream failure.
            ////    repository.StoreResult(inputHash, summary);
            ////}
            ////else
            ////{
            this.unrecordableFailures[verb] = disposition;
            ////}

            // Mark all the verb's outputs as Failed in the repository.
            foreach (BuildObject obj in verb.getOutputs())
            {
                if (obj is VirtualBuildObject)
                {
                    this.repository.StoreVirtual(obj, disposition, null);
                }
                else
                {
                    this.repository.AddObject(obj, disposition, null);
                }
            }

            this.verbIsComplete(verb, disposition);
        }
    }
}
