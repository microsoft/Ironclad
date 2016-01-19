//--
// <copyright file="Program.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace ItemCacheTool
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;
    using System.Text;
    using System.Threading.Tasks;
    using Microsoft.WindowsAzure.Storage;
    using Microsoft.WindowsAzure.Storage.Blob;
    using NuBuild;

    /// <summary>
    /// Representation of the ItemCacheTool program.
    /// </summary>
    public static class Program
    {
        /// <summary>
        /// Program entry point.
        /// </summary>
        /// <param name="args">Command line arguments.</param>
        private static void Main(string[] args)
        {
            CacheState caches = new CacheState();
            string query;
            IItemCache[] queriedCaches;
            ItemCacheContainer[] queriedContainers;
            string queriedItems;
            DateTimeOffset queriedDate;

            // -
            // Default values.
            // This corresponds to "status * *".
            // -
            query = "status";
            queriedCaches = caches.GetAllCaches;
            queriedContainers = caches.GetAllContainers;
            queriedItems = string.Empty;
            queriedDate = DateTimeOffset.MinValue;

            // -
            // Parse arguments.
            // -
            if (args.Length != 0)
            {
                if (args.Length != 3)
                {
                    if (args.Length == 4)
                    {
                        if (!DateTimeOffset.TryParse(args[3], out queriedDate))
                        {
                            queriedItems = args[3];
                        }
                    }
                    else
                    {
                        Usage(caches);
                        return;
                    }
                }

                query = args[0];
                queriedCaches = caches.ParseCacheName(args[1]);
                queriedContainers = caches.ParseContainerName(args[2]);

                if ((queriedCaches == null) || (queriedContainers == null))
                {
                    Usage(caches);
                    return;
                }
            }

            // -
            // Process request.
            // -
            switch (query)
            {
                case "list":
                case "List":
                    {
                        CacheStatus(queriedCaches, queriedContainers, true);
                        break;
                    }

                case "compare":
                case "Compare":
                    {
                        if (queriedCaches.Length < 2)
                        {
                            Console.WriteLine("Error: can't compare fewer than two caches!");
                            Usage(caches);
                            return;
                        }

                        CompareCacheContainers(queriedCaches, queriedContainers);
                        break;
                    }

                case "status":
                case "Status":
                    {
                        CacheStatus(queriedCaches, queriedContainers, false);
                        break;
                    }

                case "delete":
                case "Delete":
                    {
                        if (args.Length < 4)
                        {
                            Console.WriteLine("Error: missing argument.  Need date earlier than or specific item(s) to delete.");
                            Usage(caches);
                            return;
                        }

                        if (queriedDate == DateTimeOffset.MinValue)
                        {
                            DeleteItems(queriedCaches, queriedContainers, queriedItems);
                        }
                        else
                        {
                            DeleteItems(queriedCaches, queriedContainers, queriedDate);
                        }

                        break;
                    }

                case "check":
                case "Check":
                    {
                        CheckResults(queriedCaches, false);
                        break;
                    }

                case "cleanup":
                case "Cleanup":
                    {
                        CheckResults(queriedCaches, true);
                        break;
                    }

                case "dump":
                case "Dump":
                    {
                        DumpItems(queriedCaches, queriedContainers, queriedItems);
                        break;
                    }
            }
        }

        /// <summary>
        /// Prints a user-friendly message explaining how to use the program.
        /// </summary>
        /// <param name="caches">The caches the program is using.</param>
        private static void Usage(CacheState caches)
        {
            string containers = string.Empty;
            foreach (ItemCacheContainer container in caches.GetAllContainers)
            {
                containers += container.ToString() + " | ";
            }

            containers += " *";

            Console.WriteLine("Usage: ItemCacheTool <command> <cache> <container> [<date> | <item hash>]");
            Console.WriteLine("\t <command> = Check | Cleanup | Compare | Delete | List | Status");
            Console.WriteLine("\t <cache> = Cloud | Local | *");
            Console.WriteLine("\t <container> = {0}", containers);
            Console.WriteLine("\t [<date> | <item hash>] = specifies item(s) to delete.");
        }

        /// <summary>
        /// Provides a status report of the number of items in the specified
        /// cache containers, and optionally a list of those items.
        /// </summary>
        /// <param name="queriedCaches">Caches to examine.</param>
        /// <param name="queriedContainers">Containers in those caches to examine.</param>
        /// <param name="listContents">Whether to list the cache contents.</param>
        private static void CacheStatus(
            IItemCache[] queriedCaches,
            ItemCacheContainer[] queriedContainers,
            bool listContents)
        {
            string lineTerminator = ".";
            if (listContents)
            {
                lineTerminator = ":";
            }

            foreach (IItemCache cache in queriedCaches)
            {
                foreach (ItemCacheContainer container in queriedContainers)
                {
                    HashSet<string> items = cache.GetItemsInContainer(container);
                    Console.WriteLine("{0} cache {1} container holds {2} items{3}", cache.Name, container.ToString(), items.Count, lineTerminator);
                    if (listContents)
                    {
                        foreach (string item in items)
                        {
                            ////Console.WriteLine("Item: {0}, Date:{1}", item, cache.GetItemLastModifiedTime(container, item));
                            Console.WriteLine(item);
                        }

                        Console.WriteLine();
                    }
                }

                Console.WriteLine();
            }
        }

        /// <summary>
        /// Compares the contents of two caches.
        /// </summary>
        /// <param name="queriedCaches">Caches to compare.</param>
        /// <param name="queriedContainers">Containers in those caches to compare.</param>
        private static void CompareCacheContainers(
            IItemCache[] queriedCaches,
            ItemCacheContainer[] queriedContainers)
        {
            foreach (ItemCacheContainer container in queriedContainers)
            {
                IItemCache cacheA = queriedCaches[0];
                IItemCache cacheB = queriedCaches[1];

                HashSet<string> cacheAItems = cacheA.GetItemsInContainer(container);
                HashSet<string> cacheBItems = cacheB.GetItemsInContainer(container);

                Console.WriteLine("There are {0} items in the {1} cache {2} container.", cacheAItems.Count, cacheA.Name, container.ToString());
                Console.WriteLine("There are {0} items in the {1} cache {2} container.", cacheBItems.Count, cacheB.Name, container.ToString());

                HashSet<string> syncedItems = new HashSet<string>(cacheAItems);
                syncedItems.IntersectWith(cacheBItems);
                Console.WriteLine("There are {0} items present in both cache's {1} container.", syncedItems.Count, container);
                Console.WriteLine();
            }
        }

        /// <summary>
        /// Deletes the given items from the given caches and containers.
        /// </summary>
        /// <param name="queriedCaches">Caches to look in.</param>
        /// <param name="queriedContainers">Containers to look in.</param>
        /// <param name="queriedItems">Items to delete.</param>
        private static void DeleteItems(
            IItemCache[] queriedCaches,
            ItemCacheContainer[] queriedContainers,
            string queriedItems)
        {
            if (queriedItems == "*")
            {
                if (!DeleteItemsConfirmation())
                {
                    return;
                }
            }

            foreach (IItemCache cache in queriedCaches)
            {
                foreach (ItemCacheContainer container in queriedContainers)
                {
                    if (queriedItems == "*")
                    {
                        HashSet<string> items = cache.GetItemsInContainer(container);
                        foreach (string item in items)
                        {
                            cache.DeleteItem(container, item);
                        }
                    }
                    else
                    {
                        cache.DeleteItem(container, queriedItems);
                    }
                }
            }
        }

        /// <summary>
        /// Deletes the items from the given caches and containers
        /// that have an earlier last modified time than the given one.
        /// </summary>
        /// <param name="queriedCaches">Caches to look in.</param>
        /// <param name="queriedContainers">Containers to look in.</param>
        /// <param name="queriedDate">Date to compare against.</param>
        private static void DeleteItems(
            IItemCache[] queriedCaches,
            ItemCacheContainer[] queriedContainers,
            DateTimeOffset queriedDate)
        {
            if (!DeleteItemsConfirmation())
            {
                return;
            }

            foreach (IItemCache cache in queriedCaches)
            {
                foreach (ItemCacheContainer container in queriedContainers)
                {
                    HashSet<string> items = cache.GetItemsInContainer(container);
                    foreach (string item in items)
                    {
                        DateTimeOffset? lastModified = cache.GetItemLastModifiedTime(container, item);
                        if (lastModified.HasValue && (lastModified.Value.CompareTo(queriedDate) < 0))
                        {
                            cache.DeleteItem(container, item);
                        }
                    }
                }
            }
        }

        /// <summary>
        /// Asks the user for confirmation that deleting a large number of cache items is okay.
        /// </summary>
        /// <returns>True if deletion is okay, false otherwise.</returns>
        private static bool DeleteItemsConfirmation()
        {
            string input;
            string annoyingConfirmationString = "Yes I mean to do this!";

            Console.WriteLine("You are about to delete a potentially large number of cache items!");
            Console.WriteLine("To proceed, please enter '{0}':", annoyingConfirmationString);
            input = Console.ReadLine();
            if (input != annoyingConfirmationString)
            {
                Console.WriteLine("Your input didn't match.  Exiting without deleting anything.");
                return false;
            }

            return true;
        }

        /// <summary>
        /// Dumps the given items from the given caches and containers.
        /// </summary>
        /// <param name="queriedCaches">Caches to look in.</param>
        /// <param name="queriedContainers">Containers to look in.</param>
        /// <param name="queriedItems">Items to dump.</param>
        private static void DumpItems(
            IItemCache[] queriedCaches,
            ItemCacheContainer[] queriedContainers,
            string queriedItems)
        {
            foreach (IItemCache cache in queriedCaches)
            {
                foreach (ItemCacheContainer container in queriedContainers)
                {
                    if (queriedItems == "*")
                    {
                        HashSet<string> items = cache.GetItemsInContainer(container);
                        foreach (string item in items)
                        {
                            DumpItem(cache, container, item);
                        }
                    }
                    else
                    {
                        DumpItem(cache, container, queriedItems);
                    }
                }
            }
        }

        /// <summary>
        /// Dumps the given item from the given cache and container.
        /// </summary>
        /// <param name="cache">Cache to look in.</param>
        /// <param name="container">Container to look in.</param>
        /// <param name="item">Item to dump.</param>
        private static void DumpItem(IItemCache cache, ItemCacheContainer container, string item)
        {
#if true
            byte[] content = cache.FetchItem(container, item);
            if (content != null)
            {
                BinaryWriter writer = new BinaryWriter(Console.OpenStandardOutput());
                writer.Write(content);
                writer.Close();
            }
#endif
#if false
            ResultSummaryRecord record = FetchRecord(cache, container, item);
            if (record != null)
            {
                Console.WriteLine();
                Console.WriteLine("IsVerificationTimeout = {0}", record.IsVerificationTimeout);
                Console.WriteLine("IsFailure = {0}", record.IsFailure);
            }
            else
            {
                Console.WriteLine();
                Console.WriteLine("FetchRecord failed for {0}", item);
            }
#endif
        }

        /// <summary>
        /// Checks the given cache(s) Results and FailedResults for goodness.
        /// </summary>
        /// <param name="queriedCaches">Caches to check.</param>
        /// <param name="cleanup">Whether to cleanup after bad cache entries.</param>
        private static void CheckResults(
            IItemCache[] queriedCaches,
            bool cleanup)
        {
            // We can do this for Local, Cloud, or both.
            foreach (IItemCache cache in queriedCaches)
            {
                // We have one Objects container for objects referenced by
                // results in both the Results and FailedResults containers.
                HashSet<string> objects = cache.GetItemsInContainer(ItemCacheContainer.Objects);

                // Likewise, we have only one Sources container.
                // REVIEW: Should a "source" ever show up as a verb result?
                HashSet<string> sources = cache.GetItemsInContainer(ItemCacheContainer.Sources);

                // We initialize the orphanedObjects set to all objects and
                // then remove objects from the set when we find them listed
                // in a result (stored in either Results or FailedResults).
                HashSet<string> orphanedObjects = cache.GetItemsInContainer(ItemCacheContainer.Objects);

                // We check both successful and failed results.
                foreach (ItemCacheContainer resultsContainer in new ItemCacheContainer[] { ItemCacheContainer.Results, ItemCacheContainer.FailedResults })
                {
                    HashSet<string> parseErrors = new HashSet<string>();

                    // Misfiled results (i.e. failures in Results container or
                    // non-failures in FailedResults container).
                    HashSet<string> misfiledResults = new HashSet<string>();

                    // Results that are missing one or more ouput objects.
                    HashSet<string> resultsMissingOutputs = new HashSet<string>();

                    HashSet<string> missingOutputHashes = new HashSet<string>();
                    HashSet<string> missingOutputPaths = new HashSet<string>();
                    int timeouts = 0;
                    int failures = 0;
                    int missing = 0;

                    HashSet<string> results = cache.GetItemsInContainer(resultsContainer);
                    foreach (string result in results)
                    {
                        ResultSummaryRecord record = FetchRecord(cache, resultsContainer, result);
                        if (record == null)
                        {
                            Console.WriteLine("Parse error in {0}.", result);
                            parseErrors.Add(result);
                        }
                        else
                        {
                            if (record.IsFailure)
                            {
                                if (resultsContainer == ItemCacheContainer.Results)
                                {
                                    // We shouldn't have any failures in Results!
                                    misfiledResults.Add(result);
                                }

                                if (record.IsVerificationTimeout)
                                {
                                    ////Console.WriteLine("Timeout in {0}.", result);
                                    timeouts++;
                                }
                                else
                                {
                                    ////Console.WriteLine("Failure in {0}.", result);
                                    failures++;
                                }
                            }
                            else if (resultsContainer == ItemCacheContainer.FailedResults)
                            {
                                // We should only have failures in FailedResults!
                                misfiledResults.Add(result);
                            }

                            // Verify each output is in the cache.
                            bool hasMissingOuputs = false;
                            foreach (BuildObjectValuePointer output in record.Outputs)
                            {
                                if (objects.Contains(output.ObjectHash))
                                {
                                    // Output present in object cache.
                                    // Remove it from orphaned objects list.
                                    orphanedObjects.Remove(output.ObjectHash);
                                }
                                else if (sources.Contains(output.ObjectHash))
                                {
                                    // Output present in sources cache.
                                    Console.WriteLine("Has 'source' file listed as an output: {0}!", result);
                                }
                                else
                                {
                                    // Output missing from both object and sources caches.
                                    hasMissingOuputs = true;
                                    missingOutputHashes.Add(output.ObjectHash);
                                    missingOutputPaths.Add(output.RelativePath);
                                    missing++;
                                    Console.WriteLine("Missing Output Listed in {0}, Object {1} ({2}).", result, output.ObjectHash, output.RelativePath);
                                }
                            }

                            if (hasMissingOuputs)
                            {
                                resultsMissingOutputs.Add(result);
                            }
                        }
                    }

                    Console.WriteLine();
                    Console.WriteLine("Checked {0} results in {1} cache {2} container:", results.Count, cache.Name, resultsContainer.ToString());
                    Console.WriteLine("Corrupted (parsing errors or otherwise unreadable): {0}", parseErrors.Count);
                    Console.WriteLine("Filed in wrong container: {0}", misfiledResults.Count);
                    Console.WriteLine("Timeouts: {0}, Other failures: {1}, Total failures: {2}", timeouts, failures, timeouts + failures);
                    Console.WriteLine("Missing at least one output object: {0}", resultsMissingOutputs.Count);
                    Console.WriteLine("Total missing output objects: {0}, Unique contents: {1}, Unique paths: {2}", missing, missingOutputHashes.Count, missingOutputPaths.Count);
                    Console.WriteLine();

                    if (cleanup)
                    {
                        if (misfiledResults.Count != 0)
                        {
                            Console.Write("Deleting misfiled results...");
                            foreach (string misfiledResult in misfiledResults)
                            {
                                cache.DeleteItem(resultsContainer, misfiledResult);
                            }

                            Console.WriteLine("Done.");
                        }

                        if (resultsMissingOutputs.Count != 0)
                        {
                            Console.Write("Deleting results with missing outputs...");
                            foreach (string resultMissingOutputs in resultsMissingOutputs)
                            {
                                cache.DeleteItem(resultsContainer, resultMissingOutputs);
                            }

                            Console.WriteLine("Done.");
                        }

                        Console.WriteLine();
                    }
                }

                // REVIEW: in at least one instance, we cache an intermediate
                // object that isn't referenced by a result.  That instance is
                // DafnyIncludes.ExpandDafny(), which is called from
                // DafnyCompileOneVerb.  This is to allow cloud execution of the
                // process invoke part of the verb's execution (with the dafny
                // expansion happening in the verb's getWorker() method).  Since
                // ExpandDafny() is a work-around for a Dafny issue, it's not
                // clear whether we should further accommodate this in the build
                // system (i.e. by making ExpandDafny its own verb) or not.
                // At any rate, having orphaned objects is not necessarily bad.
                Console.WriteLine("Orphaned objects not listed in any result: {0}", orphanedObjects.Count);

                if (cleanup)
                {
                    Console.WriteLine();

                    if (orphanedObjects.Count != 0)
                    {
                        Console.Write("Deleting orphaned objects...");
                        foreach (string orphanedObject in orphanedObjects)
                        {
                            cache.DeleteItem(ItemCacheContainer.Objects, orphanedObject);
                        }

                        Console.WriteLine("Done.");
                    }
                }
            }
        }

        /// <summary>
        /// Retrieves the requested result from the given cache.
        /// </summary>
        /// <param name="cache">Cache to query.</param>
        /// <param name="container">Container to query.</param>
        /// <param name="itemHash">Result to get.</param>
        /// <returns>The requested ResultSummaryRecord, or null if not found.</returns>
        private static ResultSummaryRecord FetchRecord(IItemCache cache, ItemCacheContainer container, string itemHash)
        {
            byte[] result = cache.FetchItem(container, itemHash);

            if (result != null)
            {
                MemoryStream resultStream = new MemoryStream(result);
                try
                {
                    using (StreamReader inReader = new StreamReader(resultStream))
                    {
                        string xmlSummary = inReader.ReadToEnd();
                        ResultSummaryRecord record = ResultSummaryRecord.FromXml(xmlSummary);
                        if (record == null)
                        {
                            Console.WriteLine("FromXml failed for {0}", itemHash);
                        }

                        return record;
                    }
                }
                catch (System.Xml.XmlException ex)
                {
                    Console.WriteLine("Malformed xml in {0}: {1}", itemHash, ex.ToString());
                    return null;
                }
                finally
                {
                    resultStream.Dispose();
                }
            }
            else
            {
                Console.WriteLine("FetchItem failed for {0}", itemHash);
                return null;
            }
        }
    }
}
