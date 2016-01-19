//--
// <copyright file="CloudExecutionEngine.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace CloudExecutionWorker
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using NuBuild;

    /// <summary>
    /// Representation of the Cloud Execution Engine.
    /// </summary>
    public class CloudExecutionEngine
    {
        /// <summary>
        /// Root directory path.
        /// </summary>
        private string virtualIronRoot;

        /// <summary>
        /// Cloud implementation of the item cache.
        /// Used to explicitly store things in the cloud.
        /// </summary>
        private ItemCacheCloud cloudCache;

        /// <summary>
        /// Multiplexed cloud/local implementation of the item cache.
        /// </summary>
        private IItemCache multiplexedItemCache;

        /// <summary>
        /// Main queue of client execution requests.
        /// </summary>
        private CloudExecutionQueue mainQueue;

        /// <summary>
        /// Whether to continue servicing the queue requests.
        /// </summary>
        private bool keepSwimming;

        /// <summary>
        /// Initializes a new instance of the CloudExecutionEngine class.
        /// </summary>
        public CloudExecutionEngine()
        {
            // Establish various infrastructure.
            // TODO: Clean this up.
            this.virtualIronRoot = Directory.GetCurrentDirectory();
            string localCacheDirectory = Path.Combine(this.virtualIronRoot, "nucache");
            this.cloudCache = new ItemCacheCloud();
            this.multiplexedItemCache = new ItemCacheMultiplexer(
                    new ItemCacheLocal(localCacheDirectory),
                    this.cloudCache,
                    null);

            Console.WriteLine("Accessing execution queue.");
            this.mainQueue = new CloudExecutionQueue();
        }

        /// <summary>
        /// Runs the execution engine, which eternally processes execution
        /// requests posted to the main queue.
        /// </summary>
        public void Run()
        {
            this.keepSwimming = true;

            while (this.keepSwimming)
            {
                // Pull request off queue.
                Console.WriteLine("Waiting for new work request.");
                CloudExecutionRequest executionRequest = this.mainQueue.GetRequest(block: true);
                if (!this.keepSwimming)
                {
                    // Exit without deleting request from queue.
                    // Request will become visible again after timeout expires.
                    break;
                }

                // TODO: For now, we immediately delete the requests we take.
                // Eventually we'll want to leave the request invisible until
                // some timeout expires so that other engines can pick it up
                // if we crash.
                this.mainQueue.DeleteRequest(executionRequest);

                Console.WriteLine("Received request with ID {0}.", executionRequest.Identifier);

                // Make a progress report to soothe nervous users.
                CloudExecutionReport statusUpdate = new CloudExecutionReport(
                    executionRequest.Identifier,
                    CloudExecutionReport.StatusCode.InProgress,
                    0,
                    null,
                    null,
                    0,
                    null);

                // Submit progress report.
                this.mainQueue.SubmitReport(statusUpdate, executionRequest.ReportQueue);

                // Do the requested operation.
                CloudExecutionReport report = null;
                switch (executionRequest.RequestedOperation)
                {
                    case CloudExecutionRequest.Operation.RunExecutable:
                        report = this.RunAnExecutable(executionRequest);
                        break;

                    case CloudExecutionRequest.Operation.CommitSuicide:
                        this.keepSwimming = false;
                        goto case CloudExecutionRequest.Operation.None;

                    case CloudExecutionRequest.Operation.DeleteQueue:
                        this.mainQueue.DeleteQueue(executionRequest.ReportQueue);
                        goto case CloudExecutionRequest.Operation.None;

                    case CloudExecutionRequest.Operation.None:
                        report = new CloudExecutionReport(
                            executionRequest.Identifier,
                            CloudExecutionReport.StatusCode.Completed);
                        break;

                    default:
                        // ToDo: This should probably be treated as an error.
                        goto case CloudExecutionRequest.Operation.None;
                }

                // Submit report.
                this.mainQueue.SubmitReport(report, executionRequest.ReportQueue);
            }
        }

        /// <summary>
        /// Stops the execution engine.
        /// </summary>
        public void Stop()
        {
            this.keepSwimming = false;
        }

        /// <summary>
        /// Run the requested executable and produce a report of the results.
        /// </summary>
        /// <param name="executionRequest">The execution request.</param>
        /// <returns>A report of the results.</returns>
        private CloudExecutionReport RunAnExecutable(CloudExecutionRequest executionRequest)
        {
            // REVIEW: How/whether to use this.
            BuildObject diagnosticsBase = new BuildObject(Path.Combine("nuobj", "diagnostics", "process"));

            // Prep working directory with input files and output dirs.
            // TODO: The below will throw cache exceptions if something
            // isn't there (they should all be though).  Need to catch
            // these and fail the execution request when this happens.
            WorkingDirectory workingDirectory = new WorkingDirectory(this.virtualIronRoot);
            foreach (BuildObjectValuePointer inputFile in executionRequest.InputFileMappings)
            {
                // REVIEW: How to determine cache container here.
                ItemCacheContainer container = ItemCacheContainer.Sources;
                if (this.multiplexedItemCache.GetItemSize(container, inputFile.ObjectHash) == -1)
                {
                    container = ItemCacheContainer.Objects;
                }

                // TODO: Move path/directory manipulation code into
                // WorkingDirectory and/or ItemCache.
                string inputFilePath = workingDirectory.PathTo(inputFile.RelativePath);
                Directory.CreateDirectory(Path.GetDirectoryName(inputFilePath));  // REVIEW: Still neeeded?
                this.multiplexedItemCache.FetchItemToFile(
                    container,
                    inputFile.ObjectHash,
                    inputFilePath);
            }

            foreach (BuildObject outputFile in executionRequest.OutputFiles)
            {
                workingDirectory.CreateDirectoryFor(outputFile);
            }

            // Run executable.
            ProcessInvoker pinv = new ProcessInvoker(
                workingDirectory,
                executionRequest.Executable,
                new string[] { executionRequest.Arguments },
                diagnosticsBase,
                null, // This is captureStdout.  TODO: Should cleanup how this is used in ProcessInvoker.
                null); // This is dbgText.  REVIEW: How/whether to use this.

            // When ProcessInvoker's constructor returns, the process has
            // finished running.
            Console.WriteLine("Request {0} completed in {1} seconds.", executionRequest.Identifier, pinv.CpuTime);

            // Store output files in the (cloud) item cache, and create a
            // list of the mappings.
            List<BuildObjectValuePointer> outputFileMappings = new List<BuildObjectValuePointer>();
            foreach (BuildObject outFile in executionRequest.OutputFiles)
            {
                if (File.Exists(workingDirectory.PathTo(outFile)))
                {
                    string fileHash = Util.hashFilesystemPath(workingDirectory.PathTo(outFile));
                    Util.Assert(!string.IsNullOrEmpty(fileHash));

                    // Note we explicitly write to the cloud cache here.
                    this.cloudCache.StoreItemFromFile(ItemCacheContainer.Objects, fileHash, workingDirectory.PathTo(outFile));
                    outputFileMappings.Add(new BuildObjectValuePointer(fileHash, outFile.getRelativePath()));
                }
            }

            // Collect the results into a report.
            CloudExecutionReport report = new CloudExecutionReport(
                executionRequest.Identifier,
                CloudExecutionReport.StatusCode.Completed,
                pinv.ExitCode,
                pinv.GetStdout(),
                pinv.GetStderr(),
                pinv.CpuTime,
                outputFileMappings);

            return report;
        }
    }
}
