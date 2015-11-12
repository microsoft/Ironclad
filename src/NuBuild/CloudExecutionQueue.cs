//--
// <copyright file="CloudExecutionQueue.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Configuration;
    using System.IO;
    using System.Threading;
    using Microsoft.WindowsAzure.Storage;
    using Microsoft.WindowsAzure.Storage.Queue;

    /// <summary>
    /// Represents the queue used to make requests of cloud execution engines.
    /// </summary>
    public class CloudExecutionQueue
    {
        // Note that queue names must be all lowercase.
        // See http://msdn.microsoft.com/en-us/library/dd179349.aspx.

        /// <summary>
        /// Maximum interval to wait between polls of the request queue.
        /// In milliseconds.
        /// </summary>
        /// <remarks>
        /// REVIEW: Is 30 seconds a reasonable cap?
        /// </remarks>
        private const int RequestQueuePollIntervalCap = 30000;

        /// <summary>
        /// Name of the request queue.
        /// </summary>
        private const string RequestQueueName = "requests";

        /// <summary>
        /// Name of the default report queue.
        /// </summary>
        private const string ReportQueueName = "reports";

        /// <summary>
        /// Expiration time for request/report queue entries.
        /// Most queue entries should be picked up almost immediately,
        /// this is to prevent orphaned entries from hanging around "forever".
        /// </summary>
        private readonly TimeSpan queueEntryTtl;

        /// <summary>
        /// Azure storage account we're using.
        /// </summary>
        private CloudStorageAccount storageAccount;

        /// <summary>
        /// Cloud queue client for working with cloud queues.
        /// </summary>
        private CloudQueueClient queueClient;

        /// <summary>
        /// Queue to hold execution requests.
        /// </summary>
        private CloudQueue requestQueue;

        /// <summary>
        /// Queue to hold execution reports.
        /// </summary>
        private CloudQueue clientReportQueue;

        /// <summary>
        /// Cache of current request's report queue.
        /// </summary>
        private CloudQueue cachedServerReportQueue;

        /// <summary>
        /// Name of the cached report queue.
        /// </summary>
        private string cachedServerReportQueueName;

        /// <summary>
        /// Waiters for execution reports.
        /// </summary>
        private Dictionary<string, CloudExecutionWaiter> reportWaiters;

        /// <summary>
        /// Lock for the reportWaiters dictionary.
        /// </summary>
        private Mutex reportWaitersLock;

        /// <summary>
        /// Event that is signaled (i.e. set) if we have active waiters for execution reports.
        /// </summary>
        private ManualResetEvent haveReportWaiters;

        /// <summary>
        /// Thread that monitors the report queue.
        /// </summary>
        private Thread monitoringThread;

        /// <summary>
        /// Initializes a new instance of the CloudExecutionQueue class.
        /// </summary>
        /// <remarks>
        /// This is the constructor for servers.
        /// </remarks>
        public CloudExecutionQueue()
        {
            // Work-around for running this code in CloudExecutionEngine.  TODO: Clean this up!
            // The BuildEngine.theEngine.getIronRoot() call needs to work for BuildObject code to function properly.
            if (BuildEngine.theEngine.getIronRoot() == null)
            {
                BuildEngine.theEngine.setIronRoot(Directory.GetCurrentDirectory());
            }

            this.queueEntryTtl = new TimeSpan(0, 30, 0);  // 30 minutes.

            // Create our CloudStorageAccount object.
            // REVIEW: Hard-coded connection string index "Ironclad".
            string connectionString = null;
            ConnectionStringSettings settings = ConfigurationManager.ConnectionStrings["Ironclad"];
            if (settings != null)
            {
                connectionString = settings.ConnectionString;
            }

            if (string.IsNullOrEmpty(connectionString))
            {
                throw new ConfigurationException("Azure connection string missing from your NuBuild.exe.config file!");
            }

            this.storageAccount = CloudStorageAccount.Parse(connectionString);

            this.queueClient = this.storageAccount.CreateCloudQueueClient();

            this.requestQueue = this.queueClient.GetQueueReference(CloudExecutionQueue.RequestQueueName);
            this.requestQueue.CreateIfNotExists();
        }

        /// <summary>
        /// Initializes a new instance of the CloudExecutionQueue class.
        /// </summary>
        /// <remarks>
        /// This is the constructor for clients (does extra stuff).
        /// </remarks>
        /// <param name="reportQueueName">Name of the report queue this client is using.</param>
        public CloudExecutionQueue(string reportQueueName)
            : this()
        {
            if (string.IsNullOrEmpty(reportQueueName))
            {
                // Use default shared report queue if none is specified.
                reportQueueName = CloudExecutionQueue.ReportQueueName;
            }
            else
            {
                // Schedule auto-deletion of our private report queue.
                // We do this by setting the initial invisibility of a delete queue request.
                // This will auto-clean up our private report queue if we exit unexpectedly.
                CloudExecutionRequest deleteQueueRequest = new CloudExecutionRequest(
                    reportQueueName,
                    reportQueueName,
                    CloudExecutionRequest.Operation.DeleteQueue,
                    null,
                    null,
                    null,
                    null
                    );
                CloudQueueMessage deleteQueueMessage = new CloudQueueMessage(deleteQueueRequest.ToXml());
                this.requestQueue.AddMessage(deleteQueueMessage, new TimeSpan(12, 0, 0), new TimeSpan(4, 0, 0));
            }

            this.clientReportQueue = this.queueClient.GetQueueReference(reportQueueName);
            this.clientReportQueue.CreateIfNotExists();

            this.reportWaiters = new Dictionary<string, CloudExecutionWaiter>();
            this.reportWaitersLock = new Mutex();
            this.haveReportWaiters = new ManualResetEvent(false);

            this.monitoringThread = new Thread(new ThreadStart(this.MonitorReportQueue));
            this.monitoringThread.IsBackground = true;
            this.monitoringThread.Name = "Report Queue Monitor";
            this.monitoringThread.Start();
        }

        /// <summary>
        /// Deletes the specified queue.
        /// </summary>
        /// <param name="queue">Name of the queue to delete.</param>
        public void DeleteQueue(string queueName)
        {
            CloudQueue goner = this.queueClient.GetQueueReference(queueName);
            goner.DeleteIfExists();
        }

        /// <summary>
        /// Submits a request for cloud execution.
        /// </summary>
        /// <param name="request">
        /// The CloudExecutionRequest detailing this request.
        /// </param>
        public void SubmitRequest(CloudExecutionRequest request)
        {
            CloudQueueMessage message = new CloudQueueMessage(request.ToXml());
            this.requestQueue.AddMessage(message, this.queueEntryTtl);
        }

        /// <summary>
        /// Gets the next request from the request queue.
        /// </summary>
        /// <param name="block">Whether to block.</param>
        /// <returns>Next request on the queue.</returns>
        public CloudExecutionRequest GetRequest(bool block = false)
        {
            int pollInterval = 1000;  // In milliseconds.

            CloudQueueMessage message = null;
            while ((message = this.requestQueue.GetMessage()) == null)
            {
                if (block)
                {
                    Thread.Sleep(pollInterval);

                    // Increase poll interval if we're below the cap.
                    if (pollInterval < RequestQueuePollIntervalCap)
                    {
                        // Increase by 1/10th of a second each time.
                        // This will take 14.5s to reach a 2s interval.
                        pollInterval += 100;
                    }

                    continue;
                }
                else
                {
                    return null;
                }
            }

            ////Console.WriteLine(message.AsString);

            CloudExecutionRequest request = CloudExecutionRequest.FromMessage(message);

            return request;
        }

        /// <summary>
        /// Deletes a request from the queue.
        /// Used by reader to indicate request completion.
        /// </summary>
        /// <param name="request">Request to delete.</param>
        public void DeleteRequest(CloudExecutionRequest request)
        {
            CloudQueueMessage message = request.Message;
            this.requestQueue.DeleteMessage(message);
        }

        /// <summary>
        /// Submits a report of cloud execution for processing by the submitter.
        /// </summary>
        /// <param name="report">Report to submit.</param>
        /// <param name="reportQueueName">Name of the report queue to submit to.</param>
        public void SubmitReport(CloudExecutionReport report, string reportQueueName)
        {
            // Check to see if we need to update the cached report queue.
            if (reportQueueName != this.cachedServerReportQueueName)
            {
                this.cachedServerReportQueue = this.queueClient.GetQueueReference(reportQueueName);
                this.cachedServerReportQueue.CreateIfNotExists();
                this.cachedServerReportQueueName = reportQueueName;
            }

            CloudQueueMessage message = new CloudQueueMessage(report.ToXml());
            this.cachedServerReportQueue.AddMessage(message, this.queueEntryTtl);
        }

        /// <summary>
        /// Gets the requested execution report off of the queue.
        /// </summary>
        /// <param name="reportIdentifier">Report to retrieve.</param>
        /// <param name="numberOfOtherWaiters">Count of remaining waiters after our report arrives.</param>
        /// <returns>The execution report in question.</returns>
        public CloudExecutionReport GetReport(string reportIdentifier, out int numberOfOtherWaiters)
        {
            CloudExecutionWaiter waiter = new CloudExecutionWaiter();

            // Add the desired report to the dictionary under lock.
            this.reportWaitersLock.WaitOne();
            this.reportWaiters.Add(reportIdentifier, waiter);
            this.haveReportWaiters.Set();
            this.reportWaitersLock.ReleaseMutex();

            // Wait for report to arrive, and then return it.
            return waiter.WaitForReport(out numberOfOtherWaiters);
        }

        /// <summary>
        /// Procedure performed by the report queue monitoring thread.
        /// </summary>
        private void MonitorReportQueue()
        {
            const int MaxBatchSize = 32;  // Maximum allowed by API.
            TimeSpan invisibleTime = new TimeSpan(0, 0, 2);  // Two seconds.
            TimeSpan pollInterval = new TimeSpan(0, 0, 1);  // One second.

            List<CloudQueueMessage> messages;
            bool anyForUs;

            while (true)
            {
                // Don't bother doing anything if we don't have any active waiters.
                this.haveReportWaiters.WaitOne();

                // Get a new batch of messages.
                // No other queue readers will see these until the invisibleTime expires.
                messages = new List<CloudQueueMessage>(this.clientReportQueue.GetMessages(MaxBatchSize, invisibleTime));
                anyForUs = false;

                foreach (CloudQueueMessage message in messages)
                {
                    CloudExecutionReport report = CloudExecutionReport.FromMessage(message);

                    // Lookup the waiter for this report under lock.
                    CloudExecutionWaiter waiter;
                    int remainingWaitersCount = 0;
                    this.reportWaitersLock.WaitOne();
                    bool foundWaiter = this.reportWaiters.TryGetValue(report.Identifier, out waiter);
                    if (foundWaiter && report.Status == CloudExecutionReport.StatusCode.Completed)
                    {
                        this.reportWaiters.Remove(report.Identifier);
                        remainingWaitersCount = this.reportWaiters.Count;
                        if (remainingWaitersCount == 0)
                        {
                            // We don't have anyone else waiting for a report.
                            this.haveReportWaiters.Reset();
                        }
                    }

                    this.reportWaitersLock.ReleaseMutex();

                    if (foundWaiter)
                    {
                        // We delete the report from the queue right away,
                        // as nobody else should ever be interested in it.
                        this.clientReportQueue.DeleteMessage(message);
                        anyForUs = true;

                        switch (report.Status)
                        {
                            case CloudExecutionReport.StatusCode.Completed:
                                waiter.GiveReportToWaiter(report, remainingWaitersCount);
                                break;

                            case CloudExecutionReport.StatusCode.InProgress:
                                Console.WriteLine("Node '{0}' reports request '{1}' is in progress.", report.ProcessingNode, report.Identifier);
                                break;

                            default:
                                // REVIEW: Or just Assert here?  This should never happen.
                                Console.WriteLine("Node '{0}' reports strange status '{1}' for request '{2}'.", report.ProcessingNode, report.Status, report.Identifier);
                                break;
                        }
                    }
                }

                if ((messages.Count != 0) && !anyForUs)
                {
                    // Give other client(s) a chance to get their messages.
                    Thread.Sleep(invisibleTime + pollInterval + pollInterval);
                }
                else
                {
                    Thread.Sleep(pollInterval);
                }
            }
        }
    }
}
