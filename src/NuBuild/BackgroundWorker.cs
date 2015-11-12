//--
// <copyright file="BackgroundWorker.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Threading;
    using System.Threading.Tasks;

    /// <summary>
    /// Type of procedure that the background worker thread runs.
    /// </summary>
    /// <param name="argument1">Some argument.</param>
    /// <param name="argument2">Another argument.</param>
    public delegate void BackgroundWorkerProcedure(object argument1, object argument2);

    /// <summary>
    /// Represents a single background worker thread that sequentially performs
    /// the work added to its queue.
    /// </summary>
    /// <remarks>
    /// This class is not related to System.ComponentModel.BackgroundWorker,
    /// which provides different functionality.
    /// </remarks>
    public class BackgroundWorker : IDisposable
    {
        /// <summary>
        /// Thread that performs the background work.
        /// </summary>
        private Thread workerThread;

        /// <summary>
        /// Queue of work for background worker to perform.
        /// </summary>
        private Queue<BackgroundWorkerQueueItem> workQueue;

        /// <summary>
        /// Lock protecting the work queue.
        /// </summary>
        private Mutex workQueueLock;

        /// <summary>
        /// Event that is signalled when new items are placed on the workQueue.
        /// </summary>
        private AutoResetEvent workQueueHasNewWork;

        /// <summary>
        /// Count of work items queued to this BackgroundWorker.
        /// </summary>
        private volatile uint workItemsQueued;

        /// <summary>
        /// Count of work item procedures performed by this BackgroundWorker.
        /// </summary>
        private volatile uint workItemsPerformed;

        /// <summary>
        /// Count of work item procedures known to have failed.
        /// </summary>
        private volatile uint workItemsFailed;

        /// <summary>
        /// Flag indicating whether or not the worker thread should exit.
        /// </summary>
        private volatile bool ourWorkIsNotDone;

        /// <summary>
        /// Flag indicating whether or not Dispose has already been called.
        /// </summary>
        private bool disposed;

        /// <summary>
        /// Initializes a new instance of the BackgroundWorker class.
        /// </summary>
        public BackgroundWorker()
        {
            this.workQueue = new Queue<BackgroundWorkerQueueItem>();
            this.workQueueLock = new Mutex();
            this.workQueueHasNewWork = new AutoResetEvent(false);
            this.workItemsQueued = 0;
            this.workItemsPerformed = 0;
            this.workItemsFailed = 0;
            this.ourWorkIsNotDone = true;
            this.disposed = false;

            this.workerThread = new Thread(new ThreadStart(this.WorkerThreadMain));

            // REVIEW: Start worker thread only after the first item is queued?
            this.workerThread.Start();
        }

        /// <summary>
        /// Gets the count of work items queued to this BackgroundWorker.
        /// </summary>
        public uint GetWorkItemsQueued
        {
            get { return this.workItemsQueued; }
        }

        /// <summary>
        /// Gets the count of work item procedures performed by this
        /// BackgroundWorker.
        /// </summary>
        public uint GetWorkItemsPerformed
        {
            get { return this.workItemsPerformed; }
        }

        /// <summary>
        /// Gets the count of work item procedures known to have failed.
        /// </summary>
        public uint GetWorkItemsFailed
        {
            get { return this.workItemsFailed; }
        }

        /// <summary>
        /// Adds new work to the background worker's work queue.
        /// </summary>
        /// <param name="procedure">
        /// Procedure the background worker will run.
        /// </param>
        /// <param name="argument1">First argument for procedure.</param>
        /// <param name="argument2">Second argument for procedure.</param>
        public void QueueWork(BackgroundWorkerProcedure procedure, object argument1, object argument2)
        {
            BackgroundWorkerQueueItem workItem = new BackgroundWorkerQueueItem(procedure, argument1, argument2);

            this.workQueueLock.WaitOne();
            this.workQueue.Enqueue(workItem);
            this.workItemsQueued++;
            this.workQueueLock.ReleaseMutex();

            this.workQueueHasNewWork.Set();
        }

        /// <summary>
        /// Tells the worker thread to stop running after completing the
        /// currently queued work items.
        /// </summary>
        public void StopWork()
        {
            this.QueueWork(this.StopWorkerThread, null, null);
        }

        /// <summary>
        /// Wait for the worker thread to exit after a StopWork request.
        /// </summary>
        /// <remarks>
        /// This routine is primarily for making sure the worker thread has
        /// completed operation before collecting stats from it
        /// (i.e. calling 'GetWorkItemsPerformed').  Since we don't mark our
        /// worker thread as a "background" thread, the process will not exit
        /// until after our thread exits.  So this method is not needed for the
        /// purpose of keeping the main thread and thus process alive until the
        /// worker thread is done.
        /// </remarks>
        public void WaitForCompletion()
        {
            this.workerThread.Join();
        }

        /// <summary>
        /// Releases resources.
        /// </summary>
        public void Dispose()
        {
            this.Dispose(true);
            GC.SuppressFinalize(this);
        }

        /// <summary>
        /// Releases unmanaged and (optionally) managed resources.
        /// </summary>
        /// <param name="disposing">Whether or not to release managed resources.</param>
        protected virtual void Dispose(bool disposing)
        {
            if (this.disposed)
            {
                return;
            }

            if (disposing)
            {
                this.workQueueLock.Dispose();
                this.workQueueHasNewWork.Dispose();
            }

            this.disposed = true;
        }

        /// <summary>
        /// Special BackgroundWorkerProcedure for stopping the worker thread.
        /// </summary>
        /// <remarks>
        /// Note that this procedure ends up being counted in the statistics
        /// we keep about the number of work items queued/performed.
        /// </remarks>
        /// <param name="unused1">The parameter is not used.</param>
        /// <param name="unused2">The parameter is not used.</param>
        private void StopWorkerThread(
            object unused1,
            object unused2)
        {
            this.ourWorkIsNotDone = false;
        }

        /// <summary>
        /// Procedure performed by the background worker thread.
        /// </summary>
        [System.Diagnostics.CodeAnalysis.SuppressMessage("Microsoft.Design", "CA1031:DoNotCatchGeneralExceptionTypes", Justification = "We really do want to catch all exceptions in this case")]
        private void WorkerThreadMain()
        {
            List<BackgroundWorkerQueueItem> toDoList = new List<BackgroundWorkerQueueItem>();

            // -
            // Run until we're told to stop.
            // -
            while (this.ourWorkIsNotDone)
            {
                // -
                // Wait for new work to be added to the queue.
                // -
                if (this.workQueueHasNewWork.WaitOne())
                {
                    toDoList.Clear();

                    // -
                    // Pull all queued work items off the global work queue
                    // (while holding the lock), and place them on our
                    // thread-local toDoList.
                    // -
                    this.workQueueLock.WaitOne();

                    while (this.workQueue.Count > 0)
                    {
                        toDoList.Add(this.workQueue.Dequeue());
                    }

                    this.workQueueLock.ReleaseMutex();

                    // -
                    // Do the requested work.
                    // -
                    foreach (BackgroundWorkerQueueItem workItem in toDoList)
                    {
                        try
                        {
                            workItem.Procedure(workItem.Argument1, workItem.Argument2);
                            this.workItemsPerformed++;
                        }
                        catch
                        {
                            // -
                            // Swallow all errors caused by the work item.
                            // But count how often this happens.
                            // -
                            this.workItemsFailed++;
                        }
                    }
                }
            }
        }

        /// <summary>
        /// Represents a work item on the background worker's work queue.
        /// </summary>
        private class BackgroundWorkerQueueItem
        {
            /// <summary>
            /// The procedure the background worker runs.
            /// </summary>
            private BackgroundWorkerProcedure procedure;

            /// <summary>
            /// The first argument to pass to the procedure.
            /// </summary>
            private object argument1;

            /// <summary>
            /// The second argument to pass to the procedure.
            /// </summary>
            private object argument2;

            /// <summary>
            /// Initializes a new instance of the BackgroundWorkerQueueItem class.
            /// </summary>
            /// <param name="procedure">Procedure to run.</param>
            /// <param name="argument1">First argument for procedure.</param>
            /// <param name="argument2">Second argument for procedure.</param>
            public BackgroundWorkerQueueItem(
                BackgroundWorkerProcedure procedure,
                object argument1,
                object argument2)
            {
                this.procedure = procedure;
                this.argument1 = argument1;
                this.argument2 = argument2;
            }

            /// <summary>
            /// Gets the procedure the background worker runs.
            /// </summary>
            public BackgroundWorkerProcedure Procedure
            {
                get { return this.procedure; }
            }

            /// <summary>
            /// Gets the first argument to pass to the procedure.
            /// </summary>
            public object Argument1
            {
                get { return this.argument1; }
            }

            /// <summary>
            /// Gets the second argument to pass to the procedure.
            /// </summary>
            public object Argument2
            {
                get { return this.argument2; }
            }
        }
    }
}
