//--
// <copyright file="VerbRunner.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;
    using System.Threading;

    /// <summary>
    /// Infrastructure for performing VerbWorker work, possibly asynchronously.
    /// Conceptually, this is the part of the scheduler that runs verbs.
    /// </summary>
    /// <remarks>
    /// There is only one instance of this class in the system.
    /// </remarks>
    internal class VerbRunner
    {
        /// <summary>
        /// Whether or not to run in a special debugging mode where everything
        /// is run on a single thread (including any 'async' work).
        /// </summary>
        /// <remarks>
        /// Without this, JonH reported problems: "Breaking and examining
        /// variables on a second thread seems to send VS into fits".
        /// </remarks>
        private const bool DebugOneThread = false;

        /// <summary>
        /// A sorter of verbs (special case for <c>DafnyVerifyOneVerb</c> only?).
        /// </summary>
        private VerbToposorter verbToposorter;

        /// <summary>
        /// Event used to signal the completion of some (possibly asynchronous)
        /// work.
        /// </summary>
        private ManualResetEvent completionEvent;

        /// <summary>
        /// Lock protecting the runnableVerbs and startedVerbs collections.
        /// </summary>
        private ReaderWriterLock verbStateLock;

        /// <summary>
        /// Verbs that have been submitted, but have not yet started to run.
        /// </summary>
        private HashSet<IVerb> runnableVerbs;

        /// <summary>
        /// Verbs that have started to run (and may or may not have
        /// completed; once added we never remove them from this collection).
        /// </summary>
        private HashSet<IVerb> startedVerbs;

        /// <summary>
        /// Degree of asynchronicity to allow (i.e. number of async threads).
        /// </summary>
        private int jobParallelism;

        /// <summary>
        /// Lock protecting the taskCompletions list.
        /// </summary>
        private ReaderWriterLock taskCompletionsLock;

        /// <summary>
        /// Tasks that have completed running, but not yet processed.
        /// </summary>
        private List<TaskCompletion> taskCompletions;

        /// <summary>
        /// Number of currently running tasks.
        /// </summary>
        private int runningTasks;

        /// <summary>
        /// Initializes a new instance of the VerbRunner class.
        /// </summary>
        /// <param name="verbToposorter">The verb sorter to use.</param>
        /// <param name="jobParallelism">Degree of parallelism to allow.</param>
        public VerbRunner(VerbToposorter verbToposorter, int jobParallelism)
        {
            this.verbToposorter = verbToposorter;
            this.jobParallelism = jobParallelism;
            this.completionEvent = new ManualResetEvent(true);

            this.verbStateLock = new ReaderWriterLock();
            this.runnableVerbs = new HashSet<IVerb>();
            this.startedVerbs = new HashSet<IVerb>();

            this.taskCompletionsLock = new ReaderWriterLock();
            this.taskCompletions = new List<TaskCompletion>();

            this.runningTasks = 0;
        }

        /// <summary>
        /// Submits a verb for execution.
        /// </summary>
        /// <param name="verb">The verb to submit.</param>
        public void submitVerb(IVerb verb)
        {
            this.verbStateLock.AcquireWriterLock(Timeout.Infinite);

            // If lock contention were an issue, we could accumulate these
            // on a thread-local collection, then batch them into runnableVerbs
            // during the lock inside scheduleAndWait.
            if (!this.startedVerbs.Contains(verb))
            {
                this.runnableVerbs.Add(verb);
            }

            this.verbStateLock.ReleaseLock();
        }

        /// <summary>
        /// Called by the scheduler to run the verbs which can be run.
        /// </summary>
        /// <param name="dbgScheduler">
        /// The scheduler calling us (for debugging).
        /// </param>
        /// <returns>A list of tasks (verb runs) that have completed.</returns>
        public List<TaskCompletion> scheduleAndWait(Scheduler dbgScheduler)
        {
            while (true)
            {
                List<TaskCompletion> taskCompletionBatch;

                // Loop until something gets done.
                while (true)
                {
                    this.dbgUpdateProgress(dbgScheduler);

                    this.taskCompletionsLock.AcquireWriterLock(Timeout.Infinite);
                    taskCompletionBatch = this.taskCompletions;
                    this.taskCompletions = new List<TaskCompletion>();
                    this.completionEvent.Reset();
                    this.taskCompletionsLock.ReleaseLock();

                    bool canProcessCompletedTask = taskCompletionBatch.Count() > 0;
                    bool canStartNewTask = (this.runnableVerbs.Count() > 0) && (this.jobParallelism > this.runningTasks);
                    if (!(canProcessCompletedTask || canStartNewTask))
                    {
                        // Nothing will change until a running task finishes. Snooze.
                        if (this.runningTasks == 0)
                        {
                            dbgScheduler.dbgDumpWaitIndex();
                            Util.Assert(false);
                        }

                        this.completionEvent.WaitOne();
                        continue;
                    }

                    break;
                }

                int numCompletedTasks = taskCompletionBatch.Count();
                Say(string.Format("marking {0} tasks completing; runningTasks now {1}", numCompletedTasks, this.runningTasks));
                this.runningTasks -= numCompletedTasks;

                int idleTasks = this.jobParallelism - this.runningTasks;

                if (idleTasks > 0)
                {
                    this.verbStateLock.AcquireWriterLock(Timeout.Infinite);

                    List<IVerb> runnableVerbsBatch = new List<IVerb>(this.runnableVerbs);
                    Say("AsyncRunner toposorting " + runnableVerbsBatch.Count() + " verbs");
                    runnableVerbsBatch.Sort(this.verbToposorter);

                    ////Logger.WriteLine(string.Format("verbToposorter({0}) yields:", runnableVerbsBatch.Count));
                    ////foreach (IVerb verb in runnableVerbsBatch)
                    ////{
                    ////    Logger.WriteLine("  " + verb.ToString() + " @ "+ this.verbToposorter.getDepth(verb));
                    ////}

                    for (int i = 0; i < idleTasks && i < runnableVerbsBatch.Count(); i++)
                    {
                        IVerb verb = runnableVerbsBatch[i];
                        this.startTask(verb);
                        this.runnableVerbs.Remove(verb);
                        this.startedVerbs.Add(verb);
                    }

                    this.verbStateLock.ReleaseLock();
                }

                if (taskCompletionBatch.Count() > 0 || this.runningTasks == 0)
                {
                    // Something actually got done, so the caller could meaningfully schedule more work.
                    return taskCompletionBatch;
                }
            }
        }

        /// <summary>
        /// Writes debugging output to the logger.
        /// </summary>
        /// <param name="msg">The message to write.</param>
        private static void Say(string msg)
        {
            if (Scheduler.Debug)
            {
#pragma warning disable 162
                Logger.WriteLine("[async] " + msg);
#pragma warning restore 162
            }
        }

        /// <summary>
        /// Reports current progress to the scheduler.
        /// </summary>
        /// <param name="dbgScheduler">The scheduler.</param>
        private void dbgUpdateProgress(Scheduler dbgScheduler)
        {
            dbgScheduler.dbgUpdateProgress(this.runnableVerbs.Count(), this.runningTasks);
        }

        /// <summary>
        /// Starts a task (i.e. runs a verb).
        /// </summary>
        /// <param name="verb">The verb to run.</param>
        private void startTask(IVerb verb)
        {
            this.runningTasks += 1;

            // We execute the verb in a private build tree (WorkingDirectory).
            WorkingDirectory workingDirectory = new WorkingDirectory(BuildEngine.theEngine.getIronRoot());

            // Note that we call PrepareForVerb prior to the verb's getWorker
            // method as the getWorker call might do some of the work directly.
            // REVIEW: We might want to change our contract with getWorker to
            // disallow it from touching files in the working directory (so we
            // don't have to prep the working dir in the remote execution case).
            this.PrepareForVerb(workingDirectory, verb);

            IVerbWorker worker = verb.getWorker(workingDirectory);
            if (worker.IsSync() == VerbWorkerType.Sync)
            {
                this.completeTask(verb, worker);
            }
            else
            {
                AsyncVerbTask task = new AsyncVerbTask(this, worker, verb);
                Say(string.Format("scheduling {0}", verb));
#pragma warning disable 162
                if (DebugOneThread)
                {
                    task.Run();
                }
                else
                {
                    new Thread(new ThreadStart(task.Run)).Start();
                }
#pragma warning restore 162
            }
        }

        /// <summary>
        /// Prepares the working directory tree for a verb's execution.
        /// </summary>
        /// <param name="verb">The verb whose execution we're preparing for.</param>
        private void PrepareForVerb(WorkingDirectory workingDirectory, IVerb verb)
        {
            // Debugging aide: write out the abstract id for this verb.
            File.WriteAllText(workingDirectory.PathTo("Debug.txt"), verb.getAbstractIdentifier().ToString());

            Repository repository = BuildEngine.theEngine.Repository;

            // Copy all verb inputs from the item cache to here.
            DependencyDisposition ddisp;
            foreach (BuildObject input in verb.getDependencies(out ddisp))
            {
                if (!(input is VirtualBuildObject))
                {
                    workingDirectory.CreateDirectoryFor(input);  // REVIEW: No longer needed?
                    repository.Fetch(workingDirectory, input);
                }
            }

            // Ensures that the directory tree for each of the verb's outputs exists.
            foreach (BuildObject output in verb.getOutputs())
            {
                workingDirectory.CreateDirectoryFor(output);
            }
        }

        /// <summary>
        /// Completes a task (verb run).
        /// </summary>
        /// <remarks>
        /// Note that for Async verb workers, this method runs on a separate thread.
        /// </remarks>
        /// <param name="verb">The verb which was run.</param>
        /// <param name="worker">The verb's worker.</param>
        private void completeTask(IVerb verb, IVerbWorker worker)
        {
            this.taskCompletionsLock.AcquireWriterLock(Timeout.Infinite);
            Disposition disp = worker.Complete();
            TaskCompletion tc = new TaskCompletion(worker.GetWorkingDirectory(), verb, disp);
            this.taskCompletions.Add(tc);
            this.completionEvent.Set();
            this.taskCompletionsLock.ReleaseWriterLock();
        }

        /// <summary>
        /// Represents a completed task.
        /// Ties a Disposition to the Verb instance which created it.
        /// </summary>
        /// <remarks>
        /// REVIEW: Keep the entire worker instead of just the working dir?
        /// Might want to run worker.Complete on main thread after pulling this
        /// off the task completions list instead of on separate thread prior to
        /// putting it on the task completions list.
        /// </remarks>
        public class TaskCompletion
        {
            /// <summary>
            /// The directory the verb executed in.
            /// </summary>
            public WorkingDirectory workingDirectory;

            /// <summary>
            /// The verb whose completion this instance describes.
            /// </summary>
            public IVerb verb;

            /// <summary>
            /// The disposition of this task.
            /// </summary>
            public Disposition disposition;

            /// <summary>
            /// Initializes a new instance of the TaskCompletion class.
            /// </summary>
            /// <param name="workingDirectory">
            /// The private working directory the task executed in.
            /// </param>
            /// <param name="verb">
            /// The verb whose completion this instance describes.
            /// </param>
            /// <param name="disposition">
            /// The disposition of this task.
            /// </param>
            public TaskCompletion(WorkingDirectory workingDirectory, IVerb verb, Disposition disposition)
            {
                this.workingDirectory = workingDirectory;
                this.verb = verb;
                this.disposition = disposition;
            }
        }

        /// <summary>
        /// Representation of an asynchronous task.
        /// </summary>
        /// <remarks>
        /// REVIEW: Do we need this class? It is 1:1 with the worker.
        /// </remarks>
        private class AsyncVerbTask
        {
            /// <summary>
            /// The verb-running part of the scheduler.
            /// </summary>
            private VerbRunner runner;

            /// <summary>
            /// The worker of this verb task.
            /// </summary>
            private IVerbWorker worker;

            /// <summary>
            /// The verb associated with this task/worker.
            /// </summary>
            /// <remarks>
            /// Don't call any methods on this guy while on async thread!
            /// It's just here to carry back to the TaskCompletion on the main thread.
            /// </remarks>
            private IVerb verb;

            /// <summary>
            /// Initializes a new instance of the AsyncVerbTask class.
            /// </summary>
            /// <param name="runner">
            /// The verb running part of the scheduler.
            /// </param>
            /// <param name="worker">
            /// The worker of this verb task.
            /// </param>
            /// <param name="verb">
            /// The verb associated with this task/worker.
            /// </param>
            public AsyncVerbTask(VerbRunner runner, IVerbWorker worker, IVerb verb)
            {
                this.runner = runner;
                this.worker = worker;
                this.verb = verb;
            }

            /// <summary>
            /// Runs the task.
            /// </summary>
            /// <remarks>
            /// Note that this method runs on a separate thread.
            /// Only make thread-safe calls from here.
            /// </remarks>
            public void Run()
            {
                Say(string.Format("launching {0}", this.verb));
                Logger.WriteLine(string.Format("{0} launched", this.verb));
                this.worker.RunAsync();
                this.runner.completeTask(this.verb, this.worker);
                Say(string.Format("completed {0}", this.verb));
            }
        }
    }
}
