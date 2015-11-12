//--
// <copyright file="ProcessInvokeAsyncWorker.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;

    /// <summary>
    /// Representation of an asynchronous verb worker.
    /// </summary>
    internal class ProcessInvokeAsyncWorker : IVerbWorker
    {
        /// <summary>
        /// The private working directory for this worker to work in.
        /// </summary>
        private WorkingDirectory workingDirectory;

        /// <summary>
        /// The verb whose worker this is.
        /// </summary>
        private IProcessInvokeAsyncVerb verb;

        /// <summary>
        /// The executable to run.
        /// </summary>
        private string executable;

        /// <summary>
        /// The command line arguments to provide to the executable.
        /// </summary>
        private string[] args;

        /// <summary>
        /// How to handle the exit code from running the executable.
        /// </summary>
        private ProcessExitCodeHandling exitCodeHandling;

        /// <summary>
        /// Where to (optionally) collect diagnostics.
        /// </summary>
        private BuildObject failureBase;

        /// <summary>
        /// Where to capture standard out (I think).
        /// </summary>
        private BuildObject captureStdout;

        /// <summary>
        /// Debugging text for something or another.
        /// </summary>
        private string dbgText;

        /// <summary>
        /// Whether to allow an absolute (rather than relative) file path to the executable.
        /// </summary>
        private bool allowAbsoluteExe;

        /// <summary>
        /// Whether to allow absolute (rather than relative) file paths as arguments.
        /// </summary>
        private bool allowAbsoluteArgs;

        /// <summary>
        /// The working directory to use.
        /// </summary>
        private string workingDirOverride;

        /// <summary>
        /// Whether to return the standard output from the process in the Complete call.
        /// </summary>
        private bool returnStandardOut;

        /// <summary>
        /// Whether to return the error output from the process in the Complete call.
        /// </summary>
        private bool returnStandardError;

        /// <summary>
        /// The IProcessInvoker (either a ProcessInvoker or a CloudSubmitter) instance we use to run this executable (either locally or in the cloud).
        /// </summary>
        private IProcessInvoker pinv;

        /// <summary>
        /// Whether to run the executable in the cloud.
        /// </summary>
        private bool useCloudExecution;

        /// <summary>
        /// List of input files needed by the executable.
        /// </summary>
        private List<BuildObject> inputFiles;

        /// <summary>
        /// List of output files produced by the executable.
        /// </summary>
        private List<BuildObject> outputFiles;

        /// <summary>
        /// Initializes a new instance of the ProcessInvokeAsyncWorker class.
        /// </summary>
        /// <param name="workingDirectory">The private working directory for this worker to work in.</param>
        /// <param name="verb">The verb whose worker this is.</param>
        /// <param name="executable">The executable to run.</param>
        /// <param name="args">The command line arguments to provide to the executable.</param>
        /// <param name="exitCodeHandling">How to handle the return code from running the executable.</param>
        /// <param name="failureBase">Not sure what this is -- some debugging/diagnostic thing.</param>
        /// <param name="captureStdout">Where to capture standard out (I think).</param>
        /// <param name="dbgText">Debugging text for something or another.</param>
        /// <param name="allowAbsoluteExe">Whether to allow an absolute (rather than relative) file path to the executable.</param>
        /// <param name="allowAbsoluteArgs">Whether to allow absolute (rather than relative) file paths as arguments.</param>
        /// <param name="workingDirOverride">The working directory to use.</param>
        /// <param name="returnStandardOut">Whether to return the standard output of the process.</param>
        /// <param name="returnStandardError">Whether to return the standard error output of the process.</param>
        /// <param name="allowCloudExecution">Whether to allow this worker to run the executable in the cloud.</param>
        /// <remarks>
        /// TODO: executable should be a BuildObject, like every other dependency.
        /// </remarks>
        public ProcessInvokeAsyncWorker(
            WorkingDirectory workingDirectory,
            IProcessInvokeAsyncVerb verb,
            string executable,
            string[] args,
            ProcessExitCodeHandling exitCodeHandling,
            BuildObject failureBase,
            BuildObject captureStdout = null,
            string dbgText = null,
            bool allowAbsoluteExe = false,
            bool allowAbsoluteArgs = false,
            string workingDirOverride = null,
            bool returnStandardOut = false,
            bool returnStandardError = false,
            bool allowCloudExecution = false)
        {
            this.workingDirectory = workingDirectory;
            this.verb = verb;
            this.executable = executable;
            this.args = args;
            this.exitCodeHandling = exitCodeHandling;
            this.failureBase = failureBase;
            this.captureStdout = captureStdout;
            this.dbgText = dbgText;
            this.allowAbsoluteExe = allowAbsoluteExe;
            this.allowAbsoluteArgs = allowAbsoluteArgs;
            this.workingDirOverride = workingDirOverride;
            this.returnStandardOut = returnStandardOut;
            this.returnStandardError = returnStandardError;

            if (allowCloudExecution)
            {
                // Verbs cannot allow cloud execution if they allow absolute paths to exes or args.
                Util.Assert(!this.allowAbsoluteExe);
                Util.Assert(!this.allowAbsoluteArgs);
                Util.Assert(this.workingDirOverride == null);

                if (BuildEngine.theEngine.CloudExecutionQueue != null)
                {
                    // We're good to go for cloud execution.
                    this.useCloudExecution = true;

                    // REVIEW: If there are other things we should do on the main thread prior to CloudSubmitter invocation, we should do them here.
                    this.inputFiles = this.GetInputFiles();
                    this.outputFiles = new List<BuildObject>(this.verb.getOutputs());
                    this.outputFiles.AddRange(this.verb.getFailureOutputs());
                }
            }
        }

        /// <summary>
        /// Indicates whether this work needs to be scheduled asynchronously.
        /// Since this is the asynchronous implementation, always returns Async.
        /// </summary>
        /// <returns>Always returns Async.</returns>
        public VerbWorkerType IsSync()
        {
            return VerbWorkerType.Async;
        }

        /// <summary>
        /// Gets the private working directory this verb executes in.
        /// </summary>
        /// <returns>The directory this verb executes in.</returns>
        public WorkingDirectory GetWorkingDirectory()
        {
            return this.workingDirectory;
        }

        /// <summary>
        /// Performs the slow, asynchronous work.
        /// </summary>
        /// <remarks>
        /// Does not run on the main thread, so should not access caches
        /// (or do anything else that expects to be synchronous).
        /// When this returns, the work is expected to have completed.
        /// </remarks>
        public void RunAsync()
        {
            if (this.useCloudExecution)
            {
                // REVIEW: Would prefer to use the verb's input hash value as the request identifier below.
                this.pinv = new CloudSubmitter(
                    Path.GetRandomFileName(),
                    this.workingDirectory,
                    this.inputFiles,
                    this.outputFiles,
                    this.executable,
                    this.args,
                    this.failureBase,
                    this.captureStdout,
                    this.dbgText);
            }
            else
            {
                this.pinv = new ProcessInvoker(
                    this.workingDirectory,
                    this.executable,
                    this.args,
                    this.failureBase,
                    this.captureStdout,
                    this.dbgText,
                    this.allowAbsoluteExe,
                    this.allowAbsoluteArgs,
                    this.workingDirOverride);
            }
        }

        /// <summary>
        /// Performs the completion work for Async workers, and is called
        /// after the runAsync method returns.  Returns the ultimate
        /// disposition of the activity.
        /// </summary>
        /// <remarks>
        /// This method runs synchronously on the main thread.
        /// It can tidy up the state after async work, and store results
        /// in the Repository.
        /// Thou shalt not return Stale.
        /// </remarks>
        /// <returns>The disposition of this verb's worker's work.</returns>
        public Disposition Complete()
        {
            this.verb.RecordProcessInvokeCpuTime(this.pinv.CpuTime);

            string stdout = null;
            if (this.returnStandardOut)
            {
                stdout = this.pinv.GetStdout();
            }

            string stderr = null;
            if (this.returnStandardError)
            {
                stderr = this.pinv.GetStderr();
            }

            Disposition disposition;
            if (this.exitCodeHandling == ProcessExitCodeHandling.NonzeroIsOkay || this.pinv.ExitCode == 0)
            {
                disposition = new Fresh();
            }
            else
            {
                // Sheesh. Some tools emit error messages to stdout.
                // REVIEW: Provide full command line here rather than just executable (like old version did)?
                Failed f = new Failed(this.pinv.GetStdout() + this.pinv.GetStderr());
                f.AddError("Executable: " + this.executable + "\n");
                disposition = f;
            }

            return this.verb.Complete(this.workingDirectory, this.pinv.CpuTime, stdout, stderr, disposition);
        }

        /// <summary>
        /// Gets the input files needed for verb execution.
        /// </summary>
        /// <returns>List of the verb's input files.</returns>
        private List<BuildObject> GetInputFiles()
        {
            DependencyDisposition ddisp;
            List<BuildObject> inputFiles = new List<BuildObject>();

            foreach (BuildObject input in this.verb.getDependencies(out ddisp))
            {
                if (!(input is VirtualBuildObject))
                {
                    inputFiles.Add(input);
                }
            }

            return inputFiles;
        }
    }
}
