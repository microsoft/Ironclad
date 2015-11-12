//--
// <copyright file="ProcessInvoker.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Diagnostics;
    using System.IO;
    using System.Text;

    /// <summary>
    /// Represents the invoker of processes that do the work of a verb worker.
    /// </summary>
    public class ProcessInvoker : IProcessInvoker
    {
        /// <summary>
        /// Whether to always emit diagnostic output.
        /// </summary>
        private const bool AlwaysEmitDiagnostics = true;

        /// <summary>
        /// The CPU time used by the process, in seconds.
        /// </summary>
        private double cpuTime;

        /// <summary>
        /// The exit code returned by the process.
        /// </summary>
        private int exitCode;

        /// <summary>
        /// The stream used to collect standard out to a file (if requested).
        /// </summary>
        private StreamWriter stdoutFile;

        /// <summary>
        /// The temporary file in which to store standard out (if requested).
        /// </summary>
        private BuildObject tmpStdout;

        /// <summary>
        /// Where standard out is collected by default.
        /// </summary>
        private StringBuilder stdout;

        /// <summary>
        /// Where standard error is collected.
        /// </summary>
        private StringBuilder stderr;

        /// <summary>
        /// The private working directory for the process we invoke.
        /// </summary>
        private WorkingDirectory workingDirectory;

        /// <summary>
        /// Initializes a new instance of the ProcessInvoker class.
        /// </summary>
        /// <param name="workingDirectory">The working directory the process is started in.</param>
        /// <param name="executable">The executable to run.</param>
        /// <param name="args">The command line arguments to provide to the executable.</param>
        /// <param name="failureBase">Not sure what this is -- some debugging/diagnostic thing.</param>
        /// <param name="captureStdout">Where to (optionally) capture standard out.</param>
        /// <param name="dbgText">Debugging text for something or another.</param>
        /// <param name="allowAbsoluteExe">Whether to allow an absolute (rather than relative) file path to the executable.</param>
        /// <param name="allowAbsoluteArgs">Whether to allow absolute (rather than relative) file paths as arguments.</param>
        /// <param name="workingDirOverride">The working directory to use.</param>
        public ProcessInvoker(
            WorkingDirectory workingDirectory,
            string executable,
            string[] args,
            BuildObject failureBase,
            BuildObject captureStdout = null,
            string dbgText = null,
            bool allowAbsoluteExe = false,
            bool allowAbsoluteArgs = false,
            string workingDirOverride = null)
        {
            // Catch bad verb authors before they hurt themselves.
            Util.Assert(allowAbsoluteExe || !executable.Contains(":"));  // Hey, this looks like an absolute path! Use .getRelativePath(); it makes your output more stable.
            foreach (string arg in args)
            {
                // Pardon my distasteful heuristic to avoid flagging /flag:value args.
                Util.Assert(allowAbsoluteArgs || arg.Length < 2 || arg[1] != ':');  // Hey, this looks like an absolute path! Use .getRelativePath() to tolerate crossing machine boundaries.
            }

            this.workingDirectory = workingDirectory;
            this.stdout = new StringBuilder();
            this.stderr = new StringBuilder();

            using (Job job = new Job())
            {
                using (Process proc = new Process())
                {
                    if (allowAbsoluteExe)
                    {
                        proc.StartInfo.FileName = executable;
                    }
                    else
                    {
                        // TODO: *All* async verbs need to list their executable (and all the libs it depends upon) as dependencies.
                        proc.StartInfo.FileName = workingDirectory.PathTo(executable);
                    }

                    // TODO Is there a better way to escape the args to avoid problems with spaces?
                    proc.StartInfo.Arguments = string.Join(" ", args);
                    proc.StartInfo.WorkingDirectory = workingDirOverride == null ? workingDirectory.Root : workingDirOverride;
                    proc.StartInfo.RedirectStandardOutput = true;

                    // REVIEW: Maybe we should always capture stdout in a StringBuilder and just write it out to a file afterwards if requested?
                    if (captureStdout != null)
                    {
                        this.tmpStdout = new BuildObject(captureStdout.getRelativePath() + ".tmp");
                        this.stdoutFile = new StreamWriter(workingDirectory.PathTo(this.tmpStdout));
                        proc.OutputDataReceived += new DataReceivedEventHandler(this.StdoutRedirectHandler);
                    }
                    else
                    {
                        // Collect stdout here for diagnostics.
                        proc.OutputDataReceived += new DataReceivedEventHandler(this.StdoutHandler);
                    }

                    proc.StartInfo.RedirectStandardError = true;
                    proc.ErrorDataReceived += new DataReceivedEventHandler(this.StderrHandler);
                    proc.StartInfo.UseShellExecute = false;

                    string commandLine = proc.StartInfo.FileName + " " + proc.StartInfo.Arguments;
                    if (failureBase != null && AlwaysEmitDiagnostics)
                    {
                        // In diagnostic mode, we emit the command line twice, once ahead in case Boogie decides
                        // to run away and never come back.
                        BuildObject failureBatObj = failureBase.makeOutputObject(".bat");
                        workingDirectory.CreateDirectoryFor(failureBatObj);
                        File.WriteAllText(workingDirectory.PathTo(failureBatObj), commandLine);
                    }

                    proc.Start();
                    job.AddProcess(proc);
                    proc.BeginOutputReadLine();
                    proc.BeginErrorReadLine();
                    proc.WaitForExit();

                    this.cpuTime = job.GetCpuTime().TotalSeconds;

                    this.exitCode = proc.ExitCode;
                    if (this.stdoutFile != null)
                    {
                        this.stdoutFile.Close();
                    }

                    if (failureBase != null && AlwaysEmitDiagnostics)
                    {
                        workingDirectory.CreateDirectoryFor(failureBase);
                        File.WriteAllText(workingDirectory.PathTo(failureBase.makeOutputObject(".bat")), commandLine);
                        File.WriteAllText(workingDirectory.PathTo(failureBase.makeOutputObject(".txt")), dbgText);
                        File.WriteAllText(workingDirectory.PathTo(failureBase.makeOutputObject(".stdout")), this.GetStdoutString());
                        File.WriteAllText(workingDirectory.PathTo(failureBase.makeOutputObject(".stderr")), this.GetStderr());
                    }
                }
            }

            // REVIEW: Add Delete, Exists and Move methods to WorkingDirectory class?
            if (this.tmpStdout != null && File.Exists(workingDirectory.PathTo(this.tmpStdout)))
            {
                // REVIEW: Nothing should be here.  Bother with the delete?
                File.Delete(workingDirectory.PathTo(captureStdout));
                File.Move(workingDirectory.PathTo(this.tmpStdout), workingDirectory.PathTo(captureStdout));
                this.tmpStdout = null;
            }
        }

        /// <summary>
        /// Gets the exit code returned by the process.
        /// </summary>
        public int ExitCode
        {
            get { return this.exitCode; }
        }

        /// <summary>
        /// Gets the CPU time used by the process, in seconds.
        /// </summary>
        public double CpuTime
        {
            get { return this.cpuTime; }
        }

        /// <summary>
        /// Gets the process's standard output in the default case.
        /// Does not return the standard output if it is redirected to a file (i.e. if <c>CaptureStdout</c> is non-null).
        /// </summary>
        /// <returns>The process's standard output.</returns>
        public string GetStdout()
        {
            return this.stdout.ToString();
        }

        /// <summary>
        /// Gets the process's standard error output..
        /// </summary>
        /// <returns>The process's standard error output.</returns>
        public string GetStderr()
        {
            return this.stderr.ToString();
        }

        /// <summary>
        /// Gets the process's standard output, regardless of whether it was redirected to a file.
        /// </summary>
        /// <returns>The process's standard output.</returns>
        private string GetStdoutString()
        {
            if (this.tmpStdout != null)
            {
                return File.ReadAllText(this.workingDirectory.PathTo(this.tmpStdout));
            }
            else
            {
                return this.GetStdout();
            }
        }

        /// <summary>
        /// Alternate handler for the OutputDataReceived event.
        /// Stores the data in the previously specified file.
        /// </summary>
        /// <param name="sendingProcess">The parameter is not used.</param>
        /// <param name="dataLine">Contains a line of characters read from the process's standard out.</param>
        private void StdoutRedirectHandler(object sendingProcess, DataReceivedEventArgs dataLine)
        {
            this.stdoutFile.WriteLine(dataLine.Data);
        }

        /// <summary>
        /// Default handler for the OutputDataReceived event.
        /// Stores the data in a local StringBuilder instance.
        /// </summary>
        /// <param name="sendingProcess">The parameter is not used.</param>
        /// <param name="dataLine">Contains a line of characters read from the process's standard out.</param>
        private void StdoutHandler(object sendingProcess, DataReceivedEventArgs dataLine)
        {
            // REVIEW: Can't we use AppendLine here instead?
            this.stdout.Append(dataLine.Data + "\n");
        }

        /// <summary>
        /// Handler for the ErrorDataReceived event.
        /// Stores the data in a local StringBuilder instance.
        /// </summary>
        /// <param name="sendingProcess">The parameter is not used.</param>
        /// <param name="dataLine">Contains a line of characters read from the process's standard error.</param>
        private void StderrHandler(object sendingProcess, DataReceivedEventArgs dataLine)
        {
            // REVIEW: Can't we use AppendLine here instead?
            this.stderr.Append(dataLine.Data + "\n");
        }
    }
}
