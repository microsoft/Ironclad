//--
// <copyright file="IProcessInvoker.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    /// <summary>
    /// Definition of the interface to local and cloud process invokers.
    /// </summary>
    internal interface IProcessInvoker
    {
        /// <summary>
        /// Gets the exit code returned by the process.
        /// </summary>
        int ExitCode { get; }

        /// <summary>
        /// Gets the CPU time used by the process, in seconds.
        /// </summary>
        double CpuTime { get; }

        /// <summary>
        /// Gets the process's standard output in the default case.
        /// Does not return the standard output if it is redirected to a file (i.e. if <c>CaptureStdout</c> is non-null).
        /// </summary>
        /// <returns>The process's standard output.</returns>
        string GetStdout();

        /// <summary>
        /// Gets the process's standard error output.
        /// </summary>
        /// <returns>The process's standard error output.</returns>
        string GetStderr();
    }
}
