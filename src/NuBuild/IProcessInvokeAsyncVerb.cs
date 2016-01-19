//--
// <copyright file="IProcessInvokeAsyncVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    /// <summary>
    /// Interface that verbs which use ProcessInvokeAsyncWorker as their
    /// VerbWorker must provide (for callbacks from same).
    /// </summary>
    internal interface IProcessInvokeAsyncVerb : IVerb
    {
        /// <summary>
        /// Records the CPU time used by the async worker process.
        /// </summary>
        /// <param name="cpuTimeSeconds">The CPU time used.</param>
        void RecordProcessInvokeCpuTime(double cpuTimeSeconds);

        /// <summary>
        /// Performs any required post-processing and/or cleanup of the
        /// results of the async worker process.
        /// </summary>
        /// <param name="workingDirectory">
        /// The private working directory the verb executed in.
        /// </param>
        /// <param name="cpuTimeSeconds">
        /// CPU time used by async process.
        /// </param>
        /// <param name="stdout">
        /// Standard out from async process (if requested).
        /// </param>
        /// <param name="stderr">
        /// Standard error from async process (if requested).
        /// </param>
        /// <param name="disposition">
        /// The disposition of the async process.
        /// </param>
        /// <returns>
        /// The ultimate disposition of the worker activity.
        /// </returns>
        Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition);
    }
}
