//--
// <copyright file="IVerbWorker.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    /// <summary>
    /// Enumeration of the verb worker types: synchronous and asynchronous.
    /// </summary>
    /// <remarks>
    /// REVIEW: Couldn't this just be a boolean?
    /// </remarks>
    internal enum VerbWorkerType
    {
        /// <summary>
        /// The worker runs synchronously.
        /// </summary>
        Sync,

        /// <summary>
        /// The worker runs asynchronously.
        /// </summary>
        Async
    }

    /// <summary>
    /// Enumeration of the ways to treat process exit codes.
    /// </summary>
    /// <remarks>
    /// REVIEW: Couldn't this just be a boolean?
    /// </remarks>
    internal enum ProcessExitCodeHandling
    {
        /// <summary>
        /// Treat non-zero return codes as the process reporting a failure.
        /// </summary>
        NonzeroIsFailure,

        /// <summary>
        /// Ignore non-zero return codes from the process.
        /// </summary>
        NonzeroIsOkay
    }

    /// <summary>
    /// Definition of the interface to Verb workers.
    /// </summary>
    /// <remarks>
    /// The scheduler's VerbRunner component uses this interface to
    /// run verbs (both synchronous and asynchronous verbs).
    /// </remarks>
    internal interface IVerbWorker
    {
        /// <summary>
        /// Indicates whether this work needs to be scheduled asynchronously.
        /// If it returns Sync, the runAsync method will not be called.
        /// </summary>
        /// <returns>Sync for synchronous verbs, Async otherwise.</returns>
        VerbWorkerType IsSync();

        /// <summary>
        /// Gets the private working directory this verb executes in.
        /// </summary>
        /// <returns>The directory this verb executes in.</returns>
        WorkingDirectory GetWorkingDirectory();

        /// <summary>
        /// Performs the slow, asynchronous work.
        /// </summary>
        /// <remarks>
        /// Does not run on the main thread, so should not access caches
        /// (or do anything else that expects to be synchronous).
        /// </remarks>
        void RunAsync();

        /// <summary>
        /// Performs the completion work for Async workers, and is called
        /// after the runAsync method returns.  For Sync workers, it performs
        /// all the work not done by the getWorker call.
        /// </summary>
        /// <remarks>
        /// This method runs synchronously on the main thread.  REVIEW: Not true
        /// for Async workers!  It runs under lock, but on separate thread.
        /// It can tidy up the state after async work, and store results
        /// in the Repository.
        /// This method must not return the Stale Disposition; once completed
        /// a verb is either Fresh or Failed.
        /// </remarks>
        /// <returns>The disposition of this verb's worker's work.</returns>
        Disposition Complete();
    }
}
