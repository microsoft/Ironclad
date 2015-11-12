//--
// <copyright file="VerbSyncWorker.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    /// <summary>
    /// Representation of a synchronous verb worker.
    /// </summary>
    internal class VerbSyncWorker : IVerbWorker
    {
        /// <summary>
        /// The private working directory for this worker to work in.
        /// </summary>
        private WorkingDirectory workingDirectory;

        /// <summary>
        /// The disposition of this activity.
        /// </summary>
        private Disposition result;

        /// <summary>
        /// Initializes a new instance of the VerbSyncWorker class.
        /// </summary>
        /// <param name="workingDirectory">
        /// The private working directory for this worker to work in.
        /// </param>
        /// <param name="result">The Disposition to return on complete.</param>
        public VerbSyncWorker(WorkingDirectory workingDirectory, Disposition result)
        {
            this.workingDirectory = workingDirectory;
            this.result = result;
        }

        /// <summary>
        /// Indicates whether this work needs to be scheduled asynchronously.
        /// Since this is the synchronous implementation, always returns Sync.
        /// </summary>
        /// <returns>Always returns Sync.</returns>
        public virtual VerbWorkerType IsSync()
        {
            return VerbWorkerType.Sync;
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
        /// Performs the asynchronous work for this worker, which for a
        /// synchronous worker like this one, should not exist.  Therefore,
        /// this implementation just asserts.
        /// </summary>
        /// <remarks>
        /// Shouldn't ever be called, since our IsSync returns Sync.
        /// </remarks>
        public void RunAsync()
        { 
            Util.Assert(false);
        }

        /// <summary>
        /// Performs the work of this synchronous worker (or whatever isn't
        /// done in the constructor at least).
        /// Returns the ultimate disposition of the activity.
        /// </summary>
        /// <remarks>
        /// Thou shalt not return Stale.
        /// </remarks>
        /// <returns>The disposition of this worker's work.</returns>
        public virtual Disposition Complete()
        {
            return this.result;
        }
    }
}
