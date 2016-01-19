//--
// <copyright file="CloudExecutionWaiter.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Threading;

    /// <summary>
    /// Represents a thread waiting for a particular cloud execution report.
    /// </summary>
    internal class CloudExecutionWaiter
    {
        /// <summary>
        /// Event that is signalled when a new report is ready.
        /// </summary>
        private AutoResetEvent reportIsReady;

        /// <summary>
        /// Execution report that just arrived.
        /// </summary>
        private CloudExecutionReport executionReport;

        /// <summary>
        /// Count of other waiters.
        /// </summary>
        private int otherWaitersCount;

        /// <summary>
        /// Initializes a new instance of the CloudExecutionWaiter class.
        /// </summary>
        public CloudExecutionWaiter()
        {
            this.reportIsReady = new AutoResetEvent(false);
        }

        /// <summary>
        /// Wait for an execution report to arrive.
        /// </summary>
        /// <param name="numberOfOtherWaiters">Count of other report waiters.</param>
        /// <returns>An execution report.</returns>
        public CloudExecutionReport WaitForReport(out int numberOfOtherWaiters)
        {
            this.reportIsReady.WaitOne();

            numberOfOtherWaiters = this.otherWaitersCount;
            return this.executionReport;
        }

        /// <summary>
        /// Give an execution report to this waiter.
        /// </summary>
        /// <param name="executionReport">The execution report to give.</param>
        /// <param name="numberOfOtherWaiters">Count of other report waiters.</param>
        public void GiveReportToWaiter(CloudExecutionReport executionReport, int numberOfOtherWaiters)
        {
            this.executionReport = executionReport;
            this.otherWaitersCount = numberOfOtherWaiters;
            this.reportIsReady.Set();
        }
    }
}
