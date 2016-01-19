//--
// <copyright file="WorkerRole.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace CloudExecutionWorker
{
    using System;
    using System.Diagnostics;
    using System.Net;
    using Microsoft.WindowsAzure;
    using Microsoft.WindowsAzure.Diagnostics;
    using Microsoft.WindowsAzure.ServiceRuntime;

    /// <summary>
    /// Our worker role.
    /// This is what Azure knows how to interact with.
    /// </summary>
    /// <remarks>
    /// For information on handling configuration changes
    /// <see cref="http://go.microsoft.com/fwlink/?LinkId=166357"/>.
    /// </remarks>
    public class WorkerRole : RoleEntryPoint
    {
        /// <summary>
        /// Our CloudExecutionEngine that does the real work.
        /// </summary>
        private CloudExecutionEngine engine;

        /// <summary>
        /// Azure calls this method to do the main work.
        /// If this method returns, Azure will recycle this role instance.
        /// </summary>
        public override void Run()
        {
            Trace.TraceInformation("CloudExecutionWorker entry point called");

            this.engine = new CloudExecutionEngine();

            // TODO: Multi-thread this.
            this.engine.Run();
        }

        /// <summary>
        /// Called when this role instance is brought online by Azure.
        /// </summary>
        /// <returns>
        /// Whether Azure should proceed with calling our Run method.
        /// </returns>
        public override bool OnStart()
        {
            // Set the maximum number of concurrent connections.
            //// ServicePointManager.DefaultConnectionLimit = 12;

            return base.OnStart();
        }

        /// <summary>
        /// Called after this role instance has been taken offline by Azure
        /// but before the process exits.
        /// </summary>
        public override void OnStop()
        {
            this.engine.Stop();

            base.OnStop();
        }
    }
}
