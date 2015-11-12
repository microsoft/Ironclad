//--
// <copyright file="Program.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace CloudExecutionEngineStandalone
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using CloudExecutionWorker;

    /// <summary>
    /// Representation of the Cloud Execution Engine.
    /// </summary>
    internal class Program
    {
        /// <summary>
        /// Run executable requests posted to the requests queue.
        /// </summary>
        /// <param name="args">The parameter is unused.</param>
        public static void Main(string[] args)
        {
            CloudExecutionEngine engine = new CloudExecutionEngine();
            engine.Run();
        }
    }
}
