//--
// <copyright file="VirtualBuildObject.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    /// <summary>
    /// Representation of a virtual BuildObject.
    /// A VirtualBuildObject is never actually stored in the filesystem;
    /// it is only materialized inside the process.  It's used for results
    /// that are easy to compute, but which still need to be established
    /// in dependency order.  Instances: transitive deps, contexts.
    /// </summary>
    internal class VirtualBuildObject
        : BuildObject
    {
        /// <summary>
        /// Initializes a new instance of the VirtualBuildObject class.
        /// </summary>
        /// <param name="inpath">Virtual path name of the object.</param>
        public VirtualBuildObject(string inpath)
            : base(inpath)
        {
            Util.Assert(inpath.StartsWith(BuildEngine.theEngine.getVirtualRoot(), StringComparison.OrdinalIgnoreCase));
        }
    }
}
