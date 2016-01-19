//--
// <copyright file="IronRootDirectory.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.IO;

    /// <summary>
    /// A directory tree in the local filesystem to fetch sources from.
    /// Used to identify and isolate accesses to things under iron root.
    /// </summary>
    internal static class IronRootDirectory
    {
        /// <summary>
        /// Gets the absolute path to the given build object under IronRoot.
        /// </summary>
        /// <param name="obj">A build object.</param>
        /// <returns>The absolute path to the build object.</returns>
        public static string PathTo(BuildObject obj)
        {
            return Path.Combine(BuildEngine.theEngine.getIronRoot(), obj.getRelativePath());
        }

        /// <summary>
        /// Gets the absolute path corresponding to the given relative path under IronRoot.
        /// </summary>
        /// <param name="relativePath">Relative path to convert.</param>
        /// <returns>The absolute path corresponding to the given relative path.</returns>
        public static string PathTo(string relativePath)
        {
            return Path.Combine(BuildEngine.theEngine.getIronRoot(), relativePath);
        }
    }
}
