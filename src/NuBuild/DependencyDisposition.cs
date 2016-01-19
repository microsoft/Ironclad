//--
// <copyright file="DependencyDisposition.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    public enum DependencyDisposition
    {
        Complete,
        Incomplete,
        Failed      // Something failed upstream
    }

    public static class DependencyDispositionExtensions
    {
        public static DependencyDisposition combine(this DependencyDisposition a, DependencyDisposition b)
        {
            if (a == DependencyDisposition.Failed || b == DependencyDisposition.Failed)
            {
                return DependencyDisposition.Failed;
            }

            if (a == DependencyDisposition.Incomplete || b == DependencyDisposition.Incomplete)
            {
                return DependencyDisposition.Incomplete;
            }

            return DependencyDisposition.Complete;
        }
    }
}
