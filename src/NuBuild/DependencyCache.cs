//--
// <copyright file="DependencyCache.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    internal class DependencyCache
    {
        private Dictionary<IVerb, DependencyResult> theCache;
        private int dbgQueries = 0;
        private int dbgMisses = 0;

        public DependencyCache()
        {
            this.theCache = new Dictionary<IVerb, DependencyResult>();
        }

        public IEnumerable<BuildObject> getDependencies(IVerb verb, out DependencyDisposition ddisp)
        {
            this.dbgQueries += 1;
            DependencyResult result;
            bool present = this.theCache.TryGetValue(verb, out result);
            if (!present)
            {
                this.dbgMisses += 1;
                result = new DependencyResult();
                result.deps = verb.getDependencies(out result.ddisp);
                if (result.ddisp != DependencyDisposition.Incomplete)
                {
                    // Can't cache incomplete results, since they may change upon
                    // later inspection.
                    this.theCache[verb] = result;
                }
            }

            ddisp = result.ddisp;
            return result.deps;
        }

        public void dbgPrintStats()
        {
            Logger.WriteLine(string.Format(
                "DependencyCache queries {0} misses {1}", this.dbgQueries, this.dbgMisses));
        }

        private class DependencyResult
        {
            public IEnumerable<BuildObject> deps;
            public DependencyDisposition ddisp;
        }
    }
}
