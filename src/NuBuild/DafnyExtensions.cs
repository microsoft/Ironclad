//--
// <copyright file="DafnyExtensions.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;

    internal class DafnyExtensions
    {
        public static HashSet<BuildObject> getForestDependencies(IEnumerable<BuildObject> roots, out DependencyDisposition ddisp)
        {
            HashSet<BuildObject> result = new HashSet<BuildObject>();
            ddisp = DependencyDisposition.Complete;
            foreach (BuildObject dfysource in roots)
            {
                TransitiveDepsVerb depsVerb = new DafnyTransitiveDepsVerb(dfysource);
                DependencyDisposition localDDisp;
                result.UnionWith(depsVerb.getAvailableDeps(out localDDisp));
                ddisp = ddisp.combine(localDDisp);
                result.Add(dfysource);  // TransitiveDeps *exclude* the root, so we need to add that in, too.
            }

            return result;
        }

        public static IEnumerable<IVerb> getForestVerbs(IEnumerable<BuildObject> roots)
        {
            return roots.Select(root => new DafnyTransitiveDepsVerb(root));
        }
    }
}
