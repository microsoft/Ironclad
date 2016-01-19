//--
// <copyright file="BasmObligationIncludes.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;
    using System.Text;
    using System.Threading.Tasks;

    internal class BasmObligationIncludes
        : IIncludeFactory
    {
        private IIncludePathContext includePathSearcher;
        private BeatIncludes directIncludes;

        public BasmObligationIncludes(IIncludePathContext includePathSearcher)
        {
            this.includePathSearcher = includePathSearcher;
            this.directIncludes = new BeatIncludes(includePathSearcher);
        }

        public IEnumerable<BuildObject> getIncludes(BuildObject beatsrc)
        {
            IHasher hasher = BuildEngine.theEngine.getHasher();
            OrderPreservingSet<BuildObject> includes = new OrderPreservingSet<BuildObject>();

            BuildObject ifcFile = hasher.search(this.includePathSearcher, beatsrc.getFileNameWithoutExtension(), ModPart.Ifc);
            BuildObject impFile = hasher.search(this.includePathSearcher, beatsrc.getFileNameWithoutExtension(), ModPart.Imp);

            Util.Assert(ifcFile.Equals(beatsrc) || impFile.Equals(beatsrc));
            includes.AddRange(this.directIncludes.getBasmIncludes(ifcFile));
            includes.AddRange(this.directIncludes.getBasmIncludes(impFile));
            return includes;
        }
    }
}
