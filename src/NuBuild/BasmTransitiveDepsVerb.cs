//--
// <copyright file="BasmTransitiveDepsVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    internal class BasmTransitiveDepsVerb
        : TransitiveDepsVerb
    {
        private IContextGeneratingVerb contextVerb;

        public BasmTransitiveDepsVerb(IContextGeneratingVerb contextVerb, BuildObject input)
            : base(input)
        {
            this.contextVerb = contextVerb;
        }

        protected override TransitiveDepsVerb factory(BuildObject obj)
        {
            return new BasmTransitiveDepsVerb(this.contextVerb, obj);
        }

        protected override void extendDeps(List<BuildObject> deps)
        {
            deps.Add(this.contextVerb.getContextOutput());
        }

        protected override IIncludeFactory getIncludeFactory()
        {
            ContextContents context = (ContextContents)
                BuildEngine.theEngine.Repository.FetchVirtual(this.contextVerb.getContextOutput());
            return new BasmObligationIncludes(context.Context);
        }
    }
}
