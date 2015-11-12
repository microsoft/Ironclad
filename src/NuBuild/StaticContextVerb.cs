//--
// <copyright file="StaticContextVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    // Recipient needs to accept IContextGeneratingVerbs, but we don't need
    // any dependencies to produce this (static) context. So this is a simple,
    // non-dependent verb that just spews a ContextContents.
    internal class StaticContextVerb
        : ContextGeneratingVerb
    {
        private IIncludePathContext _context;

        public StaticContextVerb(IIncludePathContext context, string nickname, PoundDefines poundDefines)
            : base(nickname, poundDefines)
        {
            this._context = context;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            return new BuildObject[] { };
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[] { };
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            ContextContents contents = new ContextContents(this._context);
            BuildEngine.theEngine.Repository.StoreVirtual(this.getContextOutput(), new Fresh(), contents);
            return new VerbSyncWorker(workingDirectory, new Fresh());
        }
    }
}
