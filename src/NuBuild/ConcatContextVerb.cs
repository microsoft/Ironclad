//--
// <copyright file="ConcatContextVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;

    internal class ConcatContextVerb
        : ContextGeneratingVerb
    {
        private List<IContextGeneratingVerb> parents;

        public ConcatContextVerb(IEnumerable<IContextGeneratingVerb> parents, PoundDefines poundDefines)
            : base("Cat(" + string.Join(",", parents) + ")", poundDefines)
        {
            this.parents = new List<IContextGeneratingVerb>(parents);
        }

        public ConcatContextVerb(IContextGeneratingVerb parentA, IContextGeneratingVerb parentB, PoundDefines poundDefines)
            : this(new IContextGeneratingVerb[] { parentA, parentB }, poundDefines)
        {
        }

        public ConcatContextVerb(IContextGeneratingVerb parentA, IContextGeneratingVerb parentB, IContextGeneratingVerb parentC, PoundDefines poundDefines)
            : this(new IContextGeneratingVerb[] { parentA, parentB, parentC }, poundDefines)
        {
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            return this.parents.Select(parent => parent.getContextOutput());
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return this.parents;
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            IEnumerable<IIncludePathContext> contexts = this.parents.Select(parent =>
                ((ContextContents)BuildEngine.theEngine.Repository.FetchVirtual(parent.getContextOutput())).Context);
            ConcatContext context = new ConcatContext(contexts);
            ContextContents contents = new ContextContents(context);
            BuildEngine.theEngine.Repository.StoreVirtual(this.getContextOutput(), new Fresh(), contents);
            return new VerbSyncWorker(workingDirectory, new Fresh());
        }
    }
}
