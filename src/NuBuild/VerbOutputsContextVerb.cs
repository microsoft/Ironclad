//--
// <copyright file="VerbOutputsContextVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;

    /// <summary>
    /// This verb waits for a parent verb to complete, then emits
    /// a ContextContents that searches the parent verb's results.
    /// </summary>
    internal class VerbOutputsContextVerb
        : ContextGeneratingVerb
    {
        private IVerb parent;
        private bool assertSuspiciousDafnyImpls;

        public VerbOutputsContextVerb(IVerb parent, bool assertSuspiciousDafnyImpls)
            : base(parent.getAbstractIdentifier().ToString(), null)
        {
            this.parent = parent;
            this.assertSuspiciousDafnyImpls = assertSuspiciousDafnyImpls;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;

            // I really don't care how many outputs the parent has; any one will
            // link me to the parent.
            IEnumerable<BuildObject> result = this.parent.getOutputs();
            Util.Assert(result.Count() > 0);
            return result;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[] { this.parent };
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            VerbOutputsContext context = new VerbOutputsContext(this.parent, this.assertSuspiciousDafnyImpls);
            ContextContents contents = new ContextContents(context);
            BuildEngine.theEngine.Repository.StoreVirtual(this.getContextOutput(), new Fresh(), contents);
            return new VerbSyncWorker(workingDirectory, new Fresh());
        }
    }
}
