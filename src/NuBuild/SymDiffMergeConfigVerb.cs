//--
// <copyright file="SymDiffMergeConfigVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;

    internal class SymDiffMergeConfigVerb : SymDiffMergeBaseVerb, IProcessInvokeAsyncVerb
    {
        public const string CONFIG_EXTN = ".config";
        private const int version = 7;

        private AbstractId abstractId;
        private BoogieAsmVerifyVerb basmVerb;
        private BuildObject mutualSummary;
        private SymDiffInferVerb inferVerb;
        private BuildObject inferredConfig;
        private BuildObject output;

        public SymDiffMergeConfigVerb(BoogieAsmVerifyVerb basmVerb, SymDiffInferVerb inferVerb)
        {
            this.basmVerb = basmVerb;
            this.mutualSummary = basmVerb.getMutualSummary();
            this.inferVerb = inferVerb;
            this.inferredConfig = inferVerb.getOutputFile();

            this.abstractId = new AbstractId(this.GetType().Name, version, this.inferredConfig.ToString());  // One should suffice for uniqueness: String.Format("{0},{1}", mutualSummary,inferredConfig));
            this.output = this.basmVerb.outputFile().makeOutputObject(CONFIG_EXTN);
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public override BuildObject getOutputFile()
        {
            return this.output;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return base.getVerbs().Concat(new List<IVerb>() { this.basmVerb, this.inferVerb });
        }

        protected override IEnumerable<BuildObject> getInputFiles()
        {
            return new List<BuildObject>() { this.mutualSummary, this.inferredConfig };
        }

        protected override List<string> getArgs()
        {
            List<string> args = new List<string>();
            args.Add("-config");
            args.Add(this.mutualSummary.getFileName());
            args.Add(this.inferredConfig.getFileName());
            return args;
        }
    }
}
