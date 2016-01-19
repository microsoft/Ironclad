//--
// <copyright file="SymDiffMergeVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;

    internal class SymDiffMergeVerb : SymDiffMergeBaseVerb, IProcessInvokeAsyncVerb
    {
        public const string MERGED_EXTN = ".merge";
        private const int version = 8;

        private AbstractId abstractId;
        private BoogieAsmVerifyVerb basmVerb;
        private BuildObject mutualSummary;
        private SymDiffCombineVerb combiner;
        private BuildObject output;

        public SymDiffMergeVerb(BoogieAsmVerifyVerb basmVerb, SymDiffCombineVerb combiner)
        {
            this.basmVerb = basmVerb;
            this.mutualSummary = basmVerb.getMutualSummary();
            this.combiner = combiner;

            this.abstractId = new AbstractId(this.GetType().Name, version, this.combiner.getOutputFile().ToString()); // String.Format("{0},{1}", One should suffice for uniqueness: mutualSummary, combiner.getOutputFile()));
            this.output = this.basmVerb.outputFile().makeOutputObject(MERGED_EXTN + BoogieVerb.BPL_EXTN);
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
            return base.getVerbs().Concat(new List<IVerb>() { this.basmVerb, this.combiner });
        }

        protected override IEnumerable<BuildObject> getInputFiles()
        {
            return new List<BuildObject>() { this.mutualSummary, this.combiner.getOutputFile() };
        }

        protected override List<string> getArgs()
        {
            List<string> args = new List<string>();
            args.Add("-merge");
            args.Add(this.mutualSummary.getFileName());
            args.Add(this.combiner.getOutputFile().getFileName());
            return args;
        }
    }
}
