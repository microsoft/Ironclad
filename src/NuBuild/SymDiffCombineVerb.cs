//--
// <copyright file="SymDiffCombineVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;

    internal class SymDiffCombineVerb : SymDiffBaseVerb, IProcessInvokeAsyncVerb
    {
        public const string MERGED_FILE_NAME = "mergedProgSingle.bpl";

        private const int version = 3;

        private AbstractId abstractId;
        private SymDiffExtractVerb left;
        private SymDiffExtractVerb right;
        private SymDiffMergeConfigVerb merger;

        private BuildObject outputFile;

        public SymDiffCombineVerb(SymDiffExtractVerb left, SymDiffExtractVerb right, SymDiffMergeConfigVerb merger)
        {
            this.left = left;
            this.right = right;
            this.merger = merger;

            // Naming one of the files should be sufficient to uniquely identify the combiner.
            this.abstractId = new AbstractId(this.GetType().Name, version, left.getOutputFile().ToString());
            ////abstractId = String.Format("{0}(#{1},{2},{3},{4})",
            ////    this.GetType().Name,
            ////    version,
            ////    left.getOutputFile(),
            ////    right.getOutputFile(),
            ////    merger.getOutputFile());
            this.outputFile = this.mkOutputFile();
        }

        public override IEnumerable<BuildObject> getInputFiles()
        {
            return new List<BuildObject>() { this.left.getOutputFile(), this.right.getOutputFile(), this.merger.getOutputFile() };
        }

        public override BuildObject getOutputFile()
        {
            return this.outputFile;
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new List<IVerb>() { this.left, this.right, this.merger };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new List<BuildObject>() { this.getOutputFile() };
        }
        

        protected override List<string> getArgs()
        {
            List<string> args = new List<string>();
            args.Add("-allInOne");
            args.Add(this.left.getOutputFile().getFileName());
            args.Add(this.right.getOutputFile().getFileName());
            args.Add(this.merger.getOutputFile().getFileName());
            ////args.Add(left.getOutputFile().getRelativePath());
            ////args.Add(right.getOutputFile().getRelativePath());
            ////args.Add(merger.getOutputFile().getRelativePath());

            List<string> extra_args = new List<string>() { "-asserts", "-freeContracts", "-usemutual", "-sound", "-dontUseHoudiniForMS", "-checkMutualPrecondNonTerminating" };
            args.AddRange(extra_args);

            return args;
        }

        private BuildObject mkOutputFile()
        {
            // SymDiff always uses the same file name in the working directory.
            return new BuildObject(Path.Combine(this.left.getOutputFile().getDirPath(), MERGED_FILE_NAME));
        }
    }
}
