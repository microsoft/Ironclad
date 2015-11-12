//--
// <copyright file="SymDiffInferVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;

    internal class SymDiffInferVerb : SymDiffBaseVerb, IProcessInvokeAsyncVerb
    {
        public const string CONFIG = ".partial_config";

        private const int version = 6;

        private AbstractId abstractId;
        private SymDiffExtractVerb left;
        private SymDiffExtractVerb right;

        public SymDiffInferVerb(SymDiffExtractVerb left, SymDiffExtractVerb right)
        {
            this.left = left;
            this.right = right;

            this.abstractId = new AbstractId(this.GetType().Name, version, left.getOutputFile().ToString().ToString());      // Left should suffice to uniquely ID.
        }

        public override IEnumerable<BuildObject> getInputFiles()
        {
            return new List<BuildObject>() { this.left.getOutputFile(), this.right.getOutputFile() };
        }

        public override BuildObject getOutputFile()
        {
            // Choice of left/right doesn't matter here, since we're dropping the extension.
            return this.left.getOutputFile().makeOutputObject(CONFIG);
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new List<IVerb>() { this.left, this.right };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new List<BuildObject>() { this.getOutputFile() };
        }

        public override Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {
            if (!(disposition is Failed))
            {
                File.WriteAllText(workingDirectory.PathTo(this.getOutputFile()), stdout);
            }

            return disposition;
        }

        protected override List<string> getArgs()
        {
            List<string> args = new List<string>();
            args.Add("-inferConfig");
            args.Add(this.left.getOutputFile().getFileName());
            args.Add(this.right.getOutputFile().getFileName());

            return args;
        }
    }
}
