//--
// <copyright file="SymDiffExtractVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;

    internal class SymDiffExtractVerb : SymDiffBaseVerb
    {
        public const string UNROLLED_EXTN = "_u";
        public const string LEFT_FILE = "v1";
        public const string RIGHT_FILE = "v2";

        private const int version = 5;

        private AbstractId abstractId;
        private BoogieAsmVerifyVerb basmVerb;
        private BuildObject basmIn;
        private Mode mode;

        public SymDiffExtractVerb(BoogieAsmVerifyVerb basmVerb, Mode mode)
        {
            this.basmVerb = basmVerb;
            this.basmIn = basmVerb.outputFile();
            this.mode = mode;

            this.abstractId = new AbstractId(this.GetType().Name, version, this.basmIn.ToString(), concrete: mode.ToString());
        }

        public enum Mode
        {
            LEFT, RIGHT
        }

        public override IEnumerable<BuildObject> getInputFiles()
        {
            return new List<BuildObject>() { this.basmIn };
        }

        public string getFileName() {
            switch (mode) {
                 case Mode.LEFT:
                    return LEFT_FILE;
                case Mode.RIGHT:
                    return RIGHT_FILE;
                default:
                    throw new Exception("Unexpected mode for SymDiffExtractVerb");
            }
        }

        private BuildObject getTmpInputFile()
        {
            return new BuildObject(Path.Combine(basmIn.getDirPath(), getFileName() + BoogieVerb.BPL_EXTN));           
        }

        public override BuildObject getOutputFile()
        {
            return new BuildObject(Path.Combine(this.basmIn.getDirPath(), getFileName() + UNROLLED_EXTN + BoogieVerb.BPL_EXTN));
            ////return basmIn.makeOutputObject(extension + BoogieVerb.BPL_EXTN);         
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new List<IVerb>() { this.basmVerb };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new List<BuildObject>() { this.getOutputFile() };
        }
        
        public override void preprocess(WorkingDirectory workingDirectory) {
            base.preprocess(workingDirectory);
            File.Copy(workingDirectory.PathTo(basmIn), workingDirectory.PathTo(getTmpInputFile()), true);
        }

        protected override List<string> getArgs()
        {
            List<string> args = new List<string>();
            args.Add("-extractLoops");
            args.Add(getTmpInputFile().getFileName());
            args.Add(getOutputFile().getFileName());

            return args;
        }
    }
}
