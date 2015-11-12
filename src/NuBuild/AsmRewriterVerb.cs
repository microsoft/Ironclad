//--
// <copyright file="AsmRewriterVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;

    internal class AsmRewriterVerb : Verb, IProcessInvokeAsyncVerb, IAsmProducer
    {
        public const string WASM_EXTN = ".wasm";
        private const int version = 1;

        private BoogieAsmLinkVerb asmVerb;
        private AbstractId abstractId;
        private BuildObject asmFileOut;
        private BuildObject asmFileIn;
        private BuildObject pythonScript;

        public AsmRewriterVerb(BoogieAsmLinkVerb asmVerb)
        {
            this.asmVerb = asmVerb;
            this.asmFileIn = asmVerb.getAsmFile();
            this.asmFileOut = this.asmFileIn.makeOutputObject(WASM_EXTN);

            this.abstractId = new AbstractId(this.GetType().Name, version, this.asmFileOut.ToString());
            this.pythonScript = new SourcePath("tools\\scripts\\build-standalone-asm.py", SourcePath.SourceType.Tools);
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public BuildObject getAsmFile()
        {
            return this.asmFileOut;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            return new List<BuildObject>() { this.asmFileIn, this.pythonScript };
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new List<IVerb>() { this.asmVerb };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new List<BuildObject>() { this.getAsmFile() };
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            List<string> args = new List<string>() { this.pythonScript.getRelativePath(), this.asmFileIn.getRelativePath() };
            string python_exe = @"C:\Python27\pythonw.exe";

            if (!File.Exists(python_exe))
            {
                throw new FileNotFoundException("Missing python executable: " + python_exe + ".  Try installing from: https://www.python.org/");
            }

            return new ProcessInvokeAsyncWorker(
                workingDirectory,
                this,
                python_exe,
                args.ToArray(),
                ProcessExitCodeHandling.NonzeroIsFailure,
                getDiagnosticsBase(),
                allowAbsoluteExe: true,
                captureStdout: this.asmFileOut);
        }

        public Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {
            return disposition;
        }
    }
}
