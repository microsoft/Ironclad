//--
// <copyright file="MasmVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    internal class MasmVerb : Verb, IProcessInvokeAsyncVerb
    {
        public const string MASM_EXTN = ".asm";
        public const string OBJ_EXTN = ".obj";
        private const int version = 4;

        private IAsmProducer asmVerb;
        private AbstractId abstractId;
        private BuildObject outputObject;
        private BuildObject asmFile;

        public MasmVerb(IAsmProducer asmVerb)
        {
            this.asmVerb = asmVerb;
            this.asmFile = asmVerb.getAsmFile();

            this.abstractId = new AbstractId(this.GetType().Name, version, this.asmFile.ToString());
            this.outputObject = this.asmFile.makeOutputObject(OBJ_EXTN);
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public BuildObject getObj()
        {
            return this.outputObject;
        }

        public BuildObject getLis()
        {
            return this.asmFile.makeOutputObject(".lis");
        }

        ////public BuildObject getMap() { return this.asmFile.makeOutputObject(".map"); }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            return new List<BuildObject>() { this.getMasmExe(), this.asmVerb.getAsmFile() };
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new List<IVerb>() { this.asmVerb };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new List<BuildObject>() {
                this.getObj(),
                this.getLis(),
                //// this.getMap()
            };
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            List<string> args = new List<string>() { "/Cp", "/c", "/Zd", "/Zf", "/Zi" };
            args.Add("/Fo" + this.getObj().getRelativePath());
            args.Add("/Fl" + this.getLis().getRelativePath());
            ////args.Add("/Fm" + getMap().getRelativePath());
            // TODO: "/I$SPEC_INCLUDE_DIR" 
            args.Add(this.asmFile.getRelativePath());

            return new ProcessInvokeAsyncWorker(
                workingDirectory,
                this,
                this.getMasmExe().getRelativePath(),
                args.ToArray(),
                ProcessExitCodeHandling.NonzeroIsFailure,
                this.getDiagnosticsBase());
        }

        public Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {
            return disposition;
        }

        private BuildObject getMasmExe()
        {
            return new SourcePath("tools\\Assembler\\ml.exe", SourcePath.SourceType.Tools);
        }
    }
}
