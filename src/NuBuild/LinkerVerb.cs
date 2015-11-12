//--
// <copyright file="LinkerVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;

    internal class LinkerVerb : Verb, IProcessInvokeAsyncVerb
    {
        public const string UNTRUSTED_EXE_EXTN = ".uexe";

        protected BuildObject outputObject;
        protected BuildObject objFile;

        protected long maxExeSize;
        protected string entryPoint;
        protected int baseAddr;

        private const int version = 4;
        private bool isLoader;
        private MasmVerb masmVerb;
        private AbstractId abstractId;

        public LinkerVerb(MasmVerb masmVerb, bool isLoader)
        {
            this.masmVerb = masmVerb;
            this.isLoader = isLoader;
            this.objFile = masmVerb.getObj();

            this.abstractId = new AbstractId(this.GetType().Name, version + this.getVersion(), this.objFile.ToString(), concrete: isLoader ? "Loader" : "NonLoader");
            this.outputObject = this.objFile.makeOutputObject(this.outputExtension());

            // Default settings for the apps.
            this.maxExeSize = 1 * 1024 * 1024;  // 1 MB.
            this.entryPoint = "?AppEntryPoint";
            this.baseAddr = 0x340000;

            if (this.isLoader)
            {
                // Override the settings above with loader-specific values.
                this.maxExeSize = 58 * 1024;  // 58 KB
                this.entryPoint = "?LoaderEntryPoint";
                this.baseAddr = 0x300000;
            }
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public BuildObject getUntrustedExe()
        {
            return this.outputObject;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            List<BuildObject> basic = new List<BuildObject>() { this.getLinkerExe(), this.objFile };
            basic.AddRange(this.getExtraDependencies());
            return basic;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new List<IVerb>() { this.masmVerb };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new List<BuildObject>() { this.getUntrustedExe() }.Union(this.getExtraOutputs());
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            List<string> args = new List<string>() { "/LARGEADDRESSAWARE", "/driver", "/fixed", "/subsystem:native", "/nodefaultlib" };
            args.Add(this.objFile.getRelativePath());
            args.Add("/out:" + this.outputObject.getRelativePath());
            args.Add("/entry:" + this.entryPoint);
            args.Add("/base:" + this.baseAddr);

            return new ProcessInvokeAsyncWorker(
                workingDirectory,
                this,
                this.getLinkerExe().getRelativePath(),
                args.ToArray(),
                ProcessExitCodeHandling.NonzeroIsFailure,
                this.getDiagnosticsBase());
        }

        public virtual Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {
            if (!(disposition is Failed))
            {
                // Check that the executable isn't too large.
                long exeSize = new FileInfo(workingDirectory.PathTo(this.outputObject)).Length;

                if (exeSize > this.maxExeSize)
                {
                    return new Failed("Executable too big");
                }
            }

            return disposition;
        }

        protected virtual int getVersion()
        {
            // REVIEW: Is this right?  There is a private version field in this object.
            return 0;
        }

        protected virtual string outputExtension()
        {
            return UNTRUSTED_EXE_EXTN;
        }

        protected virtual BuildObject getLinkerExe()
        {
            return new SourcePath("tools\\Assembler\\link-base.exe", SourcePath.SourceType.Tools);
        }

        protected virtual IEnumerable<BuildObject> getExtraDependencies()
        {
            List<BuildObject> extraDepends = new List<BuildObject>();

            extraDepends.Add(new SourcePath("tools\\Assembler\\mspdb80.dll", SourcePath.SourceType.Tools));

            return extraDepends;
        }
        
        protected virtual IEnumerable<BuildObject> getExtraOutputs()
        {
            return new List<BuildObject>();
        }

        protected virtual bool runLinker(BuildObject asmFile, string linkerExecutable, string entryPoint, int baseAddr, long maxExeSize = -1)
        {
            return true;
        }
    }
}
