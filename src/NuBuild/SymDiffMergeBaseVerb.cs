//--
// <copyright file="SymDiffMergeBaseVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;

    internal abstract class SymDiffMergeBaseVerb : Verb, IProcessInvokeAsyncVerb
    {
        private const int version = 3;

        private static NmakeVerb boogieAsmBuildExecutableVerb = new NmakeVerb(new SourcePath("tools\\BoogieAsm\\makefile", SourcePath.SourceType.Tools));

        public abstract BuildObject getOutputFile();

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;

            List<BuildObject> deps = new List<BuildObject>(this.getInputFiles());
            deps.Add(getSymDiffMergeExecutable());

            // REVIEW: Probably need to add SymDiffMergeExecutable's dependencies too.
            return deps;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new[] { boogieAsmBuildExecutableVerb };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new List<BuildObject>() { this.getOutputFile() };
        }

        protected string getWorkingDir() { return getOutputFile().getDirPath(); }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            List<string> args = this.getArgs();

            // We use workingDirOverride flag here to change the path that the
            // process starts in to one that is still in our workingDirectory.
            // So this isn't so bad.  It would be better if NuBuild would only
            // let us supply a relative path here, however.
            string overrideDir = null;
            if (this.getWorkingDir() != null)
            {
                overrideDir = workingDirectory.PathTo(this.getWorkingDir());
            }

            return new ProcessInvokeAsyncWorker(
                workingDirectory,
                this,
                this.getSymDiffMergeExecutable().getRelativePath(),
                args.ToArray(),
                ProcessExitCodeHandling.NonzeroIsFailure,
                getDiagnosticsBase(),
                captureStdout: this.getOutputFile(),
                workingDirOverride:overrideDir);
        }

        public Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {
            return disposition;
        }

        protected abstract IEnumerable<BuildObject> getInputFiles();

        protected abstract List<string> getArgs();
 
        private BuildObject getSymDiffMergeExecutable()
        {
            return new BuildObject(Path.Combine(boogieAsmBuildExecutableVerb.getOutputPath().getRelativePath(), "symdiffmerge.exe"));
        }
   }
}
