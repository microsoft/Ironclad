//--
// <copyright file="SymDiffBaseVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;

    internal abstract class SymDiffBaseVerb : Verb, IProcessInvokeAsyncVerb
    {
        private const int version = 10;
  
        public abstract IEnumerable<BuildObject> getInputFiles();

        public abstract BuildObject getOutputFile();

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;

            List<BuildObject> deps = new List<BuildObject>(this.getInputFiles());
            deps.Add(getSymDiffExecutable());
            deps.AddRange(getSymDiffExecutableDependencies());

            // REVIEW: Probably need to add SymDiffExecutable's dependencies too.
            return deps;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new List<BuildObject>() { this.getOutputFile() };
        }

        public virtual void preprocess(WorkingDirectory workingDirectory) { }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            List<string> args = this.getArgs();

            preprocess(workingDirectory);

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
                getSymDiffExecutable().getRelativePath(),
                args.ToArray(),
                ProcessExitCodeHandling.NonzeroIsFailure,
                getDiagnosticsBase(),
                workingDirOverride: overrideDir,
                returnStandardOut: true);
        }

        public virtual Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {
            return disposition;
        }

        protected static SourcePath getSymDiffExecutable()
        {
            return new SourcePath("tools\\SymDiff\\SymDiff.exe", SourcePath.SourceType.Tools);
        }

        protected static IEnumerable<BuildObject> getSymDiffExecutableDependencies()
        {
            List<BuildObject> exeDepends = new List<BuildObject>();

            exeDepends.Add(new SourcePath("tools\\SymDiff\\Basetypes.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\SymDiff\\Core.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\SymDiff\\CodeContractsExtender.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\SymDiff\\Graph.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\SymDiff\\ParserHelper.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\SymDiff\\Provers.SMTLib.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\SymDiff\\VCGeneration.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\SymDiff\\z3.exe", SourcePath.SourceType.Tools));

            return exeDepends;
        }

        protected abstract List<string> getArgs();

        protected virtual string getWorkingDir()
        {
            return getOutputFile().getDirPath();
        }
    }
}
