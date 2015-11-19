//--
// <copyright file="VerifyFstVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    using NDepend.Path;

    internal class VerifyFstVerb
        : VerificationResultVerb, IProcessInvokeAsyncVerb
    {
        public const string FStarFileNameExtension = ".fst";
        private const int Version = 1;

        private SourcePath fstSource;
        private AbstractId abstractId;

        public VerifyFstVerb(SourcePath fstSource)
        {
            this.fstSource = fstSource;
            this.abstractId = new AbstractId(this.GetType().Name, Version, fstSource.ToString());                
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            var result = new HashSet<BuildObject>();
            ddisp = DependencyDisposition.Complete;

            result.UnionWith(this.getDependencies(fstSource));
            result.Add(this.getSource());
            return result;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[0];    // All inputs are sources.
        }

        public override BuildObject getOutputFile()
        {
            return this.fstSource.makeOutputObject(".fst.v");
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new[] { this.getOutputFile() };
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            List<string> arguments = new List<string>();
            arguments.Add("--auto_deps");
            arguments.Add(this.fstSource.getRelativePath());
            var exePath = FStarEnvironment.PathToFStarExe.getRelativePath();

            Logger.WriteLine(string.Format("[NuBuild] cmd: {0} {1}", exePath, string.Join(" ", arguments)));
            return new ProcessInvokeAsyncWorker(
                workingDirectory,
                this,
                exePath,
                arguments.ToArray(),
                ProcessExitCodeHandling.NonzeroIsOkay,
                getDiagnosticsBase(),
                returnStandardOut: true,
                returnStandardError: true,
                allowCloudExecution: true);
        }

        public Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {
            VerificationResult vr = new VerificationResult(
                this.fstSource.getRelativePath(),
                cpuTimeSeconds,
                stdout,
                stderr,
                new VerificationResultFStarParser());
            vr.addBasicPresentation();
            vr.toXmlFile(workingDirectory.PathTo(this.getOutputFile()));
            this.setWasRejectableFailure(!vr.pass);
            return disposition;
        }

        public IEnumerable<BuildObject> getDirectIncludes()
        {
            // By the time this method is called by VerbToposorter,
            // this verb is scheduled for execution, and hence its deps
            // are complete. So all of these lookups should succeed.
            // (wait, does that follow?)
            //return this.getTransitiveDepsVerb().getShallowIncludes();
            return new BuildObject[0];
        }

        protected override BuildObject getSource()
        {
            return this.fstSource;
        } 
       
        private IList<BuildObject> getDependencies(SourcePath fstSource)
        {
            // todo: this is a stopgap until proper dependency resolution is implemented.
            var result = FStarEnvironment.getTools();
            var absFilePaths = findDependencies(fstSource);
            foreach (var absPath in absFilePaths)
            {
                var ob = new SourcePath(absPath.ToString(), SourcePath.SourceType.Src);
                result.Add(ob);
            }
            return result;
        }
        private IList<IAbsoluteFilePath> findDependencies(SourcePath fstSource)
        {
            // todo: this is a stopgap until proper dependency resolution is implemented. contrary to what i repviously believed, i will need to implement a dependency scanning class and generate new targets for any .fs(t?)i files i encounter.
            return new List<IAbsoluteFilePath> { fstSource.toAbsoluteFilePath() };
        }
    }
}
