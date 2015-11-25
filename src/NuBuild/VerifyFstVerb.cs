//--
// <copyright file="VerifyFstVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Diagnostics;
    using System.Linq;

    using NDepend.Path;

    internal class VerifyFstVerb
        : VerificationResultVerb, IProcessInvokeAsyncVerb
    {
        public const string FStarFileNameExtension = ".fst";
        private const int Version = 1;

        private SourcePath fstSource;
        private AbstractId abstractId;

        private FStarFindDepsVerb depsVerb;

        public VerifyFstVerb(SourcePath fstSource)
        {
            this.fstSource = fstSource;
            this.abstractId = new AbstractId(this.GetType().Name, Version, fstSource.ToString());  
            this.depsVerb = new FStarFindDepsVerb(fstSource);
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            // note: order of the returned IEnumerable object doesn't appear to matter.
            var result = new HashSet<BuildObject> { this.getSource() };
            result.UnionWith(FStarEnvironment.getStandardDependencies());
            result.UnionWith(this.depsVerb.getOutputs());

            var depsFound = this.depsVerb.getDependenciesFound(out ddisp);
            if (ddisp != DependencyDisposition.Complete)
            {
                return result;
            }
            result.UnionWith(depsFound.Value);
            return result;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[] { this.depsVerb }; 
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
            var exePath = FStarEnvironment.PathToFStarExe.ToString();

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

        protected override BuildObject getSource()
        {
            return this.fstSource;
        }
    }
}
