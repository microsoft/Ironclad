//--
// <copyright file="FStarVerifyVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;
    using System.Runtime.CompilerServices;
    using System.Runtime.Remoting.Metadata.W3cXsd2001;
    using System.Security.Cryptography;
    using System.Text;

    using Microsoft.Data.OData.Query.SemanticAst;

    internal class FStarVerifyVerb
        : VerificationResultVerb, IProcessInvokeAsyncVerb
    {
        private const int Version = 2;

        private readonly string signature;
        private readonly AbstractId abstractId;
        private readonly BuildObject outputObj;
        private readonly string label;

        private readonly FStarFindDepsVerb findDepsVerb;
        private readonly FStarOptionParser optParser;

        public FStarVerifyVerb(IEnumerable<string> args)
        {
            this.optParser = new FStarOptionParser(args);
            this.signature = MakeArgumentSignature(this.GetNormalizedArgs());
            this.label = string.Format("FStarVerify {0}", string.Join(" ", args));
            this.abstractId = new AbstractId(this.GetType().Name, Version, this.signature);
            var vobName = Path.Combine(BuildEngine.theEngine.getVirtualRoot(), string.Format("{0}.fst.v", this.signature));
            this.outputObj = new BuildObject(vobName);
            if (this.optParser.ExplicitDeps)
            {
                this.findDepsVerb = null;
            }
            {
                this.findDepsVerb = new FStarFindDepsVerb(args);
            }
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            // note: order of the returned IEnumerable object doesn't appear to matter.
            var result = new HashSet<BuildObject>(FStarEnvironment.GetStandardDependencies());
            result.UnionWith(this.optParser.FindSourceFiles().Values.Select(p => new SourcePath(p.ToString())));
            if (this.findDepsVerb == null)
            {
                ddisp = DependencyDisposition.Complete;
                return result;
            }
            var depOut = this.findDepsVerb.getOutputs();
            result.UnionWith(depOut);

            var depOutput = this.findDepsVerb.getDependenciesFound(out ddisp);
            if (ddisp != DependencyDisposition.Complete)
            {
                return result;
            }
            var allDeps = depOutput.GetAll().Select(s => new SourcePath(s.ToString()));
            result.UnionWith(allDeps);
            return result;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            if (this.findDepsVerb == null)
            {
                return new IVerb[0];
            }
            return new IVerb[] { this.findDepsVerb };
        }

        public override BuildObject getOutputFile()
        {
            return this.outputObj;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new[] { this.getOutputFile() };
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            var arguments = this.GetNormalizedArgs().ToArray();
            var exePath = FStarEnvironment.PathToFStarExe.ToString();

            Logger.WriteLine(string.Format("{0} invokes `{1} {2}` from `{3}`", this, exePath, string.Join(" ", arguments), workingDirectory.Prefix));
            return new ProcessInvokeAsyncWorker(
                workingDirectory,
                this,
                exePath,
                arguments,
                ProcessExitCodeHandling.NonzeroIsOkay,
                getDiagnosticsBase(),
                returnStandardOut: true,
                returnStandardError: true,
                allowCloudExecution: true);
        }

        public Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {
            if (!string.IsNullOrWhiteSpace(stdout))
            {
                Logger.WriteLine(stdout, new[] { "fstar", "stdout" });
            }
            if (!string.IsNullOrWhiteSpace(stderr))
            {
                Logger.WriteLine(stderr, new[] { "fstar", "stderr" });
            }

            VerificationResult vr = new VerificationResult(
                this.label,
                cpuTimeSeconds,
                stdout,
                stderr,
                new VerificationResultFStarParser());
            vr.addBasicPresentation();
            vr.toXmlFile(workingDirectory.PathTo(this.getOutputFile()));
            this.setWasRejectableFailure(!vr.pass);
            return disposition;
        }

        private IEnumerable<string> GetNormalizedArgs()
        {
            if (!this.optParser.ExplicitDeps)
            {
                yield return "--explicit_deps";
            }
            foreach (var arg in this.optParser.GetNormalizedArgs())
            {
                yield return arg;
            }
        } 
    }
}
