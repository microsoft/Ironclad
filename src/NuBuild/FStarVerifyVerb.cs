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
        private readonly FStarDepVerb depsVerb;

        private readonly BuildObject outputObj;
        private readonly string label;

        private readonly FStarOptionParser optParser;

        public FStarVerifyVerb(IEnumerable<string> args)
        {
            this.optParser = new FStarOptionParser(args);
            this.signature = MakeArgumentSignature(args);
            this.label = string.Format("FStarVerify {0}", string.Join(" ", args));
            this.abstractId = new AbstractId(this.GetType().Name, Version, this.signature);
            this.outputObj = new BuildObject(string.Format("{0}/{1}.fst.v", BuildEngine.theEngine.getVirtualRoot(), this.signature));
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            // note: order of the returned IEnumerable object doesn't appear to matter.
            var result = new HashSet<BuildObject>(FStarEnvironment.GetStandardDependencies());
            var searchPaths = this.optParser.GetModuleSearchPaths();
            foreach (var filePath in this.optParser.SourceFilePaths)
            {
                var found = NuBuildEnvironment.FindFile(filePath, searchPaths);
                if (found == null)
                {
                    var msg = string.Format("Unable to find file (`{0}`) in module search path (`{1}`).", filePath, string.Join(";", searchPaths.Select(p => p.ToString())));
                    throw new FileNotFoundException(msg);
                }
                result.Add(new SourcePath(found.ToString()));
            }
            if (this.depsVerb == null)
            {
                ddisp = DependencyDisposition.Complete;
                return result;
            }
            var depOut = this.depsVerb.getOutputs();
            result.UnionWith(depOut);

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
            if (this.depsVerb == null)
            {
                return new IVerb[0];
            }
            return new IVerb[] { this.depsVerb };
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
            List<string> arguments = new List<string>();
            if (!this.optParser.ExplicitDeps)
            {
                arguments.Add("--explicit_deps");
            }
            arguments.AddRange(this.optParser.GetAdjustedArgs());
            var exePath = FStarEnvironment.PathToFStarExe.ToString();

            Logger.WriteLine(string.Format("{0} invokes `{1} {2}` from `{3}`", this, exePath, string.Join(" ", arguments), workingDirectory.Prefix));
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
    }
}
