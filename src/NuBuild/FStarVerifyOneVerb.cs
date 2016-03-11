//--
// <copyright file="FStarVerifyOneVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;

    internal class FStarVerifyOneVerb : VerificationResultVerb, IProcessInvokeAsyncVerb
    {
        private const int Version = 1;

        private readonly string signature;
        private readonly AbstractId abstractId;
        private readonly BuildObject obligations;
        private readonly string label;

        private readonly FStarOptionParser optParser;
        private readonly bool StrictMode;

        public FStarVerifyOneVerb(IEnumerable<string> args, AbsoluteFileSystemPath invokedFrom = null, bool strict = true)
        {
            this.optParser = new FStarOptionParser(args, invokedFrom);
            if (!this.optParser.ExplicitDeps)
            {
                throw new ArgumentException("FStarVerifyOneVerb requires the `--explicit_deps` argument to be specified.");
            }

            this.signature = this.optParser.GetSignature();
            this.label = string.Format("FStarVerifyOne {0}", string.Join(" ", args));
            this.abstractId = new AbstractId(this.GetType().Name, Version, this.signature);
            this.obligations = new BuildObject(string.Format("{0}.fst", this.signature)).makeOutputObject(".fst.v");
            // strict mode means that all stdlib dependencies are specified in the argument list.
            this.StrictMode = strict;
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
            if (!this.StrictMode)
            {
                // if we're not in "strict" mode, it means we haven't identified all of our standard library dependencies. we must compensate by identifiying the entire standard library as dependencies.
                result.UnionWith(FStarEnvironment.StandardLibrary);
            }
            ddisp = DependencyDisposition.Complete;
            return result;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[0];
        }

        public override BuildObject getOutputFile()
        {
            return this.obligations;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new[] { this.getOutputFile() };
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            var arguments = this.optParser.GetNormalizedArgs().ToArray();
            var exePath = FStarEnvironment.PathToFStarExe.ToString();

            Logger.WriteLine(string.Format("{0} invokes `{1} {2}` from `{3}`", this, exePath, string.Join(" ", arguments), workingDirectory.Prefix));
            return new ProcessInvokeAsyncWorker(workingDirectory, this, exePath, arguments, ProcessExitCodeHandling.NonzeroIsOkay, this.getDiagnosticsBase(), returnStandardOut: true, returnStandardError: true, allowCloudExecution: false);
        }

        public Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {
            Func<string, string> annotateModule =
                s =>
                {
                    if (this.optParser.VerifyModule != null)
                    {
                        return string.Format("(while verifying F* module {0}...)\n{1}", this.optParser.VerifyModule, s);
                    }
                    else
                    {
                        return s;
                    }
                };

            stdout = stdout.Trim();
            if (!string.IsNullOrWhiteSpace(stdout))
            {
                Logger.WriteLine(annotateModule(stdout), new[] { "fstar", "stdout" });
            }
            stderr = stderr.Trim();
            if (!string.IsNullOrWhiteSpace(stderr))
            {
                Logger.WriteLine(annotateModule(stderr), new[] { "fstar", "stderr" });
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
