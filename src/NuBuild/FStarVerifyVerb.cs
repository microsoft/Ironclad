//--
// <copyright file="FStarVerifyVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System.Collections.Generic;
    using System.Linq;

    internal class FStarVerifyVerb
        : VerificationResultVerb, IProcessInvokeAsyncVerb
    {
        private const int Version = 2;

        private readonly string signature;
        private readonly AbstractId abstractId;
        private readonly BuildObject outputObj;
        private readonly string label;

        private readonly FStarFindDepsVerb findDepsVerb;
        private IEnumerable<IVerb> dependencyVerbCache; 
        private readonly FStarOptionParser optParser;

        public FStarVerifyVerb(IEnumerable<string> args, AbsoluteFileSystemPath invokedFrom = null)
        {
            // todo: do i need to make this implement IObligationsProducer?

            this.optParser = new FStarOptionParser(args, invokedFrom);
            this.signature = this.optParser.GetSignature();
            this.label = string.Format("FStarVerify {0}", string.Join(" ", args));
            this.abstractId = new AbstractId(this.GetType().Name, Version, this.signature);
            this.outputObj = new BuildObject(string.Format("{0}.fst", this.signature)).makeOutputObject(".fst.v");
            if (this.optParser.ExplicitDeps)
            {
                this.findDepsVerb = null;
            }
            else
            {
                this.findDepsVerb = new FStarFindDepsVerb(args, invokedFrom);
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
            ddisp = DependencyDisposition.Complete;
            if (this.findDepsVerb == null)
            {
                return result;
            }

            var depOut = this.findDepsVerb.getOutputs();
            result.UnionWith(depOut);
            this.findDepsVerb.getDependenciesFound(out ddisp);
            if (ddisp != DependencyDisposition.Complete)
            {
                return result;
            }

            var depVerbs = this.GetDependencyVerbs(out ddisp);
            if (ddisp != DependencyDisposition.Complete)
            {
                return result;
            }
            foreach (var verb in depVerbs)
            {
                result.UnionWith(verb.getOutputs());
            }
            return result;

        }

        public override IEnumerable<IVerb> getVerbs()
        {
            if (this.findDepsVerb != null)
            {
                yield return this.findDepsVerb;
                DependencyDisposition ddisp;
                var deps = this.GetDependencyVerbs(out ddisp);
                if (ddisp == DependencyDisposition.Complete)
                {
                    foreach (var dep in deps)
                    {
                        yield return dep;
                    }
                }
            }
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
            // if the --explicit_deps flag is specified, we invoke F* directly.
            if (this.optParser.ExplicitDeps)
            {
                var arguments = this.GetNormalizedArgs().ToArray();
                var exePath = FStarEnvironment.PathToFStarExe.ToString();

                Logger.WriteLine(string.Format("{0} invokes `{1} {2}` from `{3}`", this, exePath, string.Join(" ", arguments), workingDirectory.Prefix));
                return new ProcessInvokeAsyncWorker(workingDirectory, this, exePath, arguments, ProcessExitCodeHandling.NonzeroIsOkay, this.getDiagnosticsBase(), returnStandardOut: true, returnStandardError: true, allowCloudExecution: false);
            }
            // otherwise, we rely upon dependant verbs to do the work for us.
            return new VerbSyncWorker(workingDirectory, new Fresh());
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
            return this.optParser.GetNormalizedArgs(forceExplicitDeps: true);
        }

        private IEnumerable<IVerb> GetDependencyVerbs(out DependencyDisposition ddisp)
        {
            if (this.dependencyVerbCache == null)
            {
                var findDepsOutput = this.findDepsVerb.getDependenciesFound(out ddisp);
                if (ddisp != DependencyDisposition.Complete)
                {
                    return null;
                }

                var deps = new List<IVerb>();
                foreach (var target in findDepsOutput.ByTarget.Keys)
                {
                    var args = new List<string>();
                    var baseArgs = this.optParser.GetNormalizedArgs(forceExplicitDeps: true, emitSources: false).ToArray();
                    var depArgs = findDepsOutput.ByTarget[target].Select(p => p.ToString()).ToArray();

                    args.AddRange(baseArgs);
                    args.Add("--verify_module");
                    args.Add(target.FileNameWithoutExtension);
                    args.AddRange(depArgs);
                    args.Add(target.ToString());
                    var verb = new FStarVerifyVerb(args);

                    deps.Add(verb);
                }

                ddisp = DependencyDisposition.Complete;
                this.dependencyVerbCache = deps;
                return this.dependencyVerbCache;
            }

            ddisp = DependencyDisposition.Complete;
            return this.dependencyVerbCache;

        } 
    }
}
