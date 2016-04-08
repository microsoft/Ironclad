//--
// <copyright file="FStarVerifyTreeVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;
    using System.Net.Configuration;

    internal class FStarVerifyTreeVerb : Verb, IObligationsProducer
    {
        private const int Version = 3;

        private readonly string signature;
        private readonly AbstractId abstractId;
        private readonly BuildObject obligations;

        private readonly FStarFindDepsVerb findDepsVerb;
        private IEnumerable<IVerb> dependencyVerbCache; 
        private readonly FStarOptionParser optParser;
        private readonly bool StrictMode;

        public FStarVerifyTreeVerb(IEnumerable<string> args, AbsoluteFileSystemPath invokedFrom = null, bool strict = true)
        {
            this.optParser = new FStarOptionParser(args, invokedFrom);
            this.signature = this.optParser.GetSignature();
            this.abstractId = new AbstractId(this.GetType().Name, Version, this.signature);
            this.obligations = new BuildObject(string.Format("{0}.fst", this.signature)).makeOutputObject(".tree.txt");
            if (this.optParser.ExplicitDeps)
            {
                this.findDepsVerb = null;
            }
            else
            {
                this.findDepsVerb = new FStarFindDepsVerb(args, invokedFrom);
            }
            this.StrictMode = strict;

            this.LogReproductionInstructions();
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            // note: order of the returned IEnumerable object doesn't appear to matter.
            var result = new HashSet<BuildObject>(FStarEnvironment.GetStandardDependencies(this.optParser.Universes));
            result.UnionWith(this.optParser.FindSourceFiles().Values.Select(p => new SourcePath(p.ToString())));
            ddisp = DependencyDisposition.Complete;
            if (this.findDepsVerb != null)
            {
                var depOut = this.findDepsVerb.getOutputs();
                result.UnionWith(depOut);
                this.findDepsVerb.getDependenciesFound(out ddisp);
                if (ddisp != DependencyDisposition.Complete)
                {
                    return result;
                }
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
            }

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
        public BuildObject getObligationSet()
        {
            return this.obligations;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new[] { this.getObligationSet() };
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            IEnumerable<BuildObject> verificationResults = 
                this.getVerbs()
                .Where(v => v is VerificationResultVerb)
                .Select(v => ((VerificationResultVerb)v).getOutputFile());
            VerificationObligationList vol = new VerificationObligationList(verificationResults);
            vol.store(workingDirectory, this.obligations);
            return new VerbSyncWorker(workingDirectory, new Fresh());
        }

        private IEnumerable<IVerb> GetDependencyVerbs(out DependencyDisposition ddisp)
        {
            if (this.dependencyVerbCache == null)
            {
                var deps = new List<IVerb>();

                if (this.findDepsVerb == null)
                {
                    // if we don't need to search for dependencies, we only have one obligation.
                    var verb = new FStarVerifyOneVerb(this.optParser.Args, this.optParser.InvocationPath, this.StrictMode);
                    deps.Add(verb);
                }
                else
                {
                    // otherwise, out obligations will depend upon the results of the findDepsVerb.
                    var findDepsOutput = this.findDepsVerb.getDependenciesFound(out ddisp);
                    if (ddisp != DependencyDisposition.Complete)
                    {
                        return null;
                    }

                    foreach (var target in findDepsOutput.ByTarget.Keys)
                    {
                        var moduleName = target.FileNameWithoutExtension;
                        if (!this.optParser.ShouldVerifyModule(moduleName))
                        {
                            var msg = string.Format("Skipping verification of module {0} because verification was excluded via --verify-module options.", moduleName);
                            Logger.WriteLine(msg);
                            continue;
                        }

                        var args = new List<string>();
                        var baseArgs = this.optParser.GetNormalizedArgs(forceExplicitDeps: true, emitSources: false).ToArray();
                        var depArgs = findDepsOutput.ByTarget[target].Select(p => p.ToString()).ToArray();

                        args.AddRange(baseArgs);
                        args.Add("--verify_module");
                        args.Add(moduleName);
                        args.AddRange(depArgs);
                        args.Add(target.ToString());
                        var verb = new FStarVerifyOneVerb(args);

                        deps.Add(verb);
                    }
                }

                this.dependencyVerbCache = deps;
            }

            ddisp = DependencyDisposition.Complete;
            return this.dependencyVerbCache;

        }

        private void LogReproductionInstructions()
        {
            var nuBuildExePath = RelativeFileSystemPath.Parse(String.Format("./{0}/bin/NuBuild.exe", NuBuildEnvironment.DotNuBuild));
            var fstarExePath = FileSystemPath.Join(NuBuildEnvironment.RootDirectoryPath, FStarEnvironment.PathToFStarExe);
            var normalizedArgs = this.optParser.GetNormalizedArgs();
            var msg = String.Format("{0} You can reproduce this verb's behavior by invoking the command `{1} FStarVerifyTree {2}` from `{3}`; this invocation of the FStarVerifyTree verb intends to emulate execution of `{4} {5}` from `{6}`.", this, nuBuildExePath, String.Join(" ", normalizedArgs), NuBuildEnvironment.RootDirectoryPath, fstarExePath, String.Join(" ", this.optParser.Args), this.optParser.InvocationPath);
            Logger.WriteLine(msg, new [] { "info", "tip" });
        }
    }
}
