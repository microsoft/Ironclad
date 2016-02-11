//--
// <copyright file="FStarFindDepsVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;

    internal class FStarFindDepsVerb: Verb, IProcessInvokeAsyncVerb
    {
        private const string DepsObjExtension = ".fstardep.vob";
        private const int Version = 2;

        private readonly IEnumerable<string> args;
        private readonly string signature;
        private readonly AbstractId abstractId;
        private BuildObject outputObj;

        private readonly FStarOptionParser optParser;
        
        public FStarFindDepsVerb(IEnumerable<string> args)
        {
            this.args = args;
            this.optParser = new FStarOptionParser(args);
            this.signature = MakeArgumentSignature(this.optParser.GetNormalizedArgs());
            this.abstractId = new AbstractId(this.GetType().Name, Version, this.signature);

            var vobName = Path.Combine(BuildEngine.theEngine.getVirtualRoot(), this.signature + DepsObjExtension);
            this.outputObj = new VirtualBuildObject(vobName);
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            var result = new HashSet<BuildObject>(FStarEnvironment.GetStandardDependencies());
            result.UnionWith(this.optParser.FindSourceFiles().Values.Select(p => new SourcePath(p.ToString())));
            return result;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[0];
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new[] { this.outputObj };
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            var arguments = this.GetNormalizedArgs().ToArray();
            var exePath = FStarEnvironment.PathToFStarExe.ToString();

            Logger.WriteLine(string.Format("{0} invokes `{1} {2}`", this, exePath, string.Join(" ", arguments)));
            return new ProcessInvokeAsyncWorker(
                workingDirectory,
                this,
                exePath,
                arguments.ToArray(),
                // todo: either fstar.exe doesn't return non-zero error codes or NuBuild's handling of such codes is broken.
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
                Logger.WriteLine(stdout, new[] { "fstar", "stdout", "*quiet" });
            }
            if (!string.IsNullOrWhiteSpace(stderr))
            {
                Logger.WriteLine(stderr, new[] { "fstar", "stderr" });
            }

            FStarDepOutput contents;
            try
            {
                contents = new FStarDepOutput(stdout, this.optParser, workingDirectory);
            }
            catch (Exception e)
            {
                var msg = string.Format("failed to process output of `{0} --dep make` (unhandled {1}). Details follow:\n{2}", FStarEnvironment.PathToFStarExe, e.GetType().Name, e.Message);
                Logger.WriteLine(msg, new []{"error", "fstar"});
                return new Failed();
            }
            BuildEngine.theEngine.Repository.StoreVirtual(this.outputObj, new Fresh(), contents);
            return new Fresh();
        }

        public FStarDepOutput getDependenciesFound(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Failed;
            try
            {
                var result = (FStarDepOutput)BuildEngine.theEngine.Repository.FetchVirtual(this.outputObj);
                ddisp = DependencyDisposition.Complete;
                return result;

            }
            catch (ObjectNotReadyException)
            {
                ddisp = DependencyDisposition.Incomplete;
                return null;
            }
        }

        private IEnumerable<string> GetNormalizedArgs()
        {
            yield return "--dep";
            yield return "make";
            foreach (var arg in this.optParser.GetNormalizedArgs())
            {
                yield return arg;
            }
        }
    }
}
