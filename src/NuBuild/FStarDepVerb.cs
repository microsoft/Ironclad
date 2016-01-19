//--
// <copyright file="FStarDepVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;

    internal class FStarDepVerb: Verb, IProcessInvokeAsyncVerb
    {
        private const string DepsObjExtension = ".fstdeps.vob";
        private const int Version = 1;
        // todo: i made this a BuildObject based on what's in TransitiveDepsVerb. i don't understand why it's not a SourcePath, however.
        private BuildObject sourcePath;
        private BuildObject depsObj;

        private AbstractId abstractId;

        private readonly string[] fstArgs;

        public FStarDepVerb(SourcePath sourcePath, IEnumerable<string> fstArgs)
        {
            this.sourcePath = sourcePath;
            this.depsObj = sourcePath.makeVirtualObject(BeatExtensions.whichPart(sourcePath).ExtnStr() + DepsObjExtension);
            var concrete = string.Join(" ", fstArgs);
            this.abstractId = new AbstractId(this.GetType().Name, Version, sourcePath.ToString(), concrete: concrete);
            this.fstArgs = fstArgs.ToArray();
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            var result = new HashSet<BuildObject>();
            result.UnionWith(FStarEnvironment.getStandardDependencies());
            result.Add(this.sourcePath);
            ddisp = DependencyDisposition.Complete;
            return result;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[0];    // All inputs are sources.
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new[] { this.depsObj };
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            List<string> arguments = new List<string>();
            arguments.Add("--dep");
            arguments.Add("nubuild");
            arguments.AddRange(this.fstArgs);
            arguments.Add(this.sourcePath.getRelativePath());
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
                contents = new FStarDepOutput(stdout, this.sourcePath, workingDirectory);
            }
            catch (Exception e)
            {
                var msg = string.Format("failed to process output of `{0} --find_deps` (unhandled {1}). Details follow:\n{2}", FStarEnvironment.PathToFStarExe, e.GetType().Name, e.Message);
                Logger.WriteLine(msg, new []{"error", "fstar"});
                return new Failed();
            }
            BuildEngine.theEngine.Repository.StoreVirtual(this.depsObj, new Fresh(), contents);
            return new Fresh();
        }

        public FStarDepOutput getDependenciesFound(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Failed;
            try
            {
                var result = (FStarDepOutput)BuildEngine.theEngine.Repository.FetchVirtual(this.depsObj);
                ddisp = DependencyDisposition.Complete;
                return result;

            }
            catch (ObjectNotReadyException)
            {
                ddisp = DependencyDisposition.Incomplete;
                return null;
            }
        }
    }
}
