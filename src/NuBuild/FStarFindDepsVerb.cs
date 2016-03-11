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
        private readonly BuildObject outputObj;

        private readonly FStarOptionParser optParser;
        
        public FStarFindDepsVerb(IEnumerable<string> args, AbsoluteFileSystemPath invokedFrom)
        {
            this.args = args;
            this.optParser = new FStarOptionParser(args, invokedFrom);
            this.signature = this.optParser.GetSignature();
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
            // this task runs locally, using an absolute path to the executable and all source files. there's no need, therefore, to let nubuild know about any dependencies to transfer to the working directory.
            ddisp = DependencyDisposition.Complete;
            return new BuildObject[0];
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
            var exePath = FileSystemPath.Join(NuBuildEnvironment.RootDirectoryPath, FStarEnvironment.PathToFStarExe).ToString();

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
                allowAbsoluteArgs: true,
                allowAbsoluteExe: true);
        }

        public Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {
            Func<string, string> annotateOutput =
                s =>
                    string.Format("(while scanning for F* module dependencies...)\n{0}",  s);

            stdout = stdout.Trim();
            if (!string.IsNullOrWhiteSpace(stdout))
            {
                Logger.WriteLine(annotateOutput(stdout), new[] { "fstar", "stdout", "*quiet" });
            }
            stderr = stderr.Trim();
            if (!string.IsNullOrWhiteSpace(stderr))
            {
                Logger.WriteLine(annotateOutput(stderr), new[] { "fstar", "stderr" });
            }

            FStarDepOutput contents;
            try
            {
                contents = new FStarDepOutput(stdout, this.optParser);
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
            foreach (var arg in this.optParser.GetNormalizedArgs(NuBuildEnvironment.RootDirectoryPath))
            {
                yield return arg;
            }
        }
    }
}
