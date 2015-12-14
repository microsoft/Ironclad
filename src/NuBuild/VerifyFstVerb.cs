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
    using System.IO;
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
        private readonly List<string> fstArgs;

        public VerifyFstVerb(IEnumerable<string> fstArgs, bool rewritePaths = false)
        {
            // the final argument is assumed to be our NuBuild source.
            //var sourcePath = new SourcePath(FilePath.StringToNuBuildPath(remainingArgs[remainingArgs.Count - 1]).ToString());
            if (rewritePaths)
            {
                this.fstArgs = rewritePathArgs(fstArgs);
            }
            else
            {
                this.fstArgs = fstArgs.ToList();
            }

            var last = this.fstArgs.Count - 1;
            this.fstSource = new SourcePath(this.fstArgs[last]);
            this.fstArgs.RemoveAt(last);

            var concrete = string.Join(" ", this.fstArgs);
            this.abstractId = new AbstractId(this.GetType().Name, Version, fstSource.ToString(), concrete: concrete);
            // note that what we pass into FStarFindDepsVerb's constructor is not necessarily the same as our 
            this.depsVerb = new FStarFindDepsVerb(this.fstSource, this.fstArgs);
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
            arguments.AddRange(this.fstArgs);
            arguments.Add(this.fstSource.getRelativePath());
            var exePath = FStarEnvironment.PathToFStarExe.ToString();

            Logger.WriteLine(string.Format("[NuBuild] {0} invokes `{1} {2}`", this, exePath, string.Join(" ", arguments)));
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

        private static string attemptToRewritePath(string path)
        {
            var s = Path.Combine(".", path);
            if (s.IsValidRelativeFilePath())
            {
                var relFilePath = s.ToRelativeFilePath();
                var absFilePath = relFilePath.GetAbsolutePathFrom(NuBuildEnvironment.InvocationPath);
                if (absFilePath.Exists)
                {
                    var nbPath = absFilePath.GetRelativePathFrom(NuBuildEnvironment.RootDirectoryPath);
                    return FilePath.RelativeToImplicit(nbPath);
                }
            }
            return null;
        }

        private static List<string> rewritePathArgs(IEnumerable<string> args)
        {
            var result = new List<string>();
            foreach (var a in args)
            {
                if (!a.StartsWith("--"))
                {
                    var s = attemptToRewritePath(a);
                    if (s != null)
                    {
                        result.Add(s);
                        continue;
                    }
                }

                result.Add(a);
            }

            return result;
        }
    }
}
