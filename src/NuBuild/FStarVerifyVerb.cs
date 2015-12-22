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

    using Microsoft.Data.OData.Query.SemanticAst;

    using NDepend.Path;

    internal class FStarVerifyVerb
        : VerificationResultVerb, IProcessInvokeAsyncVerb
    {
        public const string SourceFileExtension = ".fst";
        private const int Version = 1;

        private SourcePath fstSource;
        private AbstractId abstractId;

        private FStarDepVerb depsVerb;
        private readonly List<string> fstArgs;

        private List<SourcePath> secondarySources;

        public FStarVerifyVerb(IEnumerable<string> fstArgs, bool rewritePaths = false)
        {
            if (rewritePaths)
            {
                this.fstArgs = rewritePathArgs(fstArgs, out this.secondarySources);
            }
            else
            {
                this.fstArgs = fstArgs.ToList();
            }

            // the final argument is assumed to be our NuBuild source.
            var last = this.fstArgs.Count - 1;
            this.fstSource = new SourcePath(this.fstArgs[last]);
            var ext = this.fstSource.getExtension();
            if (ext == null || !ext.Equals(SourceFileExtension))
            {
                throw new ArgumentException(string.Format("The final argument to `VerifyFst` ({0}) was not an F* module source (`.fst` file); please considering rearranging the arguments to `fstar.exe` so that options preceed file names.", fstArgs.Last()));
            }
            this.fstArgs.RemoveAt(last);

            var concrete = string.Join(" ", this.fstArgs);
            this.abstractId = new AbstractId(this.GetType().Name, Version, fstSource.ToString(), concrete: concrete);
            if (extractAutoDep(this.fstArgs))
            {
                // note that what we pass into FStarDepVerb's constructor is not necessarily the same as what wasa passed into ours.
                this.depsVerb = new FStarDepVerb(this.fstSource, this.fstArgs);
            }
            else
            {
                this.depsVerb = null;
            }
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
            result.UnionWith(this.secondarySources);
            if (this.depsVerb == null)
            {
                ddisp = DependencyDisposition.Complete;
                return result;
            }
            else
            {
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
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            if (this.depsVerb == null)
            {
                return new IVerb[0];
            }
            else
            {
                return new IVerb[] { this.depsVerb };
            }
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
            arguments.AddRange(this.fstArgs);
            arguments.Add(this.fstSource.getRelativePath());
            var exePath = FStarEnvironment.PathToFStarExe.ToString();

            Logger.WriteLine(string.Format("{0} invokes `{1} {2}` from `{3}`", this, exePath, string.Join(" ", arguments), workingDirectory.ToAbsoluteDirectoryPath()));
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
            if (!s.IsValidRelativeFilePath())
                return null;
            var relFilePath = s.ToRelativeFilePath();
            var ext = relFilePath.FileExtension;
            if (!ext.Equals(".fst", StringComparison.InvariantCultureIgnoreCase) && !ext.Equals(".fsi", StringComparison.InvariantCultureIgnoreCase) && !ext.Equals(".fsti", StringComparison.InvariantCultureIgnoreCase))
            {
                return null;
            }
            var absFilePath = relFilePath.GetAbsolutePathFrom(NuBuildEnvironment.InvocationPath);
            if (!absFilePath.Exists)
            {
                return null;
            }
            var buildObjPath = absFilePath.GetRelativePathFrom(NuBuildEnvironment.RootDirectoryPath);
            return buildObjPath.ToImplicitPathString();
        }

        private static List<string> rewritePathArgs(IEnumerable<string> args, out List<SourcePath> secondarySources)
        {
            secondarySources = new List<SourcePath>();
            var result = new List<string>();
            foreach (var a in args)
            {
                if (!a.StartsWith("--"))
                {
                    var s = attemptToRewritePath(a);
                    if (s != null)
                    {
                        result.Add(s);
                        secondarySources.Add(new SourcePath(s));
                        continue;
                    }
                }

                result.Add(a);
            }

            return result;
        }

        private static bool extractAutoDep(IList<string> args)
        {
            for (var i = 0; i < args.Count; ++i)
            {
                // todo: this isn't implemented yet in F*.
                if (args[i].Equals("--auto_dep", StringComparison.InvariantCulture))
                {
                    Logger.WriteLine("Dependency search option detected.", "verbose");
                    args.RemoveAt(i);
                    return true;
                }
            }
            return false;
        }
    }
}
