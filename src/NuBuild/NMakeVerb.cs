//--
// <copyright file="NMakeVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Collections.Specialized;
    using System.Diagnostics;
    using System.IO;
    using System.Linq;

    internal class NmakeVerb
        : Verb, IProcessInvokeAsyncVerb
    {
        private const int version = 7;
        private static SourcePath nmakeExecutable;

        private SourcePath makefile;
        private CustomManifestParser customManifest;
        private AbstractId abstractId;
        private string outputPath;
        private string outputPathSuffix;

        public NmakeVerb(SourcePath makefile)
        {
            this.makefile = makefile;
            this.abstractId = new AbstractId(this.GetType().Name, version, this.makefile.ToString());

            // Generate output path.
            this.outputPath = ".";
            int depth = this.makefile.getDirPath().Split(@"\/".ToCharArray(), StringSplitOptions.RemoveEmptyEntries).Length;
            for (int i = 0; i < depth; i++)
            {
                this.outputPath = Path.Combine(this.outputPath, "..");
            }

            this.outputPathSuffix = Path.Combine(BuildEngine.theEngine.getObjRoot(), this.makefile.getDirPath());
            this.outputPath = Path.Combine(this.outputPath, this.outputPathSuffix);
            this.customManifest = new CustomManifestParser(this.makefile);
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            return this.customManifest.getDependencies().Union(new List<BuildObject>() { getNmakeExecutable() });
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[] { };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return from output in this.customManifest.getOutputs() select new BuildObject(Path.Combine(BuildEngine.theEngine.getObjRoot(), output.getRelativePath()));
        }

        public BuildObject getOutputPath()
        {
            return new BuildObject(this.outputPathSuffix);
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            // Scrub the "makeflags" environment variable from our environment
            // so we don't pass it down to our worker process.  Some users may
            // have things there that conflict with our usage.
            Process myProcess = System.Diagnostics.Process.GetCurrentProcess();
            StringDictionary environmentVariables = myProcess.StartInfo.EnvironmentVariables;
            environmentVariables.Remove("MAKEFLAGS");

            List<string> args = new List<string>();
            args.Add(string.Format("OBJ={0}\\obj", workingDirectory.PathTo(this.outputPathSuffix)));
            args.Add(string.Format("BIN={0}", workingDirectory.PathTo(this.outputPathSuffix)));
            args.Add("-f");
            args.Add(workingDirectory.PathTo(this.makefile));

            // TODO: Remove reliance on workingDirOverride, which currently hides dependency issues and other problems.
            return new ProcessInvokeAsyncWorker(
                workingDirectory,
                this,
                getNmakeExecutable().getRelativePath(), ////"c:/Program Files (x86)/Microsoft Visual Studio 12.0/VC/bin/nmake.exe",
                args.ToArray(),
                ProcessExitCodeHandling.NonzeroIsFailure,
                workingDirOverride: IronRootDirectory.PathTo(this.makefile.getDirPath()),
                failureBase: getDiagnosticsBase(),
                //allowAbsoluteExe: true,
                allowAbsoluteArgs: true);
        }

        public Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {
            return disposition;
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        private static SourcePath getNmakeExecutable()
        {
            // TODO this should eventually be a BuildObject from *building* the executable.
            if (nmakeExecutable == null)
            {
                nmakeExecutable = new SourcePath("tools\\nmake\\nmake.exe", SourcePath.SourceType.Tools);
            }

            return nmakeExecutable;
        }
    }
}
