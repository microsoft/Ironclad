//--
// <copyright file="VSSolutionVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;

    /// <summary>
    /// Verb to build a Visual Studio solution.
    /// </summary>
    internal class VSSolutionVerb
        : Verb, IProcessInvokeAsyncVerb
    {
        private const int Version = 5;

        private readonly SourcePath solutionFile;
        private readonly AbstractId abstractId;
        private readonly VSSolutionParser solutionParser;
        private readonly string outputPathSuffix;
        private readonly DafnyCompileOneVerb dafnyCompileOneVerb;

        private readonly bool releaseBuild;

        /// <summary>
        /// Initializes a new instance of the VSSolutionVerb class.
        /// </summary>
        /// <param name="solutionFile">Solution file to build.</param>
        /// <param name="optionalDafnyInput">Optional dafny-derived-CSharp dependency.</param>
        public VSSolutionVerb(SourcePath solutionFile, SourcePath optionalDafnyInput = null, bool releaseBuild = false)
        {
            this.solutionFile = solutionFile;
            this.abstractId = new AbstractId(this.GetType().Name, VSSolutionVerb.Version, this.solutionFile.ToString());
            this.releaseBuild = releaseBuild;

            // Parse the solution file (and project files contained in the solution).
            this.solutionParser = new VSSolutionParser(this.solutionFile);

            this.outputPathSuffix = Path.Combine(BuildEngine.theEngine.getObjRoot(), this.solutionFile.getDirPath());

            if (optionalDafnyInput != null)
            {
                this.dafnyCompileOneVerb = new DafnyCompileOneVerb(optionalDafnyInput);
            }
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            List<BuildObject> dependencies = new List<BuildObject>(this.solutionParser.getDependencies());
            if (this.dafnyCompileOneVerb != null)
            {
                dependencies.AddRange(this.dafnyCompileOneVerb.getOutputs());
            }

            return dependencies;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[] { this.dafnyCompileOneVerb };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            // Note that since we override the solution output directory in our
            // getWorker() below, we also need to override the output paths
            // coming from the solution parser.
            return from output in this.solutionParser.getOutputs() select new BuildObject(Path.Combine(this.outputPathSuffix, output.getFileName()));
        }

        public BuildObject getOutputPath()
        {
            return new BuildObject(this.outputPathSuffix);
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            // If we were given an optional dafny input, let this build know about the resulting verb's output.
            // Note: this is deliberately written to break if someone changes DafnyCompileOneVerb to have multiple outputs.
            if (this.dafnyCompileOneVerb != null)
            {
                File.Copy(
                    workingDirectory.PathTo(this.dafnyCompileOneVerb.getOutputs().Single()),
                    Path.Combine(workingDirectory.PathTo(this.outputPathSuffix), "DafnyDerivedInput.cs"));
            }

            List<string> args = new List<string>();
            args.Add(string.Format("/p:OutDir={0}", workingDirectory.PathTo(this.outputPathSuffix)));
            args.Add(string.Format("/p:Configuration={0}", this.releaseBuild ? "Release" : "Debug"));
            ////args.Add("/fileLogger");  // Uncomment to log MSBuild execution.
            args.Add(workingDirectory.PathTo(this.solutionFile));

            // TODO: Fix absolute path to MSBuild.exe (at least use %SystemRoot%)!
            return new ProcessInvokeAsyncWorker(
                workingDirectory,
                this,
                "c:\\Windows\\Microsoft.NET\\Framework\\v4.0.30319\\MSBuild.exe",
                args.ToArray(),
                ProcessExitCodeHandling.NonzeroIsFailure,
                failureBase: getDiagnosticsBase(),
                allowAbsoluteExe: true,
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
    }
}
