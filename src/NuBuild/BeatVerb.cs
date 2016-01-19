//--
// <copyright file="BeatVerb.cs" company="Microsoft Corporation">
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

    internal class BeatVerb
        : Verb, IProcessInvokeAsyncVerb
    {
        private const int version = 34;

        private static NmakeVerb beatBuildExecutableVerb = new NmakeVerb(new SourcePath("tools\\Beat\\makefile", SourcePath.SourceType.Tools));

        private IContextGeneratingVerb contextVerb;
        private BuildObject beatobj;
        private string appLabel;
        private AbstractId abstractId;

        public BeatVerb(IContextGeneratingVerb contextVerb, BuildObject beatobj, string appLabel)
        {
            this.contextVerb = contextVerb;
            this.beatobj = beatobj;
            this.appLabel = appLabel;
            this.abstractId = new AbstractId(this.GetType().Name, version, beatobj.ToString(), contextVerb.getPoundDefines(), concrete: appLabel);
        }

        public static bool isBeat(BuildObject obj)
        {
            return obj.getExtension().Equals(BeatExtensions.BEATIFC_EXTN)
                || obj.getExtension().Equals(BeatExtensions.BEATIMP_EXTN);
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            OrderPreservingSet<BuildObject> deps = BeatExtensions.getBeatFlavoredShallowDependencies(
                this.contextVerb, this.beatobj, out ddisp, BeatIncludes.ImportFilter.ForBeatOrBasm);
            deps.Add(this.getBeatExecutable());
            return deps;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[] { this.contextVerb, beatBuildExecutableVerb };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new BuildObject[] { this.outputFile() };
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public BuildObject getBeatExecutable()
        {
            // Whaaat? Why doesn't beatBuildExecutableVerb.getOutputPath() already end with beat.exe!? Weirdly,
            // nope, its getOutputPath() is a directory.
            return new BuildObject(Path.Combine(beatBuildExecutableVerb.getOutputPath().getRelativePath(), "beat.exe"));
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            // "beat $BUILD_DEFS -out $out.tmp -in $in $incls"
            List<string> args = new List<string>();
            args.Add("-in");
            args.Add(this.beatobj.getRelativePath());

            IEnumerable<BuildObject> beatImports =
                BeatExtensions.getBeatFlavoredShallowIncludes(this.contextVerb, this.beatobj, BeatIncludes.ImportFilter.ForBeatOrBasm);
            foreach (BuildObject ifcObj in beatImports.Where(obj => !obj.Equals(this.beatobj)))
            {
                Util.Assert(!ifcObj.getRelativePath().Contains(".imp"));   // Erk, don't feed imp files as includes!
                args.Add("-i");
                args.Add(ifcObj.getRelativePath());
            }

            args.AddRange(this.contextVerb.getPoundDefines().ToDefArgs());

            string dbgText = string.Format(
                "rem verb {0}{1}",
                this,
                System.Environment.NewLine);

            return new ProcessInvokeAsyncWorker(
                workingDirectory,
                this,
                this.getBeatExecutable().getRelativePath(),
                args.ToArray(),
                ProcessExitCodeHandling.NonzeroIsFailure,
                captureStdout: this.outputFile(),
                failureBase: getDiagnosticsBase(),
                dbgText: dbgText);
        }

        public Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {
            if (disposition is Fresh)
            {
                BeatExtensions.propagatePrivateImports(workingDirectory, this.contextVerb, this.beatobj, this.outputFile());

                // And then propagate the NuBuild annotations, too.
                AnnotationScanner.transferAnnotations(
                    workingDirectory,
                    this.beatobj,
                    this.outputFile(),
                    BoogieAsmDepBase.CommentSymbol);
            }

            return disposition;
        }

        private BuildObject outputFile()
        {
            string outputAppLabel = (this.appLabel == null ? string.Empty : this.appLabel) + this.contextVerb.getPoundDefines().ToString();
            string extn = this.beatobj.getExtension().Equals(BeatExtensions.BEATIFC_EXTN) ? BoogieAsmVerifyVerb.BASMIFC_EXTN : BoogieAsmVerifyVerb.BASMIMP_EXTN;
            return this.beatobj.makeLabeledOutputObject(outputAppLabel, extn);
        }

        private string getModuleNameForObj(BuildObject obj)
        {
            return obj.getFileNameWithoutExtension();
        }
    }
}
