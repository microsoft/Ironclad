//--
// <copyright file="DafnyCCVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
using System;
using System.Collections.Generic;
using System.IO;
    using System.Linq;

    internal class DafnyCCVerb
        : DafnyTransformBaseVerb
    {
        private AbstractId abstractId;
        private FramePointerMode useFramePointer;
        private VSSolutionVerb dafnyCCBuildExecutableVerb;

        public DafnyCCVerb(SourcePath dfyroot, string appLabel, FramePointerMode useFramePointer)
            : base(dfyroot, appLabel)
        {
            this.useFramePointer = useFramePointer;
            this.abstractId = new AbstractId(this.GetType().Name, this.getVersion() + version, dfyroot.ToString(), concrete: useFramePointer.ToString());
            this.dafnyCCBuildExecutableVerb = new VSSolutionVerb(new SourcePath("tools\\DafnyCC\\DafnyCC.sln", SourcePath.SourceType.Tools));
        }

        public enum FramePointerMode
        {
            UseFramePointer,
            NoFramePointer
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return base.getVerbs().Concat(new[] { this.dafnyCCBuildExecutableVerb });
        }
     
        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        // This is merely an assert double-check that we didn't let a spec generated
        // by DafnyCC slip through to be used in the BoogieAsmVerify step.
        internal static void AssertSmellsImplementy(BuildObject obj)
        {
            string fn = obj.getFileNameWithoutExtension();
            Util.Assert(fn.EndsWith("_" + DafnyTransformBaseVerb.DAFNY_I_SUFFIX)
                || fn.EndsWith("_" + DafnyTransformBaseVerb.DAFNY_C_SUFFIX)
                || fn.Equals("Checked")
                || fn.Equals("Heap")
                || fn.Equals("Seq"));
        }
     
        protected override int getVersion()
        {
            return 18;
        }

        protected override BuildObject getExecutable()
        {
            return new BuildObject(Path.Combine(this.dafnyCCBuildExecutableVerb.getOutputPath().getRelativePath(), "dafnycc.exe"));
        }

        protected override IEnumerable<BuildObject> getExtraDependencies()
        {
            string exePath = this.dafnyCCBuildExecutableVerb.getOutputPath().getRelativePath();

            // REVIEW: Should we extract the dafnycc.exe dependencies from the project file instead of listing them manually?
            // REVIEW: What about Graph.dll?  Not needed?
            return new BuildObject[] {
                new BuildObject(Path.Combine(exePath, "Basetypes.dll")),
                new BuildObject(Path.Combine(exePath, "CodeContractsExtender.dll")),
                new BuildObject(Path.Combine(exePath, "Core.dll")),
                new BuildObject(Path.Combine(exePath, "DafnyPipeline.dll")),
                new BuildObject(Path.Combine(exePath, "ParserHelper.dll")),
                new BuildObject(Path.Combine(exePath, "Provers.SMTLib.dll")),
                new BuildObject(Path.Combine(exePath, "VCGeneration.dll")),
                new BuildObject(Path.Combine(exePath, "z3.exe")),
                getDafnyPrelude()
            };
        }

        protected override IEnumerable<SourcePath> getRootArgs()
        {
            DependencyDisposition ddisp;
            IEnumerable<SourcePath> result = getAllDafnyModules(out ddisp);
            Util.Assert(ddisp == DependencyDisposition.Complete);
            return result;
        }

        protected override IEnumerable<string> getExtraSpecialOutputs()
        {
            // Work around some undesirable behavior presently in DafnyCC:
            // We can't pass DafnyPrelude on the command line (getRootArgs) to DafnyCC,
            // yet it emits a dafny_DafnyPrelude file that we want to account for in the output.
            return new string[] { "Checked", "Heap", "Seq" }; ////, "dafny_DafnyPrelude" };
        }

        protected override void addExtraArgs(List<string> args)
        {
            args.Add("/relational");
            if (this.useFramePointer == FramePointerMode.UseFramePointer)
            {
                args.Add("/useFramePointer");
            }
        }

        protected override IEnumerable<SourcePath> getRoots()
        {
            return new SourcePath[]
        {
                new SourcePath("src\\Trusted\\DafnySpec\\Seq.s.dfy"),
                new SourcePath("src\\Checked\\Libraries\\DafnyCC\\Seq.dfy"),
                dfyroot
            };
        }
    }
}
