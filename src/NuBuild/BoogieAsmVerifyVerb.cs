//--
// <copyright file="BoogieAsmVerifyVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;

    internal class BoogieAsmVerifyVerb
            : BoogieAsmWorkerBase
    {
        public const string MUTUAL_SUMMARY_EXTN = ".ms";
        public const string SYMDIFF_EXTN = ".symdiff";
        public const string SYMDIFF_DIR_EXTN = ".dir";
        private const string AddBoogieAxiomAnnotation = "AddBoogieAxiom";
        private const string BasmEnableSymdiffAnnotation = "BasmEnableSymdiff";

        private bool buildSymDiffMutualSummary;
        private bool enableSymdiff = false;
        private string dirName;

        public BoogieAsmVerifyVerb(IContextGeneratingVerb context, BuildObject input, bool buildSymDiffMutualSummary)
            : base(context, input)
        {
            this.buildSymDiffMutualSummary = buildSymDiffMutualSummary;
            this.enableSymdiff = BoogieAsmVerifyVerb.needs_symdiff(basmInput);
        }

        public static bool needs_symdiff(BuildObject basm)
        {
            AnnotationScanner annotations = new AnnotationScanner(basm);
            bool symdiff = false;
            foreach (string[] ann in annotations.getAnnotations(BasmEnableSymdiffAnnotation))
            {
                if (ann.Length != 2
                    || !ann[1].Equals("true"))
                {
                    throw new SourceConfigurationError("Expected " + BasmEnableSymdiffAnnotation + " to have argument 'true'.");
                }

                symdiff = true;
            }

            return symdiff;
        }

        public override BuildObject outputFile()
        {
            if (buildSymDiffMutualSummary)
            {
                // SymDiff files need to go into their own directory
                BuildObject normalName = BeatExtensions.makeOutputObject(basmInput, SYMDIFF_EXTN);
                dirName = normalName.getFileName() + SYMDIFF_DIR_EXTN;
                BuildObject dirExtendedName = new BuildObject(Path.Combine(normalName.getDirPath(), dirName, normalName.getFileName()));

                return dirExtendedName;
            }
            else
            {
                return BeatExtensions.makeOutputObject(basmInput, BoogieVerb.BPL_EXTN);
            }
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            // Hey BJP: why do we have BoogieAsmLink here offering boogie verbs? I guess because it's safe and hint-y?
            return getVerifyishVerbs();
        }

        public BuildObject getMutualSummary()
        {
            // SymDiff files need to go into their own directory.
            BuildObject normalName = BeatExtensions.makeOutputObject(basmInput, MUTUAL_SUMMARY_EXTN);
            BuildObject dirExtendedName = new BuildObject(Path.Combine(normalName.getDirPath(), dirName, normalName.getFileName()));
            return dirExtendedName;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            List<BuildObject> outputs = new List<BuildObject> { outputFile() };
            if (buildSymDiffMutualSummary)
            {
                outputs.Add(getMutualSummary());
            }

            return outputs;
        }

        protected override IEnumerable<BuildObject> getExtraDeps(out DependencyDisposition ddisp)
        {
            try
            {
                ddisp = DependencyDisposition.Complete;
                return getTrustedBoogieAxioms();
            }
            catch (ObjectNotReadyException)
            {
                // All the basms aren't here yet, so we can't scan them. Don't sweat it;
                // those deps are already being called for.
                ddisp = DependencyDisposition.Incomplete;
                return new BuildObject[] { };
            }
            catch (ObjectFailedException)
            {
                ddisp = DependencyDisposition.Failed;
                return new BuildObject[] { };
            }
        }

        protected override void extendArgs(List<string> args)
        {            
            if (!buildSymDiffMutualSummary && enableSymdiff)
            {
                args.Add("-symdiffok");
            }
            else if (buildSymDiffMutualSummary)
            {
                args.Add("-symdiffms");
                args.Add(getMutualSummary().getRelativePath());
            }

            ////foreach (SourcePath includedAxiom in getTrustedBoogieAxioms(acc.basmModules))
            foreach (SourcePath includedAxiom in getTrustedBoogieAxioms())
            {
                if (!includedAxiom.IsTrusted)
                {
                    throw new SourceConfigurationError(AddBoogieAxiomAnnotation + " annotation points at untrusted file " + includedAxiom.ToString());
                }

                // SECURITY POLICY: you can only include trusted things labeled "_axioms.bpl".
                if (!includedAxiom.getExtension().Equals(BoogieVerb.BPL_EXTN)
                    || !includedAxiom.getFileNameWithoutExtension().EndsWith("_axioms"))
                {
                    throw new SourceConfigurationError(AddBoogieAxiomAnnotation + " annotation points at file that isn't a Boogie axioms file: " + includedAxiom.ToString());
                }

                args.Add("/trustedBoogie:" + includedAxiom.getRelativePath());
            }
        }

        protected override void postprocess(WorkingDirectory workingDirectory)
        {
            AnnotationScanner.transferAnnotations(workingDirectory, basmInput, outputFile(), BoogieVerb.CommentSymbol);
        }

        protected override int getVersion()
        {
            return 20;
        }

        protected override string getAction()
        {
            return "-verify";
        }

        protected override bool outFlagWorks()
        {
            return true;
        }

        protected override bool includeAllImps()
        {
            return false;
        }

        protected override string getExtraAbstractID()
        {
            return buildSymDiffMutualSummary ? ", relational" : ", functional";
        }

        private IEnumerable<SourcePath> getTrustedBoogieAxioms()
        {
            OrderPreservingSet<SourcePath> result = new OrderPreservingSet<SourcePath>();
            AnnotationScanner anns = new AnnotationScanner(basmInput);
            foreach (string[] annotation in anns.getAnnotations(AddBoogieAxiomAnnotation))
            {
                string module = annotation[1];
                SourcePath trustedPath = new SourcePath(Path.Combine(
                    BuildEngine.theEngine.getSrcRoot(),
                    BuildEngine.VerveTrustedSpecDir,
                    module + BoogieVerb.BPL_EXTN));
                result.Add(trustedPath);
            }

            return result;
        }
    }
}
