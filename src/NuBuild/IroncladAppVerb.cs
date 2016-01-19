//--
// <copyright file="IroncladAppVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;

    internal class IroncladAppVerb
        : Verb, IObligationsProducer
    {
        public const string TRUSTED_EXE_EXTN = ".exe";
        public const string UNVERIFIED_SENTINEL_EXTENSION = ".usentinel";
        private const int version = 5;

        ////public enum VerifyMode { Verify, NoVerify };
        ////public enum SymDiffMode { UseSymDiff, NoSymDiff };

        private SourcePath dfyroot;  // REVIEW: Never used?
        private AbstractId abstractId;
        private DafnySpecVerb dafnyspecVerb;
        private DafnyCCVerb dafnyccVerb;
        private EntryStitcherVerb stitcherVerb;
        private VerificationResultSummaryVerb verifyResultsVerb;
        private LinkerVerb linkerVerb;
        private PoundDefines poundDefines;
        private VerificationRequest verificationRequest;
        private string appLabel;

        private BuildObject srcObject;
        private BuildObject exeObject;
        private BuildObject outputObject;

        public IroncladAppVerb(SourcePath dfyroot, TARGET target, DafnyCCVerb.FramePointerMode framePointerMode, VerificationRequest verificationRequest)
        {
            this.dfyroot = dfyroot;

            // TODO this is the only #define we support just yet, so I'm stuffing it in here.
            // We'll need to plumb more carefully when we want to add x64.
            if (dfyroot.getDirPath().Split(Path.DirectorySeparatorChar).Last().Equals("AppLoader"))
            {
                this.poundDefines = new PoundDefines(new string[] { "AppLoader" });
            }
            else
            {
                this.poundDefines = PoundDefines.empty();
            }

            this.verificationRequest = verificationRequest;
            this.abstractId = new AbstractId(
                this.GetType().Name,
                version,
                dfyroot.ToString(),
                this.poundDefines,
                concrete: string.Format(
                    "{0},{1},{2}",
                    target,
                    framePointerMode.ToString(),
                    verificationRequest.ToString()));
            this.appLabel = dfyroot.getDirPath().Split(Path.DirectorySeparatorChar).Last();
            this.dafnyspecVerb = new DafnySpecVerb(dfyroot, this.appLabel);
            this.dafnyccVerb = new DafnyCCVerb(dfyroot, this.appLabel, framePointerMode);

            bool isLoader = dfyroot.getRelativePath().Equals(BootableAppVerb.LOADER_DFY);

            // NB we keep dafnyccVerb as the lowest-priority context, so that our hand-written
            // beat impls will override its output.
            IContextGeneratingVerb contextWithDafny = new ConcatContextVerb(
                BuildEngine.theEngine.getVerveContextVerb(this.poundDefines),
                new VerbOutputsContextVerb(this.dafnyspecVerb, false),
                new VerbOutputsContextVerb(this.dafnyccVerb, true),
                this.poundDefines);
            this.stitcherVerb = new EntryStitcherVerb(contextWithDafny, this.appLabel);
            IContextGeneratingVerb contextWithDafnyAndEntry = new ConcatContextVerb(
                new VerbOutputsContextVerb(this.stitcherVerb, false),
                contextWithDafny,
                this.poundDefines);

            BuildObject entryImpObj = this.stitcherVerb.getEntryImpOutput();
            BoogieAsmLinkVerb entryVerb = new BoogieAsmLinkVerb(contextWithDafnyAndEntry, entryImpObj);
            if (target == TARGET.BARE_METAL)
            {
                MasmVerb masmVerb = new MasmVerb(entryVerb);
                this.linkerVerb = new LinkerVerb(masmVerb, isLoader);
            }
            else if (target == TARGET.WINDOWS)
            {     // Rewrite the asm that comes out of entryVerb before linking it
                AsmRewriterVerb rewriter = new AsmRewriterVerb(entryVerb);
                MasmVerb masmVerb = new MasmVerb(rewriter);
                this.linkerVerb = new WinLinkerVerb(masmVerb, isLoader);
            }

            BoogieAsmVerificationObligationListVerb bavolVerb =
                new BoogieAsmVerificationObligationListVerb(contextWithDafnyAndEntry, entryImpObj, verificationRequest);

            this.verifyResultsVerb = new VerificationResultSummaryVerb(bavolVerb);

            this.srcObject = this.linkerVerb.getUntrustedExe();
            if (verificationRequest.isComplete())
            {
                this.exeObject = dfyroot.makeOutputObject(TRUSTED_EXE_EXTN);
                this.outputObject = this.exeObject;
            }
            else
            {
                this.exeObject = this.srcObject;
                this.outputObject = dfyroot.makeVirtualObject(UNVERIFIED_SENTINEL_EXTENSION);
            }
        }

        public enum TARGET
        {
            BARE_METAL,
            WINDOWS
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            List<BuildObject> result = new List<BuildObject>();
            result.Add(this.srcObject);

            result.Add(this.verifyResultsVerb.getOutputFile());

            ddisp = DependencyDisposition.Complete;

            return result;
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            if (this.verificationRequest.isComplete())
            {
                // If the verification succeeded, then we convert the untrusted exe into a trusted exe (via a copy).
                VerificationResult vr = VerificationResult.fromXmlFile(this.verifyResultsVerb.getOutputFile());

                if (!vr.pass)
                {
                    return new VerbSyncWorker(workingDirectory, new Failed());
                }

                File.Copy(workingDirectory.PathTo(this.srcObject), workingDirectory.PathTo(this.outputObject), true);   // True => Overwrite
            }
            else
            {
                UnverifiedSentinelVirtualContents contents = new UnverifiedSentinelVirtualContents();
                BuildEngine.theEngine.Repository.StoreVirtual(this.outputObject, new Fresh(), contents);
            }

            return new VerbSyncWorker(workingDirectory, new Fresh());
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            List<IVerb> result = new List<IVerb>();
            result.Add(this.dafnyccVerb);
            result.Add(this.stitcherVerb);
            result.Add(this.linkerVerb);
            result.Add(this.verifyResultsVerb);
            result.AddRange(this.verifyResultsVerb.getVerbs());   // Sleazy.
            return result;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new BuildObject[] { this.outputObject };
        }

        public BuildObject getObligationSet()
        {
            return this.verifyResultsVerb.getObligationSet();
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public BuildObject getExe()
        {
            return this.exeObject;
        }

        public override Presentation getPresentation()
        {
            return this.verifyResultsVerb.getPresentation();
        }

        public string getAppLabel()
        {
            return this.appLabel;
        }
    }
}
