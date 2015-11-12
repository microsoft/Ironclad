//--
// <copyright file="BoogieVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
using System;
using System.Collections.Generic;
using System.IO;
    using System.Linq;

    internal class BoogieVerb
        : VerificationResultVerb, IProcessInvokeAsyncVerb
    {
        public const string BPL_EXTN = ".bpl";
        public const string CommentSymbol = "//-";

        private const int version = 17;
        private const string AddBoogieFlagAnnotation = "AddBoogieFlag";

        // SECURITY POLICY: we only allow checked files to specify the flags below.
        // Otherwise, one might thing it reasonable to specify "/noVerify:1" or something.
        private static readonly string[] validFlagsAnyValue = { "/restartProver", "/timeLimit", "/trace" };
        private static readonly string[] validFlagsSpecificValues = { "/proverOpt:OPTIMIZE_FOR_BV=true", "/z3opt:NL_ARITH=false" };
        private static SourcePath boogieExecutable;

        private BuildObject bplInput;
        private AbstractId abstractId;
        private IEnumerable<IVerb> upstreamVerbs;
        private int timeLimit = 300;

        public BoogieVerb(IContextGeneratingVerb context, BuildObject bplInput, VerificationRequest.SymDiffMode symdiff)
        {
            if (bplInput.getExtension().Equals(BPL_EXTN))
            {
                this.bplInput = bplInput;
                upstreamVerbs = new List<IVerb>();
                // TODO this will probably break, since we don't know where this bplInput came from. Maybe that's okay, since the verb had to already exist to reach this point.
            }
            else if (symdiff == VerificationRequest.SymDiffMode.NoSymDiff)
            {
                IVerb boogieAsmVerb = new BoogieAsmVerifyVerb(context, bplInput, false);
                this.bplInput = boogieAsmVerb.getOutputs().First();
                upstreamVerbs = new IVerb[] { boogieAsmVerb };
            }
            else
            {
                IVerb workerVerb;
                SymDiffEngine.BuildPipeline(context, bplInput, out this.bplInput, out workerVerb);
                upstreamVerbs = new IVerb[] { workerVerb };
            }

            this.abstractId = new AbstractId(
                this.GetType().Name,
                version,
                bplInput.ToString(),
                concrete: symdiff.ToString());
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            List<BuildObject> result = new List<BuildObject>() { bplInput };
            result.Add(getBoogieExecutable());
            result.AddRange(getBoogieExecutableDependencies());
            return result;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return upstreamVerbs;
        }

        public override BuildObject getOutputFile()
        {
            return BeatExtensions.makeOutputObject(bplInput, BPL_EXTN + VerificationResultVerb.VERIFICATION_RESULT_EXTN);
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new BuildObject[] { getOutputFile() };
        }

        public override AbstractId getAbstractIdentifier()
        {
            return abstractId;
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            if (false)
            {
#pragma warning disable 162
                File.WriteAllText(workingDirectory.PathTo(getOutputFile()), "Verification disabled temporarily for debugging");
                return new VerbSyncWorker(workingDirectory, new Fresh());
#pragma warning restore 162
            }

            List<string> args = new List<string>();
            args.Add("/noinfer");
            args.Add("/typeEncoding:m");
            args.Add("/z3opt:ARITH_RANDOM_SEED=1");
            args.Add("/timeLimit:" + timeLimit);
            args.AddRange(getFlags());
            args.Add(bplInput.getRelativePath());

            return new ProcessInvokeAsyncWorker(
                workingDirectory,
                this,
                getBoogieExecutable().getRelativePath(),
                args.ToArray(),
                ProcessExitCodeHandling.NonzeroIsOkay,
                getDiagnosticsBase(),
                allowCloudExecution: true,
                returnStandardOut: true,
                returnStandardError: true);
        }

        public Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {
            VerificationResult vr = new VerificationResult(
                bplInput.getRelativePath(),
                cpuTimeSeconds,
                stdout,
                stderr,
                new VerificationResultBoogieParser());
            vr.addBasicPresentation();
            vr.toXmlFile(workingDirectory.PathTo(getOutputFile()));
            setWasRejectableFailure(vr.wasOnlyTimeouts());
            return disposition;
        }

        protected override BuildObject getSource()
        {
            return bplInput;
        }

        private static SourcePath getBoogieExecutable()
        {
            // TODO this should eventually be a BuildObject from *building* the executable.
            if (BoogieVerb.boogieExecutable == null)
            {
                BoogieVerb.boogieExecutable = new SourcePath("tools\\Dafny\\Boogie.exe", SourcePath.SourceType.Tools);
            }

            return BoogieVerb.boogieExecutable;
        }

        private static IEnumerable<BuildObject> getBoogieExecutableDependencies()
        {
            List<BuildObject> exeDepends = new List<BuildObject>();

            exeDepends.Add(new SourcePath("tools\\Dafny\\AbsInt.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BaseTypes.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\CodeContractsExtender.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Concurrency.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Core.dll", SourcePath.SourceType.Tools));          
            exeDepends.Add(new SourcePath("tools\\Dafny\\Doomed.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\ExecutionEngine.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Graph.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Model.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\msvcp100.dll", SourcePath.SourceType.Tools));  // Needed by z3.
            exeDepends.Add(new SourcePath("tools\\Dafny\\msvcr100.dll", SourcePath.SourceType.Tools));  // Needed by z3.
            exeDepends.Add(new SourcePath("tools\\Dafny\\ParserHelper.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Predication.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Provers.SMTLib.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\VCExpr.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\VCGeneration.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\vcomp100.dll", SourcePath.SourceType.Tools));  // Needed by z3.
            exeDepends.Add(new SourcePath("tools\\Dafny\\z3.exe", SourcePath.SourceType.Tools));

            return exeDepends;
        }

        private IEnumerable<string> getFlags()
        {
            List<string> flags = new List<string>();
            foreach (string[] ann in new AnnotationScanner(bplInput).getAnnotations(AddBoogieFlagAnnotation))
            {
                if (ann.Count() != 2)
                {
                    throw new SourceConfigurationError(bplInput + " has malformed annotation: " + string.Join(" ", ann));
                }

                string flag = ann[1];
                string[] flagParts = flag.Split(new char[] { ':' }, 2);
                if (validFlagsAnyValue.Contains(flagParts[0]))
                {
                    flags.Add(flag);
                }
                else if (validFlagsSpecificValues.Contains(flag))
                {
                    flags.Add(flag);
                }
                else
                {
                    throw new SourceConfigurationError(bplInput + " contains disallowed flag " + flag);
                }

                if (flagParts[0].Equals("/timeLimit"))
                {
                    Util.Assert(flagParts.Count() == 2);
                    timeLimit = Int32.Parse(flagParts[1]);
                }
            }

            return flags;
        }
    }
}
