//--
// <copyright file="DafnyVerifyOneVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    internal class DafnyVerifyOneVerb
        : VerificationResultVerb, IProcessInvokeAsyncVerb
    {
        public const string DAFNY_EXTN = ".dfy";
        private const int version = 15;
        private const string ADDDAFNYFLAG_LABEL = "AddDafnyFlag";

        private SourcePath dfysource;
        private AbstractId abstractId;

        public DafnyVerifyOneVerb(SourcePath dfysource)
        {
            this.dfysource = dfysource;
            this.abstractId = new AbstractId(this.GetType().Name, version, dfysource.ToString());                
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            TransitiveDepsVerb depsVerb = this.getTransitiveDepsVerb();
            HashSet<BuildObject> result = depsVerb.getAvailableDeps(out ddisp);
            result.UnionWith(DafnyExecutableDependencies.getDafnyExecutableDependencies());
            return result;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[0];    // All inputs are sources.
        }

        public override BuildObject getOutputFile()
        {
            return this.dfysource.makeOutputObject(".dfy.v");
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new[] { this.getOutputFile() };
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            List<string> arguments = new List<string>();
            arguments.Add("/noNLarith");
            arguments.Add("/allowGlobals");
            arguments.Add("/z3opt:nlsat.randomize=false");
            arguments.Add("/z3opt:pi.warnings=true");
            arguments.Add("/proverWarnings:1");
            arguments.Add("/compile:0");
            arguments.Add("/timeLimit:30");
            arguments.Add("/noCheating:1");
            arguments.Add("/autoTriggers:1");
            arguments.Add("/ironDafny");
            foreach (string[] ann in new AnnotationScanner(this.dfysource).getAnnotations(ADDDAFNYFLAG_LABEL))
            {
                if (ann.Length != 2)
                {
                    throw new SourceConfigurationError("Expected exactly 1 argument to " + ADDDAFNYFLAG_LABEL);
                }

                arguments.Add(ann[1]);
            }

            arguments.Add(this.dfysource.getRelativePath());
            Logger.WriteLine("arguments: " + string.Join(" ", arguments));

            return new ProcessInvokeAsyncWorker(
                workingDirectory,
                this,
                DafnyExecutableDependencies.getDafnyExecutable().getRelativePath(),
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
                this.dfysource.getRelativePath(),
                cpuTimeSeconds,
                stdout,
                stderr,
                new VerificationResultDafnyParser());
            vr.addBasicPresentation();
            vr.toXmlFile(workingDirectory.PathTo(this.getOutputFile()));
            this.setWasRejectableFailure(!vr.pass);
            return disposition;
        }

        public IEnumerable<BuildObject> getDirectIncludes()
        {
            // By the time this method is called by VerbToposorter,
            // this verb is scheduled for execution, and hence its deps
            // are complete. So all of these lookups should succeed.
            // (wait, does that follow?)
            return this.getTransitiveDepsVerb().getShallowIncludes();
        }

        protected override BuildObject getSource()
        {
            return this.dfysource;
        }        

        private TransitiveDepsVerb getTransitiveDepsVerb()
        {
            return new DafnyTransitiveDepsVerb(this.dfysource);
        }
    }
}
