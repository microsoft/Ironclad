//--
// <copyright file="IronfleetAppVerb.cs" company="Microsoft Corporation">
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

    /// <summary>
    /// Verb to build an Ironfleet application.
    /// This is a top-level verb.
    /// </summary>
    internal class IronfleetAppVerb : Verb, IObligationsProducer
    {
        private const int Version = 7;
        private const string UnverifiedExeExt = ".unverified.exe";
        private const string VerifiedExeExt = ".exe";
        private readonly BuildObject input;
        private readonly BuildObject exeOutput;
        private readonly List<BuildObject> otherOutputs;
        private readonly AbstractId abstractId;
        private readonly VerificationResultSummaryVerb verifyVerb;
        private readonly VSSolutionVerb buildVerb;
        private readonly IVerb[] verbs;
        private List<BuildObject> dependencies;

        /// <summary>
        /// Initializes a new instance of the IronfleetAppVerb class.
        /// </summary>
        /// <param name="input">Main dafny file for the application.</param>
        public IronfleetAppVerb(SourcePath input, VerificationRequest verificationRequest, bool releaseBuild = false)
        {
            if (input == null)
            {
                throw new ArgumentNullException("input");
            }

            this.abstractId = new AbstractId(GetType().Name, Version, input.ToString() + verificationRequest.ToString());
            this.input = input;
            this.buildVerb = new VSSolutionVerb(new SourcePath(@"src\IronfleetTestDriver\IronfleetTestDriver.sln"), input, releaseBuild);

            if (verificationRequest.verifyMode == VerificationRequest.VerifyMode.NoVerify)
            {
                this.exeOutput = this.input.makeOutputObject(UnverifiedExeExt);
                this.verifyVerb = null;
                this.verbs = new IVerb[] { this.buildVerb };
            }
            else
            {
                this.exeOutput = this.input.makeOutputObject(VerifiedExeExt);
                this.verifyVerb = new VerificationResultSummaryVerb(new DafnyVerifyTreeVerb(input));
                this.verbs = new IVerb[] { this.verifyVerb, this.buildVerb };
            }

            this.otherOutputs = new List<BuildObject>();
            var ohs = this.buildVerb.getOutputs().ToList();
            ohs.RemoveAll(o => o.getExtension() == ".exe");
            foreach (var o in ohs)
            {
                this.otherOutputs.Add(RelocateBuildObjectToExeDirectory(o));
            }
        }

        private BuildObject RelocateBuildObjectToExeDirectory(BuildObject sourceOb)
        {
            return new BuildObject(exeOutput.getDirPath() + "\\" + sourceOb.getFileName());
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            if (this.dependencies == null)
            {
                var dependencies = new List<BuildObject>();

                // Select and append results returned from verb.getDependencies() to dependencies.
                // If the dependency disposition is ever reported as not complete, we reflect this through to the caller.
                dependencies.AddRange(this.verbs.SelectMany(verb => verb.getOutputs()));
                this.dependencies = dependencies;
            }

            Trace.Assert(this.dependencies != null);
            ddisp = DependencyDisposition.Complete;
            return this.dependencies;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return this.verbs;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            var result = new List<BuildObject> { this.exeOutput };
            result.AddRange(this.otherOutputs);
            return result;
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            Disposition disposition = new Fresh();

            if (this.verifyVerb != null)
            {
                VerificationResult verificationResult = VerificationResult.fromXmlFile(this.verifyVerb.getOutputs().Single());
                if (!verificationResult.pass)
                {
                    disposition = new Failed();
                }
            }

            if (!(disposition is Failed))
            {
                foreach (var o in this.buildVerb.getOutputs())
                {
                    if (o.getExtension() == ".exe")
                    {
                        File.Copy(workingDirectory.PathTo(o), workingDirectory.PathTo(this.exeOutput), overwrite: true);
                    }
                    else
                    {
                        var dest = this.RelocateBuildObjectToExeDirectory(o);
                        File.Copy(
                            workingDirectory.PathTo(o),
                            workingDirectory.PathTo(dest),
                            overwrite: true);
                    }
                }
            }

            return new VerbSyncWorker(workingDirectory, disposition);
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public Disposition Complete(WorkingDirectory workingDirectory, double cpuTimeSeconds, string stdout, string stderr, Disposition disposition)
        {           
            return disposition;
        }

        public BuildObject getObligationSet()
        {
            return this.verifyVerb.getObligationSet();
        }
    }
}
