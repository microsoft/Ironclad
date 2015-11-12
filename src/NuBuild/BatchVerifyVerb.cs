//--
// <copyright file="BatchVerifyVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;

    internal class BatchVerifyVerb
        : Verb, IObligationsProducer
    {
        private const string BATCH_EXTN = ".batch";
        private const int version = 1;

        private BuildObject outputObject;
        private HashSet<IObligationsProducer> producers;
        private AbstractId abstractId;
        private BatchMode mode;  // REVIEW: Never used?
        private List<BuildObject> deps;

        public BatchVerifyVerb(SourcePath batch_file, BatchMode mode, VerificationRequest verificationRequest, DafnyCCVerb.FramePointerMode useFramePointer)
        {
            this.mode = mode;

            this.producers = new HashSet<IObligationsProducer>();
            foreach (string line in File.ReadAllLines(IronRootDirectory.PathTo(batch_file)))
            {
                if (line.Equals("") || line[0] == '#')
                {
                    continue;
                }

                SourcePath src = new SourcePath(line);
                switch (mode)
                {
                    case BatchMode.DAFNY:
                        if (verificationRequest.verifyMode != VerificationRequest.VerifyMode.Verify)
                        {
                            throw new UserError("BatchVerify DAFNY only supports full verification (but maybe we should add selective?)");
                        }

                        this.producers.Add(new DafnyVerifyTreeVerb(src));
                        break;
                    case BatchMode.APP:
                        this.producers.Add(new IroncladAppVerb(src, IroncladAppVerb.TARGET.BARE_METAL, useFramePointer, verificationRequest));
                        break;
                    default:
                        throw new Exception("Unknown batch file type");
                }
            }

            string parameters = mode.ToString() + "," + verificationRequest.ToString();
            this.outputObject = batch_file.makeLabeledOutputObject(parameters, BATCH_EXTN + VerificationObligationList.VOL_EXTN);
            this.abstractId = new AbstractId(this.GetType().Name, version, batch_file.ToString(), concrete: parameters);
        }

        public BatchVerifyVerb(BuildObject batch_label, HashSet<IObligationsProducer> producers, BatchMode mode)
        {
            this.mode = mode;
            this.producers = producers;

            this.outputObject = batch_label.makeOutputObject(BATCH_EXTN + VerificationObligationList.VOL_EXTN);
            this.abstractId = new AbstractId(this.GetType().Name, version, batch_label.ToString(), concrete: mode.ToString());
        }

        public enum BatchMode
        {
            DAFNY,
            APP
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public BuildObject getObligationSet()
        {
            return this.outputObject;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            if (this.deps == null)
            {
                this.deps = new List<BuildObject>();
                foreach (IObligationsProducer producer in this.producers)
                {
                    this.deps.Add(producer.getObligationSet());
                }
            }

            ddisp = DependencyDisposition.Complete;
            return this.deps;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            // Pass this request upstream to expose upstream verbs.
            HashSet<IVerb> upstreamVerbs = new HashSet<IVerb>();
            foreach (IVerb producer in this.producers)
            {
                upstreamVerbs.UnionWith(producer.getVerbs());
                upstreamVerbs.Add(producer);
            }

            return upstreamVerbs;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new HashSet<BuildObject>() { this.outputObject };
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            // Coallesce the VerificationObligationLists from each producer into a single result set
            IEnumerable<BuildObject> master = new HashSet<BuildObject>();
            foreach (IObligationsProducer producer in this.producers)
            {
                VerificationObligationList vol = VerificationObligationList.fetch(producer.getObligationSet());
                master = master.Union(vol.getVerificationObligations());
            }

            VerificationObligationList myVOL = new VerificationObligationList(master);
            myVOL.store(workingDirectory, this.outputObject);
            return new VerbSyncWorker(workingDirectory, new Fresh());
        }
    }
}
