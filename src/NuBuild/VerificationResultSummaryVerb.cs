//--
// <copyright file="VerificationResultSummaryVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

    internal class VerificationResultSummaryVerb
        : VerificationResultVerb ////, IObligationsProducer
    {
        private const string SUMMARY_EXTN = ".summary";
        private const int version = 4;

        private BuildObject outputObject;
        private IObligationsProducer producer;
        private IEnumerable<BuildObject> verificationResults;
        private AbstractId abstractId;

        public VerificationResultSummaryVerb(IObligationsProducer producer) 
        {
            this.producer = producer;
            BuildObject id = producer.getObligationSet(); ////producer.getIdentifier();
            this.outputObject = id.makeOutputObject(id.getExtension() + SUMMARY_EXTN);
            this.abstractId = new AbstractId(this.GetType().Name, version, id.ToString());
            this.verificationResults = null;
        }

        public override AbstractId getAbstractIdentifier()
        {
            return this.abstractId;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            BuildObject obligations = this.producer.getObligationSet();
            HashSet<BuildObject> deps = new HashSet<BuildObject>();
            deps.Add(obligations);

            try
            {
                VerificationObligationList vol = VerificationObligationList.fetch(obligations);
                this.verificationResults = vol.getVerificationObligations();
                deps.UnionWith(this.verificationResults);
                ddisp = DependencyDisposition.Complete;
            }
            catch (ObjectNotReadyException)
            {
                ddisp = DependencyDisposition.Incomplete;
            }
            catch (ObjectFailedException)
            {
                ddisp = DependencyDisposition.Failed;
            }

            return deps;
        }

        public override IEnumerable<IVerb> getVerbs() 
        {
            IEnumerable<IVerb> verbs = new IVerb[] { this.producer };

            verbs = verbs.Union(this.producer.getVerbs());
            return verbs;

            // VerificationResultSummaryVerb depends on objects mentioned by producer,
            // but the necessary verbs haven't been mentioned. Is it sufficient for
            // the upstream guy (BoogieAsmVerificationObligationList) to ... hopefully ...
            // mention them? (Hopefully because he might only be incompletely queried,
            // since he's not actually dependent on the verbs he's advertising.)
            // Maybe we should provide a way for his complete() method to push the
            // verbs into the cache.
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new HashSet<BuildObject>() { this.outputObject };
        }

        public override BuildObject getOutputFile()
        {
            return this.outputObject;
        }

        public BuildObject getObligationSet()
        {
            return this.producer.getObligationSet();
        }

        public override IVerbWorker getWorker(WorkingDirectory workingDirectory)
        {
            // Read and aggregate all the input results.
            int parseFailures = 0;
            int verificationFailures = 0;
            int timeouts = 0;
            int filesWithParseFailures = 0;
            int filesWithVerificationFailures = 0;
            int filesWithTimeouts = 0;
            int passCount = 0;
            int failCount = 0;
            double cpuTime = 0;
            List<VerificationMessage> failMessages = new List<VerificationMessage>();
            List<VerificationResult> results = new List<VerificationResult>();

            // REVIEW: Why pull out the enumerator this way?
            IEnumerable<BuildObject> verificationResultsEnumerator = this.verificationResults;
            foreach (BuildObject verificationResult in verificationResultsEnumerator)
            {
                VerificationResult vr = VerificationResult.fromXmlFile(verificationResult);
                results.Add(vr);
                if (vr == null)
                {
                    return new VerbSyncWorker(
                        workingDirectory,
                        new Failed("Build system broke: missing VerificationResult for " + verificationResult));
                }

                if (vr.pass)
                {
                    passCount += 1;
                }
                else
                {
                    failCount += 1;
                    failMessages.AddRange(vr.getMessages());
                }

                parseFailures += vr.parseFailures;
                verificationFailures += vr.verificationFailures;
                timeouts += vr.timeouts;
                filesWithParseFailures += vr.parseFailures > 0 ? 1 : 0;
                filesWithVerificationFailures += vr.verificationFailures > 0 ? 1 : 0;
                filesWithTimeouts += vr.timeouts > 0 ? 1 : 0;
                ////Logger.WriteLine("Synthesizing cpuTime from " + verificationResult);
                cpuTime += vr.cpuTime;
            }

            bool allPass = failCount == 0;

            PresentationBuilder pr = new PresentationBuilder();

            int any_failures = parseFailures + verificationFailures + timeouts;
            string overall_status = any_failures > 0 ? "Fail" : "Success";

            pr.pre(VerificationResult._VERIFICATION_RESULT_PLACEHOLDER+"\n");
            pr.spacer();
            pr.startHeader();
            pr.color(this.colorByFailureCount(any_failures), "Overall status: " + overall_status);
            pr.endHeader();
            pr.line("Count of files with failures: " + failCount);
            pr.startBullet();
            pr.color(this.colorByFailureCount(filesWithParseFailures), "Files with parse failures: " + filesWithParseFailures.ToString());
            pr.endBullet();
            pr.startBullet();
            pr.color(this.colorByFailureCount(filesWithVerificationFailures), "Files with verification failures: " + filesWithVerificationFailures.ToString());
            pr.endBullet();
            pr.startBullet();
            pr.color(this.colorByFailureCount(filesWithTimeouts), "Files with timeouts: " + filesWithTimeouts.ToString());
            pr.endBullet();

            pr.spacer();
            pr.header(string.Format("Total processing time: {0:0.0}s {1}", cpuTime, new TimeSpan((long)(cpuTime * 10000000L))));
            int top_n = 10;
            pr.header(string.Format("Slowest {0} verifications:", top_n));

            results.Sort(this.ByCpuTimeDecreasing);
            foreach (VerificationResult slowResult in results.Take(top_n))
            {
                pr.startBullet();
                pr.color(
                    this.colorByFailureCount(slowResult.pass ? 0 : 1),
                    string.Format("{0,6:##0.0}s {1}", slowResult.cpuTime, slowResult.sourceLabel));
                pr.endBullet();
            }

            foreach (VerificationMessage message in failMessages)
            {
                pr.spacer();
                pr.header("Failure with " + message.SourceLabel);
                pr.pre(message.Message);
            }

            Presentation pres = pr.fix();

            VerificationResult outvr = new VerificationResult("summary", allPass, cpuTime, parseFailures, verificationFailures, timeouts, failMessages);
            outvr.addXmlFiller(pres);
            outvr.toXmlFile(workingDirectory.PathTo(this.outputObject));
            this.setWasRejectableFailure(!outvr.pass);
            return new VerbSyncWorker(workingDirectory, new Fresh());
        }
        
        public override Presentation getRealtimePresentation(Disposition d)
        {
            if (d is Failed)
            {
                return base.getRealtimePresentation(d);
            }

            VerificationResult vr = VerificationResult.fromXmlFile(this.outputObject);
            PresentationBuilder pr = new PresentationBuilder();
            pr.startLine();
            pr.color(
                vr.pass ? Presentation.GREEN : Presentation.RED,
                string.Format(
                    "{0} {1} {2,1:0.0}s",
                    this.getAbstractIdentifier(),
                    vr.pass ? "Success" : "Fail",
                    vr.cpuTime));
            pr.endLine();
            if (!vr.pass)
            {
                foreach (VerificationMessage msg in vr.getMessages())
                {
                    pr.pre(msg.Message);
                }
            }

            return pr.fix();
        }        

        public override Presentation getPresentation()
        {
            VerificationResult vr = VerificationResult.fromXmlFile(this.outputObject);
            return vr.presentation;
        }

        protected override BuildObject getSource()
        {
            return this.producer.getObligationSet();
        }

        private int ByCpuTimeDecreasing(VerificationResult va, VerificationResult vb)
        {
            return -(va.cpuTime.CompareTo(vb.cpuTime));
        }

        private string colorByFailureCount(int count)
        {
            return count == 0 ? Presentation.GREEN : Presentation.RED;
        }
    }
}
