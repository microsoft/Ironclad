//--
// <copyright file="VerificationResultVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    internal abstract class VerificationResultVerb
        : Verb, IRejectable
    {
        public const string VERIFICATION_RESULT_EXTN = ".v";

        private bool dbgWasVerificationTimeoutRecorded;
        private bool wasRejectableFailure;

        public abstract BuildObject getOutputFile();

        public override Presentation getRealtimePresentation(Disposition d)
        {
            if (d is Failed)
            {
                return base.getRealtimePresentation(d);
            }

            VerificationResult vr = VerificationResult.fromXmlFile(this.getOutputFile());
            PresentationBuilder pr = new PresentationBuilder();
            pr.startLine();
            pr.color(
                vr.pass ? Presentation.GREEN : Presentation.RED,
                string.Format(
                    "{0} {1} {2,5:0.0}s",
                    ////getSource().getRelativePath(),
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
            VerificationResult vr = VerificationResult.fromXmlFile(this.getOutputFile());
            return vr.presentation;
        }

        public bool resultWasRejectableFailure()
        {
            Util.Assert(this.dbgWasVerificationTimeoutRecorded);
            return this.wasRejectableFailure;
        }

        protected abstract BuildObject getSource();

        protected void setWasRejectableFailure(bool value)
        {
            this.dbgWasVerificationTimeoutRecorded = true;
            this.wasRejectableFailure = value;
        }
    }
}
