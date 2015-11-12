//--
// <copyright file="VerificationResult.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
using System;
using System.Collections.Generic;
using System.IO;
using System.Text.RegularExpressions;
    using System.Xml;

    internal class VerificationResult
{
	public const string _VERIFICATION_RESULT_PLACEHOLDER = "_VERIFICATION_RESULT_PLACEHOLDER";

        public const string _xml_tag = "VerificationResult";

        private const string _xml_sourcePath_attr = "SourcePath";
        private const string _xml_outcome_attr = "Outcome";
        private const string _xml_parseFailures_attr = "ParseFailures";
        private const string _xml_verificationFailures_attr = "VerificationFailures";
        private const string _xml_timeouts_attr = "Timeouts";
        private const string _xml_cputime_attr = "CPUTime";
        private const string _xml_message_tag = "Message";
        private const string _xml_message_sourcefile_attr = "SourceFile";

        private const string PASS = "pass";
        private const string FAIL = "fail";

        private static Regex whitespace = new Regex("^\\s*$");

        private string _sourceLabel;
        private bool _pass;
        private double _cpuTime;
        private int _parseFailures;
        private int _verificationFailures;
        private int _timeouts;
        private List<VerificationMessage> messages;
        private Presentation _presentation;

        public VerificationResult(string sourceLabel, double cpuTime, string stdout, string stderr, IVerificationResultParser parser)
        {
            this._sourceLabel = sourceLabel;
            this._cpuTime = cpuTime;
            this.messages = new List<VerificationMessage>();

            // REVIEW: Switch from whitespace Regex to string.IsNullOrWhiteSpace()?
            if (!whitespace.Match(stdout).Success)
            {
                this.messages.Add(new VerificationMessage(sourceLabel, stdout));
            }

            if (!whitespace.Match(stderr).Success)
            {
                this.messages.Add(new VerificationMessage(sourceLabel, stderr));
            }

            this._parseFailures = 0;
            this._verificationFailures = 0;
            this._timeouts = 0;
            parser.parseOutput(stdout + stderr, out this._parseFailures, out this._verificationFailures, out this._timeouts);
            this._pass = this._parseFailures == 0 && this._verificationFailures == 0 && this._timeouts == 0;
        }

        public VerificationResult(string sourceLabel, bool pass, double cpuTime, int parseFailures, int verificationFailures, int timeouts, IEnumerable<VerificationMessage> messages)
        {
            this._sourceLabel = sourceLabel;
            this._pass = pass;
            this._cpuTime = cpuTime;
            this._parseFailures = parseFailures;
            this._verificationFailures = verificationFailures;
            this._timeouts = timeouts;
            this.messages = new List<VerificationMessage>(messages);
        }

        private VerificationResult()
        {
        }

        public string sourceLabel
        {
            get { return this._sourceLabel; }
        }

        public bool pass
        {
            get { return this._pass; }
        }

        public double cpuTime
        {
            get { return this._cpuTime; }
        }

        public int parseFailures
        {
            get { return this._parseFailures; }
        }

        public int verificationFailures
        {
            get { return this._verificationFailures; }
        }

        public int timeouts
            {
            get { return this._timeouts; }
            }

        public Presentation presentation
        {
            get { return this._presentation; }
        }

        public static VerificationResult fromXmlFile(BuildObject obj)
        {
            using (TextReader ins = BuildEngine.theEngine.Repository.OpenRead(obj))
            {
                XmlReader xr = XmlReader.Create(ins);
                while (xr.Read())
                {
                    if (xr.NodeType == XmlNodeType.Element)
                    {
                        break;
                    }
                }

                return readXml(xr);
            }
        }

        public static VerificationResult readXml(XmlReader xr)
        {
            Util.Assert(xr.Name.Equals(_xml_tag));
            VerificationResult rc = new VerificationResult();
            rc._sourceLabel = xr.GetAttribute(_xml_sourcePath_attr);
            string outcome = xr.GetAttribute(_xml_outcome_attr);
            if (outcome.Equals(PASS))
            {
                rc._pass = true;
            }
            else if (outcome.Equals(FAIL))
            {
                rc._pass = false;
            }
            else
            {
                throw new Exception("Invalid outcome value " + outcome);
            }

            rc._cpuTime = Double.Parse(xr.GetAttribute(_xml_cputime_attr));
            rc._parseFailures = Int32.Parse(xr.GetAttribute(_xml_parseFailures_attr));
            rc._verificationFailures = Int32.Parse(xr.GetAttribute(_xml_verificationFailures_attr));
            rc._timeouts = Int32.Parse(xr.GetAttribute(_xml_timeouts_attr));
            rc.messages = new List<VerificationMessage>();

            while (xr.Read())
            {
                if (xr.NodeType == XmlNodeType.EndElement)
                {
                    Util.Assert(xr.Name.Equals(_xml_tag));
                    break;
                }
                else if (xr.NodeType == XmlNodeType.Element)
                {
                    if (xr.Name.Equals(VerificationMessage._xml_tag))
                    {
                        rc.messages.Add(VerificationMessage.ReadXml(xr));
                    }
                    else if (xr.Name.Equals(Presentation._xml_tag))
                    {
                        rc._presentation = Presentation.fromXml(xr.ReadSubtree());
                    }
                    else
                    {
                        throw new Exception("Unknown xml tag " + xr.Name);
                    }
                }
            }

            return rc;
        }

        public IEnumerable<VerificationMessage> getMessages()
        {
            return this.messages;
        }

        public void addXmlFiller(Presentation presentation)
        {
            this._presentation = presentation;
        }

        public void toXmlFile(string path)
        {
            File.Delete(path);
            using (FileStream s = File.OpenWrite(path))
            {
                XmlWriterSettings settings = new XmlWriterSettings();
                settings.Indent = true;
                XmlWriter xw = XmlWriter.Create(s, settings);
                xw.WriteStartDocument();
                this.writeXml(xw);
                xw.Close();
            }
        }

        public void writeXml(XmlWriter xw)
        {
            xw.WriteStartElement(_xml_tag);
            xw.WriteAttributeString(_xml_sourcePath_attr, this._sourceLabel);
            xw.WriteAttributeString(_xml_outcome_attr, this._pass ? PASS : FAIL);
            xw.WriteAttributeString(_xml_cputime_attr, this._cpuTime.ToString());
            xw.WriteAttributeString(_xml_parseFailures_attr, this._parseFailures.ToString());
            xw.WriteAttributeString(_xml_verificationFailures_attr, this._verificationFailures.ToString());
            xw.WriteAttributeString(_xml_timeouts_attr, this._timeouts.ToString());
            foreach (VerificationMessage message in this.messages)
            {
                message.WriteXml(xw);
            }

            if (this._presentation != null)
            {
                this._presentation.fillXml(xw);  // TODO we don't know yet how to parse this stuff back in.
            }

            xw.WriteEndElement();
        }

        public void addBasicPresentation()
        {
            PresentationBuilder pr = new PresentationBuilder();

            int any_failures = this.parseFailures + this.verificationFailures + this.timeouts;
            string overall_status = any_failures > 0 ? "Fail" : "Success";

            pr.pre(_VERIFICATION_RESULT_PLACEHOLDER+"\n");
            pr.spacer();
            pr.startHeader();
            pr.color(any_failures == 0 ? Presentation.GREEN : Presentation.RED, "Overall status: " + overall_status);
            pr.endHeader();
            pr.line(
                string.Format(
                    "{0} parse failures, {1} verification failures, {2} timeouts",
                    this._parseFailures,
                    this._verificationFailures,
                    this._timeouts));
            pr.spacer();

            foreach (VerificationMessage message in this.messages)
            {
                pr.pre(message.Message);
            }

            Presentation pres = pr.fix();
            this.addXmlFiller(pres);
        }

        internal bool wasOnlyTimeouts()
        {
            return this.verificationFailures == 0 && this.timeouts > 0;
        }
    }
}
