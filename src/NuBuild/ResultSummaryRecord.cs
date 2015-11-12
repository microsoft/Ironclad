//--
// <copyright file="ResultSummaryRecord.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Text;
    using System.Xml;

    /// <summary>
    /// Representation of the result of a particular verb's execution.
    /// </summary>
    public class ResultSummaryRecord
    {
        /// <summary>
        /// The XML element name for this object.
        /// </summary>
        public const string XmlTag = "ResultSummaryRecord";

        /// <summary>
        /// The XML attribute name for the IsVerificationTimeout value.
        /// </summary>
        public const string XmlIsVerificationTimeoutAttribute = "IsVerificationTimeout";

        /// <summary>
        /// The verb whose execution this is the result of.
        /// </summary>
        private IVerb verb;

        /// <summary>
        /// The disposition of the verb execution.
        /// </summary>
        private Disposition disposition;

        /// <summary>
        /// Whether this result is a rejectable failure.
        /// </summary>
        private bool isRejectableFailure;

        /// <summary>
        /// The build objects that were produced by this verb execution.
        /// </summary>
        private List<BuildObjectValuePointer> outputs;

        /// <summary>
        /// Initializes a new instance of the ResultSummaryRecord class.
        /// </summary>
        /// <param name="verb">
        /// The verb whose execution this is the result of.
        /// </param>
        /// <param name="disposition">
        /// The disposition of the verb execution.
        /// </param>
        /// <param name="outputs">
        /// The build objects that were produced by this verb execution.
        /// </param>
        internal ResultSummaryRecord(
            IVerb verb,
            Disposition disposition,
            IEnumerable<BuildObjectValuePointer> outputs)
            : this(verb, disposition, outputs, false)
        {
        }

        /// <summary>
        /// Initializes a new instance of the ResultSummaryRecord class.
        /// </summary>
        /// <param name="disposition">
        /// The disposition of the verb execution.
        /// </param>
        /// <param name="outputs">
        /// The build objects that were produced by this verb execution.
        /// </param>
        /// <param name="isVerificationTimeout">
        /// Whether this result is a verification timeout.
        /// </param>
        internal ResultSummaryRecord(
            Disposition disposition,
            IEnumerable<BuildObjectValuePointer> outputs,
            bool isVerificationTimeout)
            : this(null, disposition, outputs, isVerificationTimeout)
        {
        }

        /// <summary>
        /// Initializes a new instance of the ResultSummaryRecord class.
        /// </summary>
        /// <param name="verb">
        /// The verb whose execution this is the result of.
        /// </param>
        /// <param name="disposition">
        /// The disposition of the verb execution.
        /// </param>
        /// <param name="outputs">
        /// The build objects that were produced by this verb execution.
        /// </param>
        /// <param name="isRejectableFailure">
        /// Whether this result is a rejectable failure.
        /// </param>
        internal ResultSummaryRecord(
            IVerb verb,
            Disposition disposition,
            IEnumerable<BuildObjectValuePointer> outputs,
            bool isRejectableFailure)
        {
            this.verb = verb;
            this.disposition = disposition;
            this.outputs = new List<BuildObjectValuePointer>(outputs);
            this.isRejectableFailure = isRejectableFailure;

            IRejectable rejectableVerb = verb as IRejectable;
            if (rejectableVerb != null)
            {
                this.isRejectableFailure = rejectableVerb.resultWasRejectableFailure();
            }
        }

        /// <summary>
        /// Gets a value indicating whether this result is a failure of
        /// some sort (includes verification timeouts).
        /// </summary>
        public bool IsFailure
        {
            get { return this.isRejectableFailure || (this.disposition is Failed); }
        }

        /// <summary>
        /// Gets a value indicating whether this result is a verification
        /// timeout.
        /// </summary>
        public bool IsVerificationTimeout
        {
            get { return this.isRejectableFailure; }
        }

        /// <summary>
        /// Gets the build objects that were produced by this verb execution.
        /// </summary>
        public IEnumerable<BuildObjectValuePointer> Outputs
        {
            get { return this.outputs; }
        }

        /// <summary>
        /// Gets the disposition of the verb execution.
        /// </summary>
        internal Disposition Disposition
        {
            get { return this.disposition; }
        }

        /// <summary>
        /// Creates a result record from an XML representation.
        /// </summary>
        /// <param name="xs">
        /// A string containing an XML document representing this result record.
        /// </param>
        /// <returns>
        /// A new result record corresponding to the XML representation read.
        /// </returns>
        public static ResultSummaryRecord FromXml(string xs)
        {
            XmlReader xr = XmlReader.Create(new StringReader(xs));
            while (xr.Read())
            {
                if (xr.NodeType == XmlNodeType.Element)
                {
                    break;
                }
            }

            return ReadXml(xr);
        }

        /// <summary>
        /// Helper function to read an XML element (not a full document)
        /// representing a result record.
        /// </summary>
        /// <remarks>
        /// Note that the XmlReader is expected to be positioned in the XML
        /// document such that the current node is a result record element.
        /// </remarks>
        /// <param name="xr">The XmlReader object to read from.</param>
        /// <returns>
        /// A new result record corresponding to the XML representation read.
        /// </returns>
        public static ResultSummaryRecord ReadXml(XmlReader xr)
        {
            Util.Assert(xr.Name.Equals(ResultSummaryRecord.XmlTag));

            bool isVerificationTimeout = false;
            bool.TryParse(
                xr.GetAttribute(XmlIsVerificationTimeoutAttribute), out isVerificationTimeout);

            xr.ReadToFollowing(Disposition._xml_tag);
            Disposition d = Disposition.readXml(xr);

            List<BuildObjectValuePointer> lbovp = new List<BuildObjectValuePointer>();
            while (xr.Read())
            {
                if (xr.NodeType == XmlNodeType.EndElement)
                {
                    Util.Assert(xr.Name.Equals(ResultSummaryRecord.XmlTag));
                    break;
                }
                else if (xr.NodeType == XmlNodeType.Element)
                {
                    if (xr.Name.Equals(BuildObjectValuePointer.XmlTag))
                    {
                        lbovp.Add(BuildObjectValuePointer.ReadXml(xr));
                    }
                    else
                    {
                        throw new Exception("Unknown xml tag " + xr.Name);
                    }
                }
            }

            return new ResultSummaryRecord(d, lbovp, isVerificationTimeout);
        }

        /// <summary>
        /// Creates an XML document representing this result record.
        /// </summary>
        /// <returns>
        /// A string containing an XML document representing this result record.
        /// </returns>
        public string ToXml()
        {
            StringBuilder sb = new StringBuilder();
            XmlWriterSettings settings = new XmlWriterSettings();
            settings.Indent = true;
            XmlWriter xw = XmlWriter.Create(sb, settings);
            xw.WriteStartDocument();
            this.WriteXml(xw);
            xw.Close();
            return sb.ToString();
        }

        /// <summary>
        /// Helper function to write an XML element (not a full document)
        /// representing this result record.
        /// </summary>
        /// <param name="xw">The XmlWriter object to write to.</param>
        public void WriteXml(XmlWriter xw)
        {
            xw.WriteStartElement(XmlTag);
            xw.WriteAttributeString(
                ResultSummaryRecord.XmlIsVerificationTimeoutAttribute,
                this.isRejectableFailure.ToString());

            if (this.verb != null)
            {
                this.verb.writeTimingXml(xw);
                this.verb.writeDebugXml(xw);
            }

            this.disposition.writeXml(xw);

            foreach (BuildObjectValuePointer bovp in this.outputs)
            {
                bovp.WriteXml(xw);
            }

            xw.WriteEndElement();
        }
    }
}
