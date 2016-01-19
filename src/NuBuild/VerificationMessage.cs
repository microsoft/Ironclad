//--
// <copyright file="VerificationMessage.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Xml;

    internal class VerificationMessage
    {
        public const string _xml_tag = "VerificationMessage";
        private const string _xml_message_sourcefile_attr = "SourceFile";

        private string sourceLabel;
        private string message;

        public VerificationMessage(string sourceLabel, string message)
        {
            this.sourceLabel = sourceLabel;
            this.message = message;
        }

        public string SourceLabel
        {
            get { return this.sourceLabel; }
        }

        public string Message
        {
            get { return this.message; }
        }

        public static VerificationMessage ReadXml(XmlReader xr)
        {
            Util.Assert(xr.Name.Equals(VerificationMessage._xml_tag));
            string relSourcePath = xr.GetAttribute(VerificationMessage._xml_message_sourcefile_attr);
            string message = xr.ReadElementContentAsString();
            return new VerificationMessage(relSourcePath, message);
        }

        public void WriteXml(XmlWriter xw)
        {
            xw.WriteStartElement(VerificationMessage._xml_tag);
            xw.WriteAttributeString(VerificationMessage._xml_message_sourcefile_attr, this.sourceLabel);
            xw.WriteString(this.message);
            xw.WriteEndElement();
        }
    }
}
