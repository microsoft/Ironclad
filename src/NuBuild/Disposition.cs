//--
// <copyright file="Disposition.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Xml;

    internal class Disposition
    {
        public const string _xml_tag = "Disposition";
        private const string _xml_value_attr = "Value";

        public static Disposition readXml(XmlReader xr)
        {
            Util.Assert(xr.Name.Equals(_xml_tag));
            string value = xr.GetAttribute(_xml_value_attr);
            if (value.Equals(Fresh.Value))
            {
                return new Fresh();
            }
            else if (value.Equals(Failed.Value))
            {
                return Failed.readXml(xr);
            }
            else
            {
                throw new Exception("Invalid disposition value " + value);
            }
        }

        public virtual IEnumerable<string> getMessages()
        {
            return new string[0];
        }

        public virtual void writeXml(XmlWriter xw)
        {
            xw.WriteStartElement(_xml_tag);
            xw.WriteAttributeString(_xml_value_attr, ToString());
            this.writeXmlExtend(xw);
            xw.WriteEndElement();
        }

        protected virtual void writeXmlExtend(XmlWriter xw)
        {
        }
    }

    internal class Stale : Disposition
    {
        public const string Value = "Stale";

        public override string ToString()
        {
            return Value;
        }
    }

    internal class Fresh : Disposition
    {
        public const string Value = "Fresh";

        public override string ToString()
        {
            return Value;
        }
    }

    /// <summary>
    /// Failed represents a PERMANENT failure. Any non-Stale disposition is recorded
    /// permanently in the build cache (including the globally-shared build cache!),
    /// preventing that particular verb from ever being tried again. Only record a
    /// Failed disposition if repeating the verb is guaranteed to fail again the same way.
    /// </summary>
    internal class Failed : Disposition
    {
        public const string Value = "Failed";
        private const string _xml_MessageTag = "Message";

        private List<string> messages;

        public Failed(string msg = null)
        {
            this.messages = new List<string>();
            if (msg != null)
            {
                this.AddError(msg);
            }
        }

        public Failed(IEnumerable<string> messages)
        {
            this.messages = new List<string>(messages);
        }

        public static new Disposition readXml(XmlReader xr)
        {
            List<string> messages = new List<string>();
            if (!xr.IsEmptyElement)
            {
                while (xr.Read())
                {
                    if (xr.NodeType == XmlNodeType.Element)
                    {
                        if (xr.Name.Equals(_xml_MessageTag))
                        {
                            messages.Add(xr.ReadElementContentAsString());
                        }
                        else
                        {
                            throw new Exception("Unrecognized Disposition::Failed tag " + xr.Name);
                        }
                    }
                    else if (xr.NodeType == XmlNodeType.EndElement)
                    {
                        Util.Assert(xr.Name.Equals(Disposition._xml_tag));
                        break;
                    }
                }
            }

            Failed f = new Failed();
            f.messages = messages;
            return f;
        }

        public void AddError(string msg)
        {
            this.messages.Add(msg);
        }

        public override string ToString()
        {
            return Failed.Value;
        }

        public override IEnumerable<string> getMessages()
        {
            return this.messages;
        }

        protected override void writeXmlExtend(XmlWriter xw)
        {
            foreach (string message in this.messages)
            {
                xw.WriteStartElement(_xml_MessageTag);
                xw.WriteString(message);
                xw.WriteEndElement();
            }
        }
    }
}
