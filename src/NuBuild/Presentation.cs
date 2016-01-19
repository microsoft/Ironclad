//--
// <copyright file="Presentation.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.IO;
    using System.Text;
    using System.Xml;

    internal class Presentation : XmlFiller
    {
        // Completed representation.
        private string xmls;

        public const string _xml_tag = "Presentation";
        public const string HEADER = "Header";
        public const string LINE = "Line";
        public const string SPACER = "Spacer";
        public const string COLOR = "Color";
        public const string BULLET = "Bullet";
        public const string PRE = "Pre";

        public const string RED = "red";
        public const string GREEN = "green";

        public const string _xml_ColorValue_attr = "Value";

        public Presentation(string xmls)
        {
            this.xmls = xmls;
        }

        public static Presentation fromXml(XmlReader xr)
        {
            StringBuilder sb = new StringBuilder();
            using (XmlWriter xw = XmlWriter.Create(sb))
            {
                xw.WriteStartDocument();
                xw.WriteNode(xr, false);
                xw.WriteEndDocument();
                xw.Close();
            }

            return new Presentation(sb.ToString());
        }

        public void fillXml(XmlWriter xw)
        {
            using (XmlReader xr = XmlReader.Create(new StringReader(this.xmls)))
            {
                xr.ReadToFollowing(_xml_tag);
                xw.WriteNode(xr, false);
            }
        }

        public void format(Presentater p)
        {
            using (XmlReader xr = XmlReader.Create(new StringReader(this.xmls)))
            {
                xr.ReadToFollowing(_xml_tag);
                while (xr.Read())
                {
                    if (xr.NodeType == XmlNodeType.Element)
                    {
                        switch (xr.Name)
                        {
                            case HEADER:
                                p.startHeader();
                                break;
                            case LINE:
                                p.startLine();
                                break;
                            case SPACER:
                                p.startSpacer();
                                break;
                            case COLOR:
                                p.startColor(xr.GetAttribute(_xml_ColorValue_attr));
                                break;
                            case BULLET:
                                p.startBullet();
                                break;
                            case PRE:
                                p.startPre();
                                break;
                            default:
                                Util.Assert(false);
                                break;
                        }
                    }
                    else if (xr.NodeType == XmlNodeType.EndElement)
                    {
                        switch (xr.Name)
                        {
                            case _xml_tag:
                                break;
                            case HEADER:
                                p.endHeader();
                                break;
                            case LINE:
                                p.endLine();
                                break;
                            case SPACER:
                                p.endSpacer();
                                break;
                            case COLOR:
                                p.endColor();
                                break;
                            case BULLET:
                                p.endBullet();
                                break;
                            case PRE:
                                p.endPre();
                                break;
                            default:
                                Util.Assert(false);
                                break;
                        }
                    }
                    else if (xr.NodeType == XmlNodeType.Text)
                    {
                        p.doText(xr.Value);
                    }
                }
            }
        }

        internal static string abbreviateLines(string m)
        {
            StringBuilder sb = new StringBuilder();
            int count = 0;
            const int limit = 20;
            using (StringReader sr = new StringReader(m))
            {
                string line;
                while ((line = sr.ReadLine()) != null)
                {
                    if (count == limit)
                    {
                        sb.AppendLine("[...error messages truncated. See failure log.]");
                        break;
                    }

                    sb.AppendLine(line);
                    count += 1;
                }
            }

            return sb.ToString();
        }
    }
}
