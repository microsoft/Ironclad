//--
// <copyright file="PresentationBuilder.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Text;
    using System.Xml;

    internal class PresentationBuilder
    {
        // Build-up interface.
        private StringBuilder sb;
        private XmlWriter xw;

        public PresentationBuilder()
        {
            this.sb = new StringBuilder();

            // Notice no indentation, to avoid mungling text.
            this.xw = XmlWriter.Create(this.sb);
            this.xw.WriteStartDocument();
            this.xw.WriteStartElement(Presentation._xml_tag);
        }

        public Presentation fix()
        {
            this.xw.WriteEndElement();
            this.xw.WriteEndDocument();
            this.xw.Close();
            return new Presentation(this.sb.ToString());
        }

        public void text(string s)
        {
            this.xw.WriteString(s);
        }

        public void color(string color, string s)
        {
            this.xw.WriteStartElement(Presentation.COLOR);
            this.xw.WriteAttributeString(Presentation._xml_ColorValue_attr, color);
            this.text(s);
            this.xw.WriteEndElement();
        }

        public void header(string s)
        {
            this.simpleTag(Presentation.HEADER, s);
        }

        public void line(string s)
        {
            this.simpleTag(Presentation.LINE, s);
        }

        public void spacer()
        {
            this.simpleTag(Presentation.SPACER, string.Empty);
        }

        public void bullet(string s)
        {
            this.simpleTag(Presentation.BULLET, s);
        }

        public void pre(string s)
        {
            this.simpleTag(Presentation.PRE, s);
        }

        public void startHeader()
        {
            this.xw.WriteStartElement(Presentation.HEADER);
        }

        public void endHeader()
        {
            this.xw.WriteEndElement();
        }

        public void startLine()
        {
            this.xw.WriteStartElement(Presentation.LINE);
        }

        public void endLine()
        {
            this.xw.WriteEndElement();
        }

        public void startBullet()
        {
            this.xw.WriteStartElement(Presentation.BULLET);
        }

        public void endBullet()
        {
            this.xw.WriteEndElement();
        }

        private void simpleTag(string tag, string s)
        {
            this.xw.WriteStartElement(tag);
            this.text(s);
            this.xw.WriteEndElement();
        }
    }
}
