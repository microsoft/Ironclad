//--
// <copyright file="Presentater.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Text;

    /// <summary>
    /// TODO: Rename this (and the file) to IPresentater, or maybe IPresenter.
    /// REVIEW: These all just emit strings.  Wouldn't a simple table suffice?
    /// </summary>
    internal interface Presentater
    {
        void startHeader();

        void endHeader();

        void startLine();

        void endLine();

        void startSpacer();

        void endSpacer();

        void startColor(string colorName);

        void endColor();

        void startBullet();

        void endBullet();

        void startPre();

        void endPre();

        void doText(string text);
    }

    public class HTMLPresentater : Presentater
    {
        private StringBuilder document;

        public HTMLPresentater()
        {
            this.document = new StringBuilder();
            this.document.Append("<html>\n<body>\n");
        }

        public override string ToString()
        {
            this.document.Append("</body>\n</html>\n");
            return this.document.ToString();
        }

        public void startHeader()
        {
            this.document.Append("<h3><u>");
        }

        public void endHeader()
        {
            this.document.Append("</u></h3>");
        }

        public void startLine()
        {
            this.document.Append("<br>");
        }

        public void endLine()
        {
            this.document.Append("</br>\n");
        }

        public void startSpacer()
        {
            this.document.Append("<p>\n");
        }

        public void endSpacer()
        {
            this.document.Append("</p>\n");
        }

        public void startColor(string colorName)
        {
            string htmlColor;
            switch (colorName)
            {
                case Presentation.RED:
                    htmlColor = "red";
                    break;
                case Presentation.GREEN:
                    htmlColor = "green";
                    break;
                default: htmlColor = "black";
                    break;
            }

            this.document.Append("<font color=\"" + htmlColor + "\">");
        }

        public void endColor()
        {
            this.document.Append("</font>");
        }

        public void startBullet()
        {
            this.document.Append("<li>");
        }

        public void endBullet()
        {
            this.document.Append("</li>\n");
        }

        public void startPre()
        {
            this.document.Append("<pre>");
        }

        public void endPre()
        {
            this.document.Append("</pre>\n");
        }

        public void doText(string text)
        {
            this.document.Append(text);
        }
    }

    /// <summary>
    /// Appears to be a "Presentater" that uses "ANSI escape sequences" to
    /// produce colored output on console terminals that support it.
    /// </summary>
    /// <remarks>
    /// <para>
    /// "ANSI escape sequences" is probably the most common name for these
    /// things, although it is technically a misnomer, as ANSI withdrew the
    /// ANSI X3.64 spec in 1997.  The real spec is ECMA-48, aka ISO/IEC 6429.
    /// See <a href="http://www.ecma-international.org/publications/files/ECMA-ST/Ecma-048.pdf"/>.
    /// </para>
    /// <para>
    /// Windows <c>cmd.exe</c> doesn't implement this spec.  So only those folks
    /// using alternative shells will get easily-readable output from this.
    /// </para>
    /// </remarks>
    public class ASCIIPresentater : Presentater
    {
        // REVIEW: These don't appear to properly follow the ECMA-48 spec.
        // All of these commands are of type "Select Graphic Rendition" or SGR.
        // In the spec, this is covered in section 8.3.117. 
        // The 0 code is supposed to cancel the effect of any preceding SGR,
        // i.e. "\x1b[0m" should cancel everything.  Thus the following stop
        // codes don't just stop what their start codes started (and are overly
        // verbose).  A universal stop code would suffice for this usage.
        // Notes on codes used below:
        // 0 = cancel the effect of any preceding SGR.
        // 1 = bold.
        // 32 = green display (i.e. text).
        // 37 = white display (i.e. text).
        // 39 = default display (i.e. text) color.
        // 40 = black background.
        // 41 = red background.
        // 43 = yellow background.
        // 49 = default background color.
        private static ColorEnum Red = new ColorEnum("\x1b[01;41m", "\x1b[0;49m");
        private static ColorEnum Green = new ColorEnum("\x1b[01;32m", "\x1b[0;0m");
        private static ColorEnum BlackBackground = new ColorEnum("\x1b[01;40m", "\x1b[0;49m");
        private static ColorEnum YellowBackground = new ColorEnum("\x1b[01;43m", "\x1b[0;49m");
        private static ColorEnum BoldWhite = new ColorEnum("\x1b[01;37m", "\x1b[0;39m");
        private static ColorEnum WhiteOnBlack = ColorEnum.join(BlackBackground, BoldWhite);
        private static ColorEnum Ordinary = new ColorEnum(string.Empty, string.Empty);

        private StringBuilder document;
        private ColorEnum colorEnum;

        public ASCIIPresentater()
        {
            this.document = new StringBuilder();
        }

        public override string ToString()
        {
            return this.document.ToString();
        }

        public void startHeader()
        {
            this.document.Append(WhiteOnBlack.start);
        }

        public void endHeader()
        {
            this.document.Append(WhiteOnBlack.stop + "\n");
        }

        public void startLine()
        {
        }

        public void endLine()
        {
            this.document.Append("\n");
        }

        public void startSpacer()
        {
        }

        public void endSpacer()
        {
            this.document.Append("\n");
        }

        public void startColor(string colorName)
        {
            Util.Assert(this.colorEnum == null);
            switch (colorName)
            {
                case Presentation.RED:
                    this.colorEnum = Red;
                    break;
                case Presentation.GREEN:
                    this.colorEnum = Green;
                    break;
                default:
                    this.colorEnum = Ordinary;
                    break;
            }

            this.document.Append(this.colorEnum.start);
        }

        public void endColor()
        {
            this.document.Append(this.colorEnum.stop);
            this.colorEnum = null;
        }

        public void startBullet()
        {
            this.document.Append(" * ");
        }

        public void endBullet()
        {
            this.document.Append("\n");
        }

        public void startPre()
        {
        }

        public void endPre()
        {
            if (!this.document.ToString().EndsWith("\n"))
            {
                this.document.Append("\n");
            }
        }

        public void doText(string text)
        {
            this.document.Append(text);
        }

        /// <summary>
        /// Definition of the start and stop sequences for a color.
        /// </summary>
        /// <remarks>
        /// REVIEW: This class is not needed, as there is only one stop sequence.
        /// </remarks>
        private class ColorEnum
        {
            public string start;
            public string stop;

            public ColorEnum(string start, string stop)
            {
                this.start = start;
                this.stop = stop;
            }

            public static ColorEnum join(ColorEnum a, ColorEnum b)
            {
                return new ColorEnum(a.start + b.start, b.stop + a.stop);
            }
        }
    }
}
