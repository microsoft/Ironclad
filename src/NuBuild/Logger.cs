//--
// <copyright file="Logger.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.IO;
    using System.Linq;

    /// <summary>
    /// Utility for writing log messages simultaneously to the console and
    /// a log file.
    /// </summary>
    internal class Logger
    {
        /// <summary>
        /// The log file.
        /// </summary>
        private static StreamWriter log;

        /// <summary>
        /// Writes a message to both the log file and the console.
        /// </summary>
        /// <param name="msg">Message to write.</param>
        public static void Write(string msg)
        {
            OpenLog();
            log.Write(msg);
            log.Flush();
            System.Console.Write(msg);
        }

        /// <summary>
        /// Writes a message and the newline string to both the log file
        /// and the console.
        /// </summary>
        /// <param name="msg">Message to write.</param>
        public static void WriteLine(string msg)
        {
            Write(msg + System.Environment.NewLine);
        }

        public static void WritePresentation(Presentation pr)
        {
            ASCIIPresentater ascii = new ASCIIPresentater();
            pr.format(ascii);
            var lines = ascii.ToString().Split('\n').ToList();

            // trim last line if empty.
            if (string.IsNullOrWhiteSpace(lines[lines.Count - 1]))
            {
                lines.RemoveAt(lines.Count - 1);
            }

            foreach (var line in lines)
            {
                WriteLine(line);
            }
        }

        /// <summary>
        /// Opens the log file (if it isn't already open).
        /// </summary>
        private static void OpenLog()
        {
            if (log == null)
            {
                log = new StreamWriter("nubuild.log");
            }
        }
    }
}
