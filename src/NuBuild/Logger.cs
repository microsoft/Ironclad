//--
// <copyright file="Logger.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;

    using NDepend.Path;

    /// <summary>
    /// Utility for writing Out messages simultaneously to the console and
    /// a Out file.
    /// </summary>
    internal class Logger
    {
        private static List<string> StartupBuffer;
 
        /// <summary>
        /// The Out file.
        /// </summary>
        private static StreamWriter Out;

        private static IAbsoluteFilePath Path;

        static Logger()
        {
            StartupBuffer = new List<string>();
            Path = null;
            Out = null;
        }

        
        /// <summary>
        /// Writes a message and the newline string to both the Out file
        /// and the console.
        /// </summary>
        /// <param name="msg">Message to write.</param>
        private static void WriteLineToDisplay(string msg)
        {
            Console.WriteLine(msg);
        }

        private static void WriteLineToFile(string msg)
        {
            if (Out != null)
            {
                Out.WriteLine(msg);
                Out.Flush();
            }
            else
            {
                StartupBuffer.Add(msg);
            }
        }

        /// <summary>
        /// Writes a message and the newline string to both the Out file
        /// and the console.
        /// </summary>
        /// <param name="msg">Message to write.</param>
        public static void WriteLine(string msg)
        {
            WriteLineToDisplay(msg);
            WriteLineToFile(msg);
        }

        public static void WriteLines(Presentation pr)
        {
            var ascii = new ASCIIPresentater(colorize: false);
            pr.format(ascii);
            var lines = ascii.ToString().Split('\n').ToList();

            // trim last line if empty.
            if (string.IsNullOrWhiteSpace(lines[lines.Count - 1]))
            {
                lines.RemoveAt(lines.Count - 1);
            }

            foreach (var line in lines)
            {
                WriteLineToFile(line);
            }

            ascii = new ASCIIPresentater();
            pr.format(ascii);
            lines = ascii.ToString().Split('\n').ToList();

            // trim last line if empty.
            if (string.IsNullOrWhiteSpace(lines[lines.Count - 1]))
            {
                lines.RemoveAt(lines.Count - 1);
            }

            foreach (var line in lines)
            {
                WriteLineToDisplay(line);
            }
        }

        /// <summary>
        /// Opens the Out file (if it isn't already open).
        /// </summary>
        public static void Start(IAbsoluteFilePath path)
        {
            if (Out != null && !string.Equals(path.ToString(), Path.ToString(), StringComparison.InvariantCultureIgnoreCase))
            {
                throw new InvalidOperationException("Attempt to open a log at conflicting locations.");
            }

            Path = path;
            Out = new StreamWriter(path.ToString(), append: true);
            foreach (var line in StartupBuffer)
            {
                Out.WriteLine(line);
            }
            StartupBuffer = null;

            var now = DateTime.UtcNow;
            var greeting = string.Format("[NuBuild] NuBuild log `{0}` opened at {1}.", Path, now);
            WriteLine(greeting);
            Out.Flush();
        }
    }
}
