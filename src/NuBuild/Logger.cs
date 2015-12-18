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

    internal class Logger
    {
        private static List<string> StartupBuffer;
 
        private static StreamWriter Log;

        private static IAbsoluteFilePath Path;

        private static object Lock;

        static Logger()
        {
            StartupBuffer = new List<string>();
            Lock = new object();
            Path = null;
            Log = null;
        }


        private static void WriteLineToStdOut(string msg)
        {
            lock (Lock)
            {
                Console.Out.WriteLine(msg);
            }
        }

        /// <summary>
        /// Writes a message and the newline string to both the Log file
        /// and the console.
        /// </summary>
        /// <param name="msg">Message to write.</param>
        private static void WriteLineToStdError(string msg)
        {
            lock (Lock)
            {
                Console.Error.WriteLine(msg);
            }
        }

        private static void WriteLineToLog(string msg)
        {
            lock (Lock)
            {
                if (Log != null)
                {
                    Log.WriteLine(msg);
                    Log.Flush();
                }
                else
                {
                    StartupBuffer.Add(msg);
                }
            }
        }

        /// <summary>
        /// Writes a message and the newline string to both the Log file
        /// and the console.
        /// </summary>
        /// <param name="msg">Message to write.</param>
        public static void WriteLine(string msg)
        {
            lock (Lock)
            {
                WriteLineToStdError(msg);
                WriteLineToLog(msg);
            }
        }

        public static void WriteLines(Presentation pr)
        {
            lock (Lock)
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
                    WriteLineToLog(line);
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
                    WriteLineToStdOut(line);
                }
            }
        }

        /// <summary>
        /// Opens the Log file (if it isn't already open).
        /// </summary>
        public static void Start(IAbsoluteFilePath path)
        {
            if (Log != null && !string.Equals(path.ToString(), Path.ToString(), StringComparison.InvariantCultureIgnoreCase))
            {
                throw new InvalidOperationException("Attempt to open a log at conflicting locations.");
            }

            Path = path;
            Log = new StreamWriter(path.ToString(), append: true);
            foreach (var line in StartupBuffer)
            {
                Log.WriteLine(line);
            }
            StartupBuffer = null;

            var now = DateTime.UtcNow;
            var greeting = string.Format("[NuBuild] NuBuild log `{0}` opened at {1}.", Path, now);
            WriteLine(greeting);
            Log.Flush();
        }
    }
}
