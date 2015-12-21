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
    using System.Text;

    using NDepend.Helpers;
    using NDepend.Path;

    internal class Logger
    {
        private static readonly List<string> StartupBuffer;
        private static readonly object Lock;
        private static readonly HashSet<string> ActiveTags;
        private static readonly HashSet<string> DefaultMessageTags;

        private static StreamWriter Log;
        private static IAbsoluteFilePath Path;

        private static Func<IEnumerable<string>, bool> IsOutput { get; set; } 

        static Logger()
        {
            StartupBuffer = new List<string>();
            ActiveTags = new HashSet<string> { "error", "warning", "fatal", "info", "summary", "stderr" };
            DefaultMessageTags = new HashSet<string> { "info" };
            IsOutput = tags => tags.Contains("stdout");
            Lock = new object();
            Path = null;
            Log = null;
        }

        private static bool FilterTags(IEnumerable<string> messageTags, out SortedSet<string> effectiveTags)
        {
            var e = Enumerable.Intersect(messageTags ?? DefaultMessageTags, ActiveTags);
            if (e.Any())
            {
                effectiveTags = new SortedSet<string>(e);
                return true;
            }
            else
            {
                effectiveTags = null;
                return false;
            }
        }

        public static void LogTag(string tag)
        {
            lock (Lock)
            {
                ActiveTags.Add(tag);
            }
        }

        public static void IgnoreTag(string tag)
        {
            lock (Lock)
            {
                ActiveTags.Remove(tag);
            }
        }

        private static string FormatMessage(string msg, SortedSet<string> tags)
        {
            // todo: prefix should be "fstar|STDOUT" where CAPS is matched and fstar is unmatched msg tag.
            string prefix = tags == null ? "" : string.Format("{0}|", string.Join("|", tags));
            return string.Format("{0}{1}", prefix, msg);
        }

        public static void WriteLine(string msg, IEnumerable<string> tags = null)
        {
            SortedSet<string> effective;
            if (!FilterTags(tags, out effective))
            {
                return;
            }

            var formatted = FormatMessage(msg, effective);
            bool isOutput = IsOutput(effective);
            lock (Lock)
            {
                if (isOutput)
                {
                    Console.Out.WriteLine(msg);
                }
                else
                {
                    Console.Error.WriteLine(formatted);
                }

                if (Log == null)
                {
                    StartupBuffer.Add(formatted);
                }
                else
                {
                    Log.WriteLine(formatted);
                }
            }
        }

        public static void WriteLine(string msg, string tag)
        {
            var tags = tag == null ? null : new[] { tag };
            WriteLine(msg, tags);
        }

        public static void Write(Presentation pr, IEnumerable<string> tags = null)
        {
            var sb = new StringBuilder();
            // todo: is colorization really necessary? it's a pain to support as implemented.
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
                sb.AppendLine(line);
            }

            var msg = sb.ToString();
            WriteLine(msg, tags);
        }

        public static void Write(Presentation pr, string tag)
        {
            var tags = tag == null ? null : new[] { tag };
            Write(pr, tags);
        }

        public static void Start(IAbsoluteFilePath path)
        {
            lock (Lock)
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
                StartupBuffer.Clear();

                var now = DateTime.UtcNow;
                var greeting = string.Format("NuBuild log `{0}` opened at {1}.", Path, now);
                WriteLine(greeting);
                Log.Flush();
            }
        }
    }
}
