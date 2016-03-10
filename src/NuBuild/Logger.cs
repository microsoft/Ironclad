//--
// <copyright file="Logger.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Diagnostics;
    using System.IO;
    using System.Linq;
    using System.Text;

    internal class Logger
    {
        private const string QuietTag = "*quiet";
        private static readonly List<string> StartupBuffer;
        private static readonly object Lock;
        private static readonly HashSet<string> ActiveTags;
        private static readonly HashSet<string> DefaultMessageTags;

        private static StreamWriter Log;
        private static AbsoluteFileSystemPath Path;

        private static Func<IEnumerable<string>, bool> IsOutput { get; set; } 

        static Logger()
        {
            StartupBuffer = new List<string>();
            ActiveTags = new HashSet<string> { "error", "warning", "fatal", "info", "summary", "stderr", "progress"};
            DefaultMessageTags = new HashSet<string> { "info" };
            IsOutput = tags => tags.Contains("stdout");
            Lock = new object();
            Path = null;
            Log = null;
        }

        private static string FormatPrefix(IEnumerable<string> messageTags, out SortedSet<string> effective)
        {
            var tags = (messageTags ?? DefaultMessageTags).Select(s => s.ToLowerInvariant());
            var sortedTags = new SortedSet<string>(tags);
            effective = new SortedSet<string>();
            var sb = new StringBuilder();
            foreach (var tag in sortedTags)
            {
                if (ActiveTags.Contains(tag))
                {
                    sb.Append(tag.ToUpperInvariant());
                    effective.Add(tag);
                }
                else
                {
                    if (tag.StartsWith("*"))
                    {
                        effective.Add(tag);
                    }
                    else
                    {
                        sb.Append(tag);
                    }
                }
                sb.Append("|");
            }
            var result = sb.ToString();
            return result;
        }

        public static void LogTag(string tag)
        {
            lock (Lock)
            {
                ActiveTags.Add(tag.ToLowerInvariant());
            }
        }

        public static void IgnoreTag(string tag)
        {
            lock (Lock)
            {
                ActiveTags.Remove(tag.ToLowerInvariant());
            }
        }

        public static void Quiet()
        {
            lock (Lock)
            {
                ActiveTags.Clear();
                LogTag("stderr");
                LogTag("stdout");
            }
        }

        private static string FormatMessage(string msg, IEnumerable<string> tags, out SortedSet<string> effective, bool fixNewLines)
        {
            var prefix = FormatPrefix(tags, out effective);
            var s = string.Format("{0}{1}", prefix, msg);
            if (fixNewLines)
            {
                var lines = s.Split(new[] { "\r\n", "\n" }, StringSplitOptions.None);
                s = string.Join("\n", lines);
            }
            return s;
        }

        public static void WriteLine(string msg, IEnumerable<string> tags = null, bool fixNewLines = true)
        {
            SortedSet<string> effective;
            var formatted = FormatMessage(msg, tags, out effective, fixNewLines);
            bool isOutput = IsOutput(effective);
            lock (Lock)
            {
                Trace.WriteLine(formatted);

                if (effective.Count > 0 && !effective.Contains(QuietTag))
                {
                    if (isOutput)
                    {
                        Console.Out.WriteLine(msg);
                    }
                    else
                    {
                        Console.Error.WriteLine(formatted);
                    }
                }

                if (Log == null)
                {
                    StartupBuffer.Add(formatted);
                }
                else
                {
                    Log.WriteLine(formatted);
                    // todo: i haven't figured out how to flush the log if an exception is thrown (a high-level finally doesn't work), so i need to flush regularly for now.
                    Flush();
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
            var lines = ascii.ToString().Split(new []{"\r\n", "\n"}, StringSplitOptions.None).ToList();

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

        public static void Start(AbsoluteFileSystemPath path)
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

        public static void Flush()
        {
            lock (Lock)
            {
                if (Log != null)
                {
                    Log.Flush();
                }
            }
        }
    }
}
