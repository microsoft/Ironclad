//--
// <copyright file="DafnyIncludes.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Text.RegularExpressions;

    /// <summary>
    /// Extractor of Dafny include file names (and related functionality).
    /// </summary>
    internal class DafnyIncludes
        : IIncludeFactory
    {
        /// <summary>
        /// Regular expression matching Dafny include lines.
        /// </summary>
        private Regex includeRegex;

        /// <summary>
        /// Temporary working directory used by ExpandDafny method.
        /// </summary>
        private WorkingDirectory workingDirectory;

        /// <summary>
        /// TextWriter used by ExpandDafny method.
        /// </summary>
        private TextWriter outputWriter;

        /// <summary>
        /// Set of include files already visited.
        /// Used by ExpandDafny method.
        /// </summary>
        private HashSet<string> visited;

        /// <summary>
        /// Initializes a new instance of the DafnyIncludes class.
        /// </summary>
        public DafnyIncludes()
        {
            this.includeRegex = new Regex("^\\s*include\\s*\"(.*)\"");
        }

        /// <summary>
        /// Gets a list of the include files included in the given Dafny source file.
        /// </summary>
        /// <param name="dfysource">Source file to extract include file names from.</param>
        /// <returns>List of include file BuildObjects.</returns>
        public IEnumerable<BuildObject> getIncludes(BuildObject dfysource)
        {
            List<BuildObject> outlist = new List<BuildObject>();
            using (TextReader tr = BuildEngine.theEngine.Repository.OpenRead(dfysource))
            {
                while (true)
                {
                    string line = tr.ReadLine();
                    if (line == null)
                    {
                        break;
                    }

                    Match match = this.includeRegex.Match(line);
                    int count = 0;
                    while (match.Success)
                    {
                        string includedPath = match.Groups[1].ToString();
                        string gluedPath = Path.Combine(dfysource.getDirPath(), includedPath);
                        SourcePath sp = new SourcePath(gluedPath);
                        outlist.Add(sp);
                        count += 1;
                        match = match.NextMatch();  // That would be unexpected!
                    }

                    Util.Assert(count <= 1);
                }
            }

            ////Logger.WriteLine(String.Format("{0} includes {1} things", dfysource.getFilesystemPath(), outlist.Count));
            return outlist;
        }

        /// <summary>
        /// Expand a dafny source file to include all of its includes inline.
        /// </summary>
        /// <param name="workingDirectory">Temporary working directory to use.</param>
        /// <param name="input">Source build object.</param>
        /// <param name="output">Where to create build object for expanded source file.</param>
        public void ExpandDafny(WorkingDirectory workingDirectory, SourcePath input, SourcePath output)
        {
            // Prepare the output stream.
            using (TextWriter outWriter = new StreamWriter(workingDirectory.PathTo(output)))
            {
                // Stash away a few things for use by our recursive helper function.
                this.workingDirectory = workingDirectory;
                this.outputWriter = outWriter;
                this.visited = new HashSet<string>();

                // Recursively expand the initial Dafny source file to inline all of its includes.
                this.ExpandDafnyRecurse(input);
            }

            // Cache the output file in the Repository.
            BuildEngine.theEngine.Repository.Store(workingDirectory, output, new Fresh());
        }

        /// <summary>
        /// Helper function for ExpandDafny method.
        /// </summary>
        /// <param name="input">Next include file to visit.</param>
        /// <returns>True if the given file wasn't already included, false otherwise.</returns>
        private bool ExpandDafnyRecurse(SourcePath input)
        {
            // Only visit each unique include file once.
            // Note that SourcePaths (like all BuildObjects) have normalized file paths.
            string inputPath = input.getRelativePath();
            if (this.visited.Contains(inputPath))
            {
                return false;
            }
            else
            {
                this.visited.Add(inputPath);
            }

            using (TextReader reader = new StreamReader(this.workingDirectory.PathTo(input)))
            {
                while (true)
                {
                    string line = reader.ReadLine();
                    if (line == null)
                    {
                        return true;
                    }

                    Match match = this.includeRegex.Match(line);
                    if (match.Success)
                    {
                        // This is an "include" line.  Find the included object.
                        string includedPath = match.Groups[1].ToString();
                        string gluedPath = Path.Combine(input.getDirPath(), includedPath);
                        SourcePath nextInclude = new SourcePath(gluedPath);
                        string nextPath = nextInclude.getRelativePath();

                        // Recurse on the new include file.
                        this.outputWriter.WriteLine("//- Begin include {0} (from {1})", nextPath, inputPath);
                        if (!this.ExpandDafnyRecurse(nextInclude))
                        {
                            this.outputWriter.WriteLine("//- Already included {0}", nextPath);
                        }

                        this.outputWriter.WriteLine("//- End include {0} (from {1})", nextPath, inputPath);
                    }
                    else
                    {
                        // This isn't an "include" line.  Write it to our output.
                        this.outputWriter.WriteLine(line);
                    }
                }
            }
        }
    }
}
