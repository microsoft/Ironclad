//--
// <copyright file="VSSolutionParser.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Text.RegularExpressions;

    internal class VSSolutionParser
    {
        private SourcePath solutionFile;
        private List<BuildObject> dependencies = new List<BuildObject>();
        private List<BuildObject> outputs = new List<BuildObject>();

        public VSSolutionParser(SourcePath solutionFile)
        {
            this.solutionFile = solutionFile;
            this.Parse();
        }

        public IEnumerable<BuildObject> getDependencies()
        {
            return this.dependencies;
        }

        public IEnumerable<BuildObject> getOutputs()
        {
            return this.outputs;
        }

        private void Parse()
        {
            this.dependencies.Add(this.solutionFile);

            using (StreamReader stream = new StreamReader(IronRootDirectory.PathTo(this.solutionFile)))
            {
                Regex regex = new Regex(@"Project\([\S]+\)[\s]+=[\s]+([^$]*)", RegexOptions.IgnoreCase);
                string line;

                while ((line = stream.ReadLine()) != null)
                {
                    MatchCollection matches = regex.Matches(line);

                    if (matches.Count > 0)
                    {
                        SourcePath projFile = this.solutionFile.getNewSourcePath(matches[0].Groups[1].Value.Split("\", ".ToCharArray())[5]);
                        ////Console.WriteLine(String.Format("Found project file {0}", projFile.getFilesystemPath()));
                        VSProjectParser proj = new VSProjectParser(projFile);
                        this.dependencies.AddRange(proj.getDependencies());
                        this.outputs.AddRange(proj.getOutputs());
                    }
                }

                stream.Close();
            }
        }
    }
}
