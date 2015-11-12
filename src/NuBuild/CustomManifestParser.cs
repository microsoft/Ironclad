//--
// <copyright file="CustomManifestParser.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Text;

    internal class CustomManifestParser
    {
        private HashSet<BuildObject> dependencies = new HashSet<BuildObject>();
        private HashSet<BuildObject> outputs = new HashSet<BuildObject>();

        public CustomManifestParser(SourcePath basePath)
        {
            this.parseCustomManifest(basePath);
        }

        public IEnumerable<BuildObject> getDependencies()
        {
            return this.dependencies;
        }

        public IEnumerable<BuildObject> getOutputs()
        {
            return this.outputs;
        }

        private void parseCustomManifest(SourcePath basePath)
        {
            SourcePath manifest = basePath.getNewSourcePath("nubuild-manifest.txt");
            this.dependencies.Add(manifest);

            using (StreamReader stream = new StreamReader(IronRootDirectory.PathTo(manifest)))
            {
                string origline;

                while ((origline = stream.ReadLine()) != null)
                {
                    string line = origline.Trim();

                    if (line.Length == 0)
                    {
                        continue;
                    }

                    if (line.Substring(0, 1) == "#")
                    {
                        continue;
                    }

                    string[] parts = line.Split();

                    if (parts.Length != 2)
                    {
                        throw new UserError(string.Format("{0}: badly formed manifest line {1}", IronRootDirectory.PathTo(manifest), origline));
                    }

                    if ("output".Equals(parts[0]))
                    {
                        this.outputs.Add(new BuildObject(Path.Combine(basePath.getDirPath(), parts[1])));
                    }
                    else if ("dependency".Equals(parts[0]))
                    {
                        this.dependencies.Add(basePath.getNewSourcePath(parts[1]));
                    }
                }
            }
        }
    }
}
