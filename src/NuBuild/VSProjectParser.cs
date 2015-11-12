//--
// <copyright file="VSProjectParser.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Xml;

    /// <summary>
    /// Mechanism for parsing Visual Studio project Files.
    /// Determines project dependencies and outputs.
    /// </summary>
    internal class VSProjectParser
    {
        private SourcePath projectFile;
        private HashSet<BuildObject> dependencies = new HashSet<BuildObject>();
        private HashSet<BuildObject> outputs = new HashSet<BuildObject>();
        private string outputType = null;
        private string assemblyName = null;
        ////private string outputPath = null;

        /// <summary>
        /// Initializes a new instance of the VSProjectParser class.
        /// </summary>
        /// <param name="projectFile">Visual Studio project file to parse.</param>
        public VSProjectParser(SourcePath projectFile)
        {
            this.projectFile = projectFile;
            this.Parse();

            CustomManifestParser cm = new CustomManifestParser(this.projectFile);
            this.dependencies.UnionWith(cm.getDependencies());
            this.outputs.UnionWith(cm.getOutputs());
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
            this.dependencies.Add(this.projectFile);

            using (XmlTextReader reader = new XmlTextReader(IronRootDirectory.PathTo(this.projectFile)))
            {
                while (reader.Read())
                {
                    if (reader.NodeType == XmlNodeType.Element)
                    {
                        if (string.Compare(reader.Name, "Compile") == 0)
                        {
                            this.dependencies.Add(this.projectFile.getNewSourcePath(reader.GetAttribute("Include")));
                        }
                        else if (string.Compare(reader.Name, "PropertyGroup") == 0)
                        {
                            this.ParseOutput(reader);
                        }
                    }
                }

                reader.Close();
            }

            if (this.outputType != null && this.assemblyName != null) //// && outputPath != null)
            {
                string path = Path.Combine(this.projectFile.getDirPath(), string.Format("{0}.{1}", this.assemblyName, this.OutputTypeToExtension(this.outputType)));
                ////Console.WriteLine("{0}: generating {1}", this.projectFile.getRelativePath(), path);
                this.outputs.Add(new BuildObject(path));
            }
            else
            {
                throw new UserError(string.Format("Project {0} doesn't seem to have output specification in the expected format", this.projectFile.getRelativePath()));
            }
        }

        private void ValidateConsistentOption(string optionName, string oldValue, string newValue)
        {
            if (oldValue == null)
            {
                return;
            }

            if (!oldValue.Equals(newValue))
            {
                throw new UserError(
                    string.Format(
                        "Values for {0} not consistent across all build configurations in {1} ({2} vs {3})",
                        optionName,
                        this.projectFile.getRelativePath(),
                        oldValue,
                        newValue));
            }
        }

        private void ParseOutput(XmlTextReader reader)
        {
            string lastElement = null;

            while (reader.Read())
            {
                if (reader.NodeType == XmlNodeType.EndElement)
                {
                    lastElement = null;

                    if ("PropertyGroup".Equals(reader.Name))
                    {
                        break;
                    }
                }

                if (reader.NodeType == XmlNodeType.Element)
                {
                    lastElement = reader.Name;
                }

                if (reader.NodeType == XmlNodeType.Text && lastElement != null)
                {
                    string val = reader.Value;

                    ////if ("OutputPath".Equals(lastElement))
                    ////{
                    ////    validateConsistentOption("OutputPath", outputPath, val);
                    ////    outputPath = val;
                    ////}
                    if ("AssemblyName".Equals(lastElement))
                    {
                        this.ValidateConsistentOption("AssemblyName", this.assemblyName, val);
                        this.assemblyName = val;
                    }

                    if ("OutputType".Equals(lastElement))
                    {
                        this.ValidateConsistentOption("OutputType", this.outputType, val);
                        this.outputType = val;
                    }
                }
            }
        }

        private string OutputTypeToExtension(string outputType)
        {
            switch (outputType)
            {
                case "Exe":
                    return "exe";
                case "Library":
                    return "dll";
                default:
                    throw new SourceConfigurationError("VSProjectParser doesn't know how to canonicalize " + outputType);
            }
        }
    }
}
