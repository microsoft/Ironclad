//--
// <copyright file="SourcePathIncludeContext.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;

    // This context looks for files in a set of source path locations.
    internal class SourcePathIncludeContext
        : IncludePathContext
    {
        private List<DirectoryRecord> directories;
        private List<string> dstExtensions;
        private string _descr;

        public SourcePathIncludeContext()
        {
            this.directories = new List<DirectoryRecord>();
            this.dstExtensions = new List<string>();
        }

        public override string ToString()
        {
            if (this._descr == null)
            {
                this._descr = "{" + string.Join(",", this.directories.Select(d => d.directory)) + "}; {"
                    + string.Join(",", this.dstExtensions) + "}";
            }

            return this._descr;
        }

        // Add a directory path relative to ironRoot.
        public void addDirectory(string directory)
        {
            Util.Assert(this._descr == null);
            this.directories.Add(new DirectoryRecord(directory));
        }

        public void addDstExtension(string extension)
        {
            Util.Assert(this._descr == null);
            this.dstExtensions.Add(extension);
        }

        public override BuildObject search(string basename, ModPart modPart)
        {
            List<SourcePath> results = new List<SourcePath>();

            foreach (string extension in this.dstExtensions.Where(extn => BeatExtensions.whichPart(extn) == modPart))
            {
                string filename = basename + extension;
                foreach (DirectoryRecord directoryRecord in this.directories)
                {
                    if (directoryRecord.Contains(filename))
                    {
                        string proposed = Path.Combine(
                            BuildEngine.theEngine.getIronRoot(),
                            BuildEngine.theEngine.getSrcRoot(),
                            directoryRecord.directory,
                            basename + extension);
                        ////Logger.WriteLine("SourcePathIncludeContext Trying " + proposed);
                        ////Util.Assert(File.Exists(proposed));
                        results.Add(new SourcePath(proposed));
                    }
                }
            }

            if (results.Count() == 0)
            {
                return null;
            }
            else if (results.Count() > 1)
            {
                throw new SourceConfigurationError(string.Format(
                    "Reference {0} matches {1} paths: {2}",
                    basename,
                    results.Count(),
                    string.Join(",", results)));
            }
            else
            {
                return results.First();
            }
        }

        private class DirectoryRecord
        {
            private readonly string _directory;
            private readonly HashSet<string> _files;

            public DirectoryRecord(string directory)
            {
                this._directory = directory;
                string absDir = Path.Combine(
                            BuildEngine.theEngine.getIronRoot(),
                            BuildEngine.theEngine.getSrcRoot(),
                            this._directory);
                this._files = new HashSet<string>(Directory.EnumerateFiles(absDir)
                    .Select(path => Path.GetFileName(path)));
            }

            public string directory
            {
                get { return this._directory; }
            }

            public bool Contains(string file)
            {
                return this._files.Contains(file);
            }
        }
   }
}
