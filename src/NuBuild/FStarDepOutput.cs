
namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    class FStarDepOutput : VirtualContents
    {
        public readonly Dictionary<RelativeFileSystemPath, IEnumerable<RelativeFileSystemPath>> ByTarget;

        private readonly IDictionary<string, RelativeFileSystemPath> foundSources;

        public FStarDepOutput(string output, FStarOptionParser optParser, WorkingDirectory workDir)
        {
            this.foundSources = optParser.FindSourceFiles();
            this.ByTarget = this.Parse(output, workDir);
        }

        public IEnumerable<RelativeFileSystemPath> GetAll()
        {
            var set = new HashSet<RelativeFileSystemPath>();
            foreach (var target in this.ByTarget.Keys)
            {
                set.Add(target);
                foreach (var depend in this.ByTarget[target])
                {
                    set.Add(target);
                }
            }
            return set;
        }

        private Dictionary<RelativeFileSystemPath, IEnumerable<RelativeFileSystemPath>> Parse(string output, WorkingDirectory workDir)
        {
            //var stdLib = FStarEnvironment.StandardLibrary;
            var lines = output.Split(new[] { "\r\n", "\n" }, StringSplitOptions.RemoveEmptyEntries);
            var result = new Dictionary<RelativeFileSystemPath, IEnumerable<RelativeFileSystemPath>>();

            // output is a makefile-like language. 
            // - each line is "target: depend depend depend"
            // - all filenames appear to be absolute paths.
            // - backslashes are not escaped.
            // todo: are spaces escaped?

            for (var i = 0; i < lines.Length; ++i)
            {
                var line = lines[i];
                var sepByColon = line.Split(new[] { ": " }, StringSplitOptions.None);
                if (sepByColon.Length != 2)
                {
                    var msg = string.Format("Expected line {0} of `fstar --dep make` output to contain a `:`.", i);
                    throw new InvalidOperationException(msg);
                }
                var sepBySpaces = sepByColon[1].Split(new[] { ' ' }, StringSplitOptions.RemoveEmptyEntries);

                var target = this.ParsePath(sepByColon[0], workDir);
                var depends = new List<RelativeFileSystemPath>();
                foreach (var depend in sepBySpaces)
                {
                    depends.Add(ParsePath(depend, workDir));
                }
                result.Add(target, depends);
            }
            return result;
        }

        private RelativeFileSystemPath ParsePath(string s, WorkingDirectory workDir)
        {
            if (FileSystemPath.IsAbsolutePath(s))
            {
                return AbsoluteFileSystemPath.Parse(s).MapToBuildObjectPath(workDir);
            }
            else if (foundSources.ContainsKey(s))
            {
                return foundSources[s];
            }
            else
            {
                return RelativeFileSystemPath.Parse(s, permitImplicit: true);
            }
        }
    }
}
