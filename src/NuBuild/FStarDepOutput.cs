
namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;

    class FStarDepOutput : VirtualContents
    {
        public readonly Dictionary<RelativeFileSystemPath, IEnumerable<RelativeFileSystemPath>> ByTarget;

        private readonly IDictionary<string, RelativeFileSystemPath> foundSources;
        
        public FStarDepOutput(string output, FStarOptionParser optParser)
        {
            this.foundSources = optParser.FindSourceFiles();
            this.ByTarget = this.Parse(output);
        }

        public IEnumerable<RelativeFileSystemPath> GetAll()
        {
            var set = new SortedSet<RelativeFileSystemPath>();
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

        public IEnumerable<string> GetAllModules()
        {
            var set = new SortedSet<string>();
            set.UnionWith(this.GetAll().Select(p => p.FileNameWithoutExtension));
            return set;
        }

        private Dictionary<RelativeFileSystemPath, IEnumerable<RelativeFileSystemPath>> Parse(string output)
        {
            // we silently drop references to prims.fst, as that's hardcoded into F*.
            // todo: this might be controlled with command-line arguments.
            const string prims = "prims.fst";

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

                var target = this.ParsePath(sepByColon[0]);
                if (target.FileName.Equals(prims, StringComparison.CurrentCultureIgnoreCase))
                {
                    continue;
                }

                var depends = new List<RelativeFileSystemPath>();
                foreach (var depend in sepBySpaces)
                {
                    var dependPath = this.ParsePath(depend);
                    if (dependPath.FileName.Equals(prims, StringComparison.CurrentCultureIgnoreCase))
                    {
                        continue;
                    }

                    depends.Add(dependPath);
                }
                result.Add(target, depends);
            }
            return result;
        }

        private RelativeFileSystemPath ParsePath(string s)
        {
            if (FileSystemPath.IsAbsolutePath(s))
            {
                return AbsoluteFileSystemPath.Parse(s).MapToBuildObjectPath();
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
