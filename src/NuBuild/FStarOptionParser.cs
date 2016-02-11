using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace NuBuild
{
    public class FStarOptionParser
    {
        private readonly string[] args;
        private readonly List<RelativeFileSystemPath> includePaths;
        private readonly List<string> sourceFileArgs;
        private readonly List<string> ignored; 

        public FStarOptionParser(IEnumerable<string> args)
        {
            this.args = args.ToArray();
            this.includePaths = new List<RelativeFileSystemPath>();
            this.sourceFileArgs = new List<string>();
            this.ignored = new List<string>();
            this.ParseArgs();
        }

        public IEnumerable<string> Args
        {
            get
            {
                return this.args;
            }
        }

        public bool ExplicitDeps { get; private set; }

        private bool NoDefaultIncludes
        {
            get
            {
                // this flag's value must be known before calling ParseArgs().
                return this.args.Contains("--no_default_includes");
            }
        }

        public IEnumerable<RelativeFileSystemPath> IncludePaths
        {
            get
            {
                return this.includePaths;
            }
        }

        public IEnumerable<string> SourceFileArgs
        {
            get
            {
                return this.sourceFileArgs;
            }
        }

        public IEnumerable<RelativeFileSystemPath> SourceFilePaths
        {
            get
            {
                return this.sourceFileArgs.Select(s => RelativeFileSystemPath.Parse(s, permitImplicit: true));
            }
        }
             

        public IEnumerable<RelativeFileSystemPath> GetModuleSearchPaths()
        {
            var paths = new List<RelativeFileSystemPath>();
            if (!this.NoDefaultIncludes)
            {
                paths.AddRange(FStarEnvironment.DefaultModuleSearchPaths.Reverse());
            }
            paths.AddRange(this.IncludePaths);
            paths.Add(NuBuildEnvironment.InvocationPath.ExtractRelative(NuBuildEnvironment.RootDirectoryPath));
            return paths;
        }

        public IEnumerable<string> GetNormalizedArgs()
        {
            yield return "--no_default_includes";
            if (this.ExplicitDeps)
            {
                yield return "--explicit_deps";
            }
            var paths = this.GetModuleSearchPaths();
            foreach (var path in paths)
            {
                yield return "--include";
                yield return path.ToString();
            }
            foreach (var path in this.SourceFilePaths)
            {
                yield return path.ToString("i");
            }
            foreach (var arg in this.ignored)
            {
                yield return arg;
            }
        }

        private void ParseArgs()
        {
            if (this.args.Length == 0)
            {
                return;
            }

            var last = this.args.Length - 1;
            for (var i = 0; i < this.args.Length; ++i)
            {
                var arg = this.args[i].ToLower();
                if (arg.StartsWith("--"))
                {
                    if (arg.Equals("--admit_fsi", StringComparison.CurrentCultureIgnoreCase)
                        || arg.Equals("--z3timeout", StringComparison.CurrentCulture)
                        || arg.Equals("--verify_module", StringComparison.CurrentCulture))
                    {
                        // --admit_fsi requires a parameter.
                        if (i == last)
                        {
                            var msg = string.Format("F* argument `{0}` requires a parameter.", arg);
                            throw new ArgumentException(msg);
                        }
                        this.ignored.Add(this.args[i]);
                        this.ignored.Add(this.args[++i]);
                    }
                    else if (arg.Equals("--include", StringComparison.CurrentCultureIgnoreCase))
                    {
                        // --include requires a parameter.
                        if (i == last)
                        {
                            throw new ArgumentException("F* argument `--include` requires a parameter.");
                        }
                        var relPath = ParseIncludePath(this.args[++i]);
                        this.includePaths.Add(relPath);
                    }
                    else if (arg.Equals("--explicit_deps", StringComparison.CurrentCultureIgnoreCase))
                    {
                        this.ExplicitDeps = true;
                    }
                    else if (arg.Equals("--dep", StringComparison.CurrentCultureIgnoreCase))
                    {
                        throw new ArgumentException("Use of F* option `--dep` is disallowed");
                    }
                    else
                    {
                        UnrecognizedArg(arg);
                    }
                }
                else if (arg.EndsWith(".fst") || arg.EndsWith(".fsi") || arg.EndsWith(".fsti"))
                {
                    this.sourceFileArgs.Add(this.args[i]);
                }
                else
                {
                    UnrecognizedArg(arg);
                }
            }
        }

        public IDictionary<string, RelativeFileSystemPath> FindSourceFiles()
        {
            var result = new Dictionary<string, RelativeFileSystemPath>();
            var searchPaths = this.GetModuleSearchPaths();
            foreach (var fileArg in this.SourceFileArgs)
            {
                var filePath = RelativeFileSystemPath.Parse(fileArg, permitImplicit: true);
                var found = NuBuildEnvironment.FindFile(filePath, searchPaths);
                if (found == null)
                {
                    var msg = string.Format("Unable to find file (`{0}`) in module search path (`{1}`).", fileArg, string.Join(";", searchPaths.Select(p => p.ToString())));
                    throw new FileNotFoundException(msg);
                }
                result.Add(fileArg, found);
            }
            return result;
        } 

        private void UnrecognizedArg(string arg)
        {
            var msg = string.Format("Unrecognized F* option {0}", arg);
            Logger.WriteLine(msg, new[] { "warning", "fstar" });
            this.ignored.Add(arg);
        }

        private static RelativeFileSystemPath ParseIncludePath(string s)
        {
            if (FileSystemPath.IsAbsolutePath(s))
            {
                var msg = string.Format("Passing absolute paths to F* (i.e. `{0}`) is disallowed.", s);
                throw new ArgumentException(msg);
            }
            var relPath = RelativeFileSystemPath.Parse(s, permitImplicit: true);
            var absPath = AbsoluteFileSystemPath.FromRelative(relPath, NuBuildEnvironment.InvocationPath);
            return absPath.ExtractRelative(NuBuildEnvironment.RootDirectoryPath);
        }
    }
}
