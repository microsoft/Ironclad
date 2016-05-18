using System;
using System.Collections.Generic;
using System.Linq;

namespace NuBuild
{
    using System.IO;
    using System.Text.RegularExpressions;

    public static class FStarEnvironment
    {
        private static readonly IEnumerable<string> ExecutableSearchPaths = new [] { ".\\.fstar\\bin", ".\\bin", ".\\.nubuild\\.z3\\build" };

        private static readonly AbsoluteFileSystemPath AbsolutePathToFStarExe;
        private static readonly AbsoluteFileSystemPath AbsolutePathToZ3Exe;
        private static readonly IEnumerable<string> ImplicitStandardLibraryDependencies = new[] { "prims.fst" };

        public static readonly IEnumerable<SourcePath> Binaries;
        public static readonly IEnumerable<SourcePath> StandardLibrary;


        // the following list of default module search paths must match what's listed in `fstar/src/options.fs`.
        // don't include the current directory, however.
        // todo: it would be nice to be able to query F* for this list so that it does not need to be manually synchronized.
        private static readonly IEnumerable<string> standardLibrarySearchPaths = new [] { "./lib", "./lib/fstar", "./stdlib", "./stdlib/fstar" };
        private static readonly IEnumerable<string> universesStandardLibrarySearchPaths = new[] { "./ulib" };

        private static readonly IEnumerable<RelativeFileSystemPath> StandardLibrarySearchPaths;
        private static readonly IEnumerable<RelativeFileSystemPath> UniversesStandardLibrarySearchPaths;

        public static readonly IDictionary<string, string> VersionInfo; 

        static FStarEnvironment()
        {
            var pathToFStarExe = FindExecutable("fstar.exe");
            var pathToZ3Exe = FindExecutable("z3.exe");
            VersionInfo = GetVersionInfo(pathToFStarExe);
            Binaries = findBinaries(pathToFStarExe, VersionInfo, pathToZ3Exe);
            AbsolutePathToFStarExe = pathToFStarExe;
            AbsolutePathToZ3Exe = pathToZ3Exe;

            // F* defines more standard search paths than actually exist and rejects explicit specification of non-existent directories, so we need to filter out the paths that do not exist.
            var paths = new List<RelativeFileSystemPath>();
            foreach (var s in standardLibrarySearchPaths)
            {
                var path = RelativeFileSystemPath.Parse(s, permitImplicit: true);
                if (Directory.Exists(path.ToString()))
                {
                    paths.Add(path);
                }
            }
            StandardLibrarySearchPaths = SelectExistingDirectoryPaths(standardLibrarySearchPaths);
            UniversesStandardLibrarySearchPaths = SelectExistingDirectoryPaths(universesStandardLibrarySearchPaths);
            StandardLibrary = FindStandardLibrary();
        }

        public static RelativeFileSystemPath PathToFStarExe
        {
            get
            {
                return AbsolutePathToFStarExe.MapToBuildObjectPath();
            }
        }

        public static RelativeFileSystemPath PathToZ3Exe
        {
            get
            {
                return AbsolutePathToZ3Exe.MapToBuildObjectPath();
            }
        }

        public static RelativeFileSystemPath HomeDirectoryPath
        {
            get
            {
                return PathToFStarExe.ParentDirectoryPath.ParentDirectoryPath;
            }
        }

        public static IEnumerable<SourcePath> GetStandardDependencies(bool universes)
        {
            var searchPaths = universes ? UniversesStandardLibrarySearchPaths : StandardLibrarySearchPaths;
            var implicitDeps = ImplicitStandardLibraryDependencies.Select(s => NuBuildEnvironment.FindFile(RelativeFileSystemPath.Parse(s, permitImplicit: true), searchPaths));
            return Binaries.Concat(implicitDeps.Select(p => new SourcePath(p.ToString(), SourcePath.SourceType.Tools)));
        }

        private static List<SourcePath> findBinaries(AbsoluteFileSystemPath pathToFStarExe, IDictionary<string, string> versionInfo, AbsoluteFileSystemPath pathToZ3Exe)
        {
            AbsoluteFileSystemPath binPath = pathToFStarExe.ParentDirectoryPath;
            var result = new List<SourcePath>();

            result.Add(new SourcePath(pathToFStarExe.MapToBuildObjectPath().ToString(), SourcePath.SourceType.Tools, HashVersionInfo));

            string[] patterns;
            if (versionInfo["compiler"].StartsWith("OCaml"))
            {
                patterns = new[] { @"FStar\..*\.dll$", @".msvc[pr]100\.dll$" };
            }
            else
            {
                // we'll be less choosy about the F# binaries we'd like to copy over.
                patterns = new[] { @".*$" };
            }
            var regExprs = patterns.Select(s => new Regex(s, RegexOptions.IgnoreCase)).ToArray();
            var paths = binPath.ListFiles(recurse: true);
            foreach (var path in paths)
            {
                foreach (var re in regExprs)
                {
                    if (re.IsMatch(path.ToString()))
                    {
                        var nbPath = path.MapToBuildObjectPath().ToString();
                        result.Add(new SourcePath(nbPath, SourcePath.SourceType.Tools));
                        break;
                    }
                }
            }

            result.Add(new SourcePath(pathToZ3Exe.MapToBuildObjectPath().ToString(), SourcePath.SourceType.Tools));
            return result;
        }

        private static List<SourcePath> FindStandardLibrary()
        {
            if (AbsolutePathToFStarExe == null)
            {
                throw new InvalidOperationException("AbsolutePathToZ3Exe must be set before calling FindStandardLibrary");
            }

            if (StandardLibrarySearchPaths == null)
            {
                throw new InvalidOperationException("StandardLibrarySearchPaths must be set before calling FindStandardLibrary");
            }

            if (UniversesStandardLibrarySearchPaths == null)
            {
                throw new InvalidOperationException("UniversesStandardLibrarySearchPaths must be set before calling FindStandardLibrary");
            }

            var result = new List<SourcePath>();

            var regExprs = new[] { @"\.fs(t|ti|i)$", @"\.ml$" }.Select(s => new Regex(s, RegexOptions.IgnoreCase));

            var libPaths = new List<AbsoluteFileSystemPath>();
            foreach (var relPath in StandardLibrarySearchPaths.Concat(UniversesStandardLibrarySearchPaths))
            {
                var absPath = AbsoluteFileSystemPath.FromRelative(relPath, NuBuildEnvironment.RootDirectoryPath);
                libPaths.AddRange(absPath.ListFiles(recurse: true));
            }

            // some F* sources treat the contrib directory as the standard library, even though it really isn't.
            AbsoluteFileSystemPath contribDir = AbsolutePathToFStarExe.ParentDirectoryPath.CreateSiblingPath("contrib");
            var contribFiles = contribDir.ListFiles(recurse: true);

            var paths = libPaths.Concat(contribFiles);
            foreach (var path in paths)
            {
                foreach (var re in regExprs)
                {
                    if (re.IsMatch(path.ToString()))
                    {
                var nbPath = path.MapToBuildObjectPath().ToString();
                result.Add(new SourcePath(nbPath, SourcePath.SourceType.Tools));
                        break;
                    }
                }
            }
            return result;
        }

        private static AbsoluteFileSystemPath FindExecutable(string fileName)
        {
            NuBuildEnvironment.AddExecutableSearchPaths(ExecutableSearchPaths.Select(s => RelativeFileSystemPath.Parse(s)));

            var filePath = RelativeFileSystemPath.Parse(fileName, permitImplicit: true);
            var relFilePath = NuBuildEnvironment.FindExecutable(filePath);

            if (null == relFilePath)
            {
                var msg = string.Format("Unable to find `{0}` in search path ({1})", fileName, string.Join(";", NuBuildEnvironment.ExecutableSearchPaths.Select(p => p.ToString())));
                throw new InvalidOperationException(msg);
            }
            var absFilePath = AbsoluteFileSystemPath.FromRelative(relFilePath, NuBuildEnvironment.RootDirectoryPath);
            Logger.WriteLine(string.Format("{0} found at `{1}`.", fileName, absFilePath));
            return absFilePath;
        }

        private static IDictionary<string, string> GetVersionInfo(AbsoluteFileSystemPath exePath)
        {
            var invoker = SimpleProcessInvoker.Exec(exePath, "--version");
            if (invoker.ExitCode != 0)
            {
                var msg = string.Format("Unable to obtain version information from F* (exit code is {0}).", invoker.ExitCode);
                throw new Exception(msg);
            }
            var report = string.Format("`fstar.exe --version` reports:\n{0}\n", invoker.GetStdout());
            Logger.WriteLine(report, new [] { "info", "fstar" });
            var lines = invoker.GetStdout().Split(new[] { "\r\n", "\r", "\n" }, StringSplitOptions.RemoveEmptyEntries);
            var versionInfo = new Dictionary<string, string>();
            foreach (var line in lines)
            {
                var s = line.Trim();
                if (s.StartsWith("F* "))
                {
                    if (versionInfo.ContainsKey("version"))
                    {
                        var msg = string.Format("Ignoring duplicate field in F * version record: {0}", s);
                        Logger.WriteLine(msg, new[] { "warning", "fstar" });
                        continue;
                    }
                    versionInfo["version"] = s.Substring(3);
                    continue;
                }
                var split = s.Split(new[] { '=' });
                if (split.Length != 2)
                {
                    var msg = string.Format("Ignoring unrecognized output in F * version record: {0}", s);
                    Logger.WriteLine(msg, new[] { "warning", "fstar" });
                    continue;
                }
                var key = split[0];
                var value = split[1];
                if (versionInfo.ContainsKey(key))
                {
                    var msg = string.Format("Ignoring duplicate field in F * version record: {0}", s);
                    Logger.WriteLine(msg, new[] { "warning", "fstar" });
                    continue;
                }
                versionInfo[key] = value;
            }
            return versionInfo;
        }

        private static string HashVersionInfo(AbsoluteFileSystemPath path)
        {
            var commit = VersionInfo["commit"];
            if (commit != "unknown commit" && commit.EndsWith(" (dirty)"))
            {
                return Util.HashFileContents(path.ToString());
            }
            else
            {
                return Util.HashString(commit);
            }
        } 

        public static IEnumerable<RelativeFileSystemPath> DefaultModuleSearchPaths(bool universes)
        {
            return universes ? UniversesStandardLibrarySearchPaths : StandardLibrarySearchPaths;
        }

        private static IEnumerable<RelativeFileSystemPath> SelectExistingDirectoryPaths(IEnumerable<string> paths)
        {
            // F* defines more standard search paths than actually exist and rejects explicit specification of non-existent directories, so we need to filter out the paths that do not exist.
            var result = new List<RelativeFileSystemPath>();
            foreach (var s in paths)
            {
                var path = FileSystemPath.Join(HomeDirectoryPath, RelativeFileSystemPath.Parse(s, permitImplicit: true));
                if (Directory.Exists(path.ToString()))
                {
                    result.Add(path);
                }
            }
            return result;
        }
    }
}
