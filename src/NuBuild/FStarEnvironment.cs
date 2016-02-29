using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    using System.Diagnostics;
    using System.IO;
    using System.Text.RegularExpressions;

    using Microsoft.CSharp.RuntimeBinder;

    public static class FStarEnvironment
    {
        private const string DefaultPathToFStarExe = ".\\.fstar\\bin\\fstar.exe";

        private static readonly AbsoluteFileSystemPath AbsolutePathToFStarExe;

        private static readonly List<SourcePath> Binaries;
        private static readonly List<SourcePath> StandardLibrary;

        public static readonly IDictionary<string, string> VersionInfo; 

        static FStarEnvironment()
        {
            var pathToFStarExe = findFStarExecutable();
            Binaries = findBinaries(pathToFStarExe);
            StandardLibrary = findStandardLibrary(pathToFStarExe);
            VersionInfo = GetVersionInfo(pathToFStarExe);
            AbsolutePathToFStarExe = pathToFStarExe;
        }

        public static RelativeFileSystemPath PathToFStarExe
        {
            get
            {
                return AbsolutePathToFStarExe.MapToBuildObjectPath();
            }
        }

        public static IEnumerable<SourcePath> getStandardDependencies()
        {
            return Binaries.Concat(StandardLibrary);
        }

        private static List<SourcePath> findBinaries(AbsoluteFileSystemPath pathToFStarExe)
        {
            AbsoluteFileSystemPath binPath = pathToFStarExe.ParentDirectoryPath;
            var result = new List<SourcePath>();

            result.Add(new SourcePath(pathToFStarExe.MapToBuildObjectPath().ToString(), SourcePath.SourceType.Tools, HashVersionInfo));

            var regExprs = new[] { new Regex(@".*\.dll$", RegexOptions.IgnoreCase), new Regex(@".*\.pdb$", RegexOptions.IgnoreCase), new Regex(@".*\.config$", RegexOptions.IgnoreCase) };
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
            return result;
        }

        private static List<SourcePath> findStandardLibrary(AbsoluteFileSystemPath pathToFStarExe)
        {
            var result = new List<SourcePath>();

            AbsoluteFileSystemPath libDir = pathToFStarExe.ParentDirectoryPath.CreateSiblingPath("lib");
            var libPaths = libDir.ListFiles(recurse: true);
            AbsoluteFileSystemPath contribDir = pathToFStarExe.ParentDirectoryPath.CreateSiblingPath("contrib");
            var contribFiles = contribDir.ListFiles(recurse: true);

            var paths = libPaths.Concat(contribFiles);
            foreach (var path in paths)
            {
                // todo: should these be added as sources?
                var nbPath = path.MapToBuildObjectPath().ToString();
                result.Add(new SourcePath(nbPath, SourcePath.SourceType.Tools));
            }
            return result;
        }

        private static AbsoluteFileSystemPath findFStarExecutable()
        {
            RelativeFileSystemPath relFilePath;
            string configStr;

            try
            {
                configStr = NuBuildEnvironment.Options.LookupPath("fstar", DefaultPathToFStarExe);
            }
            catch (RuntimeBinderException)
            {
                configStr = null;
            }

            if (configStr == null)
            {
                Logger.WriteLine(string.Format("`{0}` entry `paths.fstar` is unspecifed; assuming default path (`{1}`)", NuBuildEnvironment.ConfigFileRelativePath, DefaultPathToFStarExe));
                relFilePath = RelativeFileSystemPath.Parse(DefaultPathToFStarExe);
            }
            else
            {
                relFilePath = RelativeFileSystemPath.Parse(configStr, permitImplicit: true);
            }

            var absFilePath = AbsoluteFileSystemPath.FromRelative(relFilePath, NuBuildEnvironment.RootDirectoryPath);
            if (absFilePath.IsExistingFile)
            {
                Logger.WriteLine(string.Format("F* found at `{0}`.", absFilePath));
                return absFilePath;
            }
            else
            {
                var s = absFilePath.ToString();
                throw new FileNotFoundException(string.Format("A needed file (`{0}`) is missing. Please verify that the `paths.fstar` entry in your `{1}` file is accurate.", s, NuBuildEnvironment.ConfigFileRelativePath));
            }
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
    }
}
