using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    using System.Data.Common;
    using System.Diagnostics;
    using System.IO;
    using System.Text.RegularExpressions;

    using Microsoft.CSharp.RuntimeBinder;

    public static class FStarEnvironment
    {
        private const string DefaultPathToFStarExe = ".\\.fstar\\bin\\fstar.exe";

        private static readonly AbsoluteFileSystemPath AbsolutePathToFStarExe;
        private static readonly IEnumerable<string> ImplicitDependencies = new[] { "./lib/prims.fst" };

        public static readonly IEnumerable<SourcePath> Binaries;
        public static readonly IEnumerable<SourcePath> StandardLibrary;


        // the following list of default module search paths must match what's listed in `fstar/src/options.fs`.
        // don't include the current directory, however.
        // todo: it would be nice to be able to query F* for this list so that it does not need to be manually synchronized.
        private static readonly List<RelativeFileSystemPath> StandardLibrarySearchPaths = 
            (new[]
             {
                "./lib",
                "./lib/fstar",
                "./stdlib",
                "./stdlib/fstar",
             })
            .Select(s => RelativeFileSystemPath.Parse(s)).ToList();

        static FStarEnvironment()
        {
            var pathToFStarExe = findFStarExecutable();
            Binaries = findBinaries(pathToFStarExe);
            StandardLibrary = findStandardLibrary(pathToFStarExe);
            AbsolutePathToFStarExe = pathToFStarExe;

        }

        public static RelativeFileSystemPath PathToFStarExe
        {
            get
            {
                return AbsolutePathToFStarExe.MapToBuildObjectPath();
            }
        }

        public static RelativeFileSystemPath HomeDirectoryPath
        {
            get
            {
                return PathToFStarExe.ParentDirectoryPath.ParentDirectoryPath;
            }
        }

        public static IEnumerable<SourcePath> GetStandardDependencies()
        {
            return Binaries.Concat(ImplicitDependencies.Select(s => new SourcePath(s)));
        }

        private static List<SourcePath> findBinaries(AbsoluteFileSystemPath pathToFStarExe)
        {
            AbsoluteFileSystemPath binPath = pathToFStarExe.ParentDirectoryPath;
            var result = new List<SourcePath>();

            result.Add(new SourcePath(pathToFStarExe.MapToBuildObjectPath().ToString(), SourcePath.SourceType.Tools));

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

        public static IEnumerable<RelativeFileSystemPath> DefaultModuleSearchPaths
        {
            get
            {
                foreach (var relPath in StandardLibrarySearchPaths)
                {
                    yield return FileSystemPath.Join(HomeDirectoryPath, relPath);
                }
            }
        }
    }
}
