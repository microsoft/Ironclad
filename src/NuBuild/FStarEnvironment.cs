using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    using System.Diagnostics;
    using System.IO;

    using Microsoft.CSharp.RuntimeBinder;

    using Minimatch;

    using NDepend.Path;

    public static class FStarEnvironment
    {
        private const string DefaultPathToFStarExe = ".\\bin\\fstar.exe";

        private static readonly IAbsoluteFilePath AbsolutePathToFStarExe;

        private static readonly List<SourcePath> Binaries;
        private static readonly List<SourcePath> StandardLibrary;

        static FStarEnvironment()
        {
            var pathToFStarExe = findFStarExecutable();
            Binaries = findBinaries(pathToFStarExe);
            StandardLibrary = findStandardLibrary(pathToFStarExe);
            AbsolutePathToFStarExe = pathToFStarExe;
        }

        public static IRelativeFilePath PathToFStarExe
        {
            get
            {
                return AbsolutePathToFStarExe.ToBuildObjectPath();
            }
        }

        public static IEnumerable<SourcePath> getStandardDependencies()
        {
            return Binaries.Concat(StandardLibrary);
        }

        private static List<SourcePath> findBinaries(IAbsoluteFilePath pathToFStarExe)
        {
            IAbsoluteDirectoryPath binPath = pathToFStarExe.ParentDirectoryPath;
            var result = new List<SourcePath>();

            result.Add(new SourcePath(pathToFStarExe.ToBuildObjectPath().ToString(), SourcePath.SourceType.Tools));

            var globs = new[] { new Minimatcher("*.dll"), new Minimatcher("*.pdb"), new Minimatcher("*.config") };
            var paths = FileSystemPath.ListFiles(binPath, recurse: true);
            foreach (var path in paths)
            {
                foreach (var glob in globs)
                {
                    if (glob.IsMatch(path.ToString()))
                    {
                        var nbPath = path.ToBuildObjectPath().ToString();
                        result.Add(new SourcePath(nbPath, SourcePath.SourceType.Tools));
                        break;
                    }
                }
            }
            return result;
        }

        private static List<SourcePath> findStandardLibrary(IAbsoluteFilePath pathToFStarExe)
        {
            IAbsoluteDirectoryPath libPath = pathToFStarExe.ParentDirectoryPath.GetBrotherDirectoryWithName("lib");
            var result = new List<SourcePath>();

            var globs = new[] { new Minimatcher("*") };
            var paths = FileSystemPath.ListFiles(libPath, recurse: true);
            foreach (var path in paths)
            {
                foreach (var glob in globs)
                {
                    if (glob.IsMatch(path.ToString()))
                    {
                        // todo: should these be added as sources?
                        var nbPath = path.ToBuildObjectPath().ToString();
                        result.Add(new SourcePath(nbPath, SourcePath.SourceType.Tools));
                        break;
                    }
                }
            }
            return result;
        }

        private static IAbsoluteFilePath findFStarExecutable()
        {
            IRelativeFilePath relFilePath;
            string configStr;

            try
            {
                configStr = (string)NuBuildEnvironment.ConfigDotYaml.paths.fstar;
            }
            catch (RuntimeBinderException)
            {
                configStr = null;
            }

            if (configStr == null)
            {
                Logger.WriteLine(string.Format("[NuBuild] `{0}` entry `paths.fstar` is unspecifed; assuming default path (`{1}`)", NuBuild.NuBuildEnvironment.ConfigDotYamlRelativePath, DefaultPathToFStarExe));
                relFilePath = DefaultPathToFStarExe.ToRelativeFilePath();
            }
            else
            {
                relFilePath = FileSystemPath.ImplicitPathStringToRelativeFilePath(configStr);
            }

            var absFilePath = relFilePath.GetAbsolutePathFrom(NuBuildEnvironment.RootDirectoryPath);
            if (absFilePath.Exists)
            {
                Logger.WriteLine(string.Format("[NuBuild] F* found at `{0}`.", absFilePath));
                return absFilePath;
            }
            else
            {
                var s = absFilePath.ToString();
                throw new FileNotFoundException(string.Format("A needed file (`{0}`) is missing. Please verify that the `paths.fstar` entry in your `{1}` file is accurate.", s, NuBuildEnvironment.ConfigDotYamlRelativePath));
            }
        }
    }
}
