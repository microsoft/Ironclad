using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    using System.Diagnostics;
    using System.IO;

    using NDepend.Path;

    public static class FStarEnvironment
    {
        private const string DefaultPathToFStarExe = ".\\bin\\fstar.exe";
        public static SourcePath PathToFStarExe { get; private set; }

        static FStarEnvironment()
        {
            findFStarExecutable();
        }

        private static void findFStarExecutable()
        {
            IRelativeFilePath relFilePath;
            var configStr = (string)NuBuild.NuBuildEnvironment.ConfigDotYaml.paths.fstar;
            if (configStr == null)
            {
                Logger.WriteLine(string.Format("[NuBuild] `{0}` entry `paths.fstar` is unspecifed; assuming default path (`{1}`)", NuBuild.NuBuildEnvironment.ConfigDotYamlRelativePath, DefaultPathToFStarExe));
                relFilePath = DefaultPathToFStarExe.ToRelativeFilePath();
            }
            else
            {
                relFilePath = FilePath.ImplicitToRelative(configStr);
            }

            var relDirPath = relFilePath.ParentDirectoryPath;
            var absFilePath = relDirPath.GetAbsolutePathFrom(NuBuildEnvironment.RootDirectoryPath);
            if (absFilePath.Exists)
            {
                Logger.WriteLine(string.Format("[NuBuild] F* found at `{0}`.", absFilePath));
                PathToFStarExe = new SourcePath(relFilePath.ToString(), SourcePath.SourceType.Tools);
            }
            else
            {
                var s = absFilePath.ToString();
                throw new FileNotFoundException(string.Format("A needed file (`{0}`) is missing. Please verify that the `paths.fstar` entry in your `{1}` file is accurate.", s, NuBuild.NuBuildEnvironment.ConfigDotYamlRelativePath));
            }
        }

        public static IList<BuildObject> getTools()
        {
            var result = new List<BuildObject>();

            result.Add(PathToFStarExe);
            // todo: need to add all dependencies.
            /*exeDepends.Add(new SourcePath("tools\\Dafny\\AbsInt.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BaseTypes.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\CodeContractsExtender.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Concurrency.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Core.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Dafny.exe.config", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\DafnyPipeline.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\DafnyPrelude.bpl", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Doomed.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\ExecutionEngine.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Graph.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Model.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\msvcp100.dll", SourcePath.SourceType.Tools));  // Needed by z3.
            exeDepends.Add(new SourcePath("tools\\Dafny\\msvcr100.dll", SourcePath.SourceType.Tools));  // Needed by z3.
            exeDepends.Add(new SourcePath("tools\\Dafny\\ParserHelper.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Provers.SMTLib.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\VCExpr.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\VCGeneration.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\vcomp100.dll", SourcePath.SourceType.Tools));  // Needed by z3.
            exeDepends.Add(new SourcePath("tools\\Dafny\\DafnyRuntime.cs", SourcePath.SourceType.Tools));  // Needed for compilation
            exeDepends.Add(new SourcePath("tools\\Dafny\\z3.exe", SourcePath.SourceType.Tools));*/

            return result;
        }

        private static List<IAbsoluteFilePath> findDependencies(SourcePath fstSource)
        {
            return new List<IAbsoluteFilePath>();
        }
    }
}
