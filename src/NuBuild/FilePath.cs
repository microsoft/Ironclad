namespace NuBuild
{
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;

    using NDepend.Path;

    public static class FilePath
    {
        public static IRelativeFilePath ImplicitToRelative(string s)
        {
            if (!s.StartsWith(".\\") && !s.StartsWith("./"))
            {
                return (".\\" + s).ToRelativeFilePath();
            }
            else
            {
                return s.ToRelativeFilePath();
            }
        }

        public static string RelativeToImplicit(IRelativeFilePath relFilePath)
        {
            var s = relFilePath.ToString();
            return s.Substring(2);
        }


        public static IRelativeFilePath AbsoluteToNuBuild(IAbsoluteFilePath absFilePath, WorkingDirectory workDir = null)
        {
            if (workDir == null)
            {
                return absFilePath.GetRelativePathFrom(NuBuildEnvironment.RootDirectoryPath);
            }
            else
            {
                return absFilePath.GetRelativePathFrom(workDir.Root.ToAbsoluteDirectoryPath());
            }
        }

        
        public static IEnumerable<IAbsoluteFilePath> GetListing(IAbsoluteDirectoryPath dirPath, bool recurse = false)
        {
            return 
                Galactic.FileSystem.Directory.GetListing(dirPath.ToString(), true)
                .Where(s => !s.IsValidAbsoluteDirectoryPath() || !ExistsAndIsReallyDirectory(s.ToAbsoluteDirectoryPath()))
                .Select(s => s.ToAbsoluteFilePath());
        }

        private static bool ExistsAndIsReallyDirectory(IAbsoluteDirectoryPath path)
        {
            try
            {
                var dirInfo = path.DirectoryInfo;

            }
            catch (DirectoryNotFoundException)
            {
                return false;
            }
            return true;
        }

        public static IRelativeFilePath StringToNuBuildPath(string s)
        {
            var absPathStr = Path.GetFullPath(s);
            return AbsoluteToNuBuild(absPathStr.ToAbsoluteFilePath());
        }

        public static string NormalizeImplicit(string s)
        {
            return RelativeToImplicit(ImplicitToRelative(s));
        }
    }
}
