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

        public static IRelativeFilePath AbsoluteToNuBuild(IAbsoluteFilePath absFilePath)
        {
            return absFilePath.GetRelativePathFrom(NuBuildEnvironment.RootDirectoryPath);
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

    }
}
