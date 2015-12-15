namespace NuBuild
{
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;

    using NDepend.Path;

    public static class FileSystemPath
    {
        public static IRelativeFilePath ImplicitPathStringToRelativeFilePath(string s)
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

        public static string ToImplicitPathString(this IRelativePath @this)
        {
            var s = @this.ToString();
            return s.Substring(2);
        }


        public static IRelativeFilePath ToBuildObjectPath(this IAbsoluteFilePath @this, WorkingDirectory workDir = null)
        {
            if (workDir == null)
            {
                return @this.GetRelativePathFrom(NuBuildEnvironment.RootDirectoryPath);
            }
            else
            {
                return @this.GetRelativePathFrom(workDir.Root.ToAbsoluteDirectoryPath());
            }
        }

        
        public static IEnumerable<IAbsoluteFilePath> ListFiles(IAbsoluteDirectoryPath dirPath, bool recurse = false)
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

        public static IRelativeFilePath ToBuildObjectPath(this string pathStr, WorkingDirectory workDir = null)
        {
            return Path.GetFullPath(pathStr).ToAbsoluteFilePath().ToBuildObjectPath(workDir);
        }

        public static string NormalizeImplicitPathString(string s)
        {
            return ToImplicitPathString(ImplicitPathStringToRelativeFilePath(s));
        }
    }
}
