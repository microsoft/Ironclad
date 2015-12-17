namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;

    using NDepend.Path;

    public static class FileSystemPath
    {
        public static string ImplicitToRelative(string s)
        {
            // todo: replace with pre-defined constants, et al.
            if (!s.StartsWith(".\\") && !s.StartsWith("./"))
            {
                return ".\\" + s;
            }
            else
            {
                return s;            
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
                Directory.EnumerateFiles(dirPath.ToString(), "*", SearchOption.TopDirectoryOnly)
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

        public static bool HasPrefix(this IAbsolutePath path, IAbsolutePath prefix)
        {
            return path.ToString().StartsWith(prefix.ToString(), StringComparison.InvariantCultureIgnoreCase);
        }

        public static bool HasPrefix(this IRelativePath path, IRelativePath prefix)
        {
            return path.ToString().StartsWith(prefix.ToString(), StringComparison.InvariantCultureIgnoreCase);
        }

        public static IRelativeFilePath ToBuildObjectPath(this IRelativeFilePath path, IRelativeDirectoryPath prefix)
        {
            if (prefix == null || path.HasPrefix(prefix))
            {
                return path.ToString().ToRelativeFilePath();
            }
            else
            {

                return Join(prefix, path);
            }
        }

        public static IRelativeFilePath Join(IRelativeDirectoryPath lhs, IRelativeFilePath rhs)
        {
            return Path.Combine(lhs.ToString(), rhs.ToString()).ToRelativeFilePath();            
        }

        public static IAbsoluteDirectoryPath Join(IAbsoluteDirectoryPath lhs, IRelativeDirectoryPath rhs)
        {
            return Path.Combine(lhs.ToString(), rhs.ToString()).ToAbsoluteDirectoryPath();            
        }

        public static IAbsoluteFilePath Join(IAbsoluteDirectoryPath lhs, IRelativeFilePath rhs)
        {
            return Path.Combine(lhs.ToString(), rhs.ToString()).ToAbsoluteFilePath();            
        }

        public static IRelativeDirectoryPath Join(IRelativeDirectoryPath lhs, IRelativeDirectoryPath rhs)
        {
            return Path.Combine(lhs.ToString(), rhs.ToString()).ToRelativeDirectoryPath();            
        }


        public static IRelativeFilePath ToBuildObjectPath(this string pathStr, WorkingDirectory workDir = null)
        {
            return Path.GetFullPath(pathStr).ToAbsoluteFilePath().ToBuildObjectPath(workDir);
        }

        public static string NormalizeImplicitPathString(string s)
        {
            return ImplicitToRelative(s).ToRelativeFilePath().ToImplicitPathString();
        }
    }
}
