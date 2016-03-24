namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;

    public abstract class FileSystemPath
    {
        private readonly string normalized;

        protected FileSystemPath(string normalized)
        {
            if (normalized == null)
            {
                throw new ArgumentNullException("normalized");
            }

            this.normalized = normalized;
        }

        public override string ToString()
        {
            return this.normalized;
        }

        public string ToString(string option)
        {
            option = option.ToLower().Trim();
            if (option.Equals("i"))
            {
                return this.normalized.Substring(2);
            }
            else if (option.Contains("x"))
            {
                return this.ToString();
            }
            else
            {
                var msg = string.Format("Unrecognized formatting option `{0}`.", option);
                throw new ArgumentException(msg, "option");
            }
        }

        public string FileExtension
        {
            get
            {
                return Path.GetExtension(this.ToString());
            }
        }
        public string FileName
        {
            get
            {
                return Path.GetFileName(this.ToString());
            }
        }

        public string FileNameWithoutExtension
        {
            get
            {
                return Path.GetFileNameWithoutExtension(this.ToString());
            }
        }

        public static bool IsAbsolutePath(string pathStr)
        {
            return Path.IsPathRooted(pathStr);
        }

        public static bool IsRelativePath(string pathStr, bool permitImplicit = false)
        {
            if (Path.IsPathRooted(pathStr))
            {
                return false;
            }
            if (!permitImplicit)
            {
                return !IsImplicitRelativePath(pathStr);
            }
            return true;
        }

        public static RelativeFileSystemPath Join(RelativeFileSystemPath lhs, RelativeFileSystemPath rhs)
        {
            return RelativeFileSystemPath.Parse(Path.Combine(lhs.ToString(), rhs.ToString()));            
        }

        public static AbsoluteFileSystemPath Join(AbsoluteFileSystemPath lhs, RelativeFileSystemPath rhs)
        {
            return AbsoluteFileSystemPath.Parse(Path.Combine(lhs.ToString(), rhs.ToString()));
        }

        public static RelativeFileSystemPath MapToBuildObjectPath(string pathStr, WorkingDirectory workDir = null)
        {
            // todo: this is a candidate for relocating to BuildObject
            return AbsoluteFileSystemPath.Parse(pathStr).MapToBuildObjectPath(workDir);
        }

        protected static bool IsImplicitRelativePath(string s)
        {
            if (s == ".")
            {
                return false;
            }
            if (Path.IsPathRooted(s))
            {
                throw new ArgumentException("Absolute paths are disallowed.");
            }
            return !s.StartsWith("." + Path.DirectorySeparatorChar) && !s.StartsWith("." + Path.AltDirectorySeparatorChar);
        }

        protected static string Normalize(string pathStr)
        {
            string s;
            // remove trailing directory separator.
            if (pathStr.EndsWith(new string(Path.DirectorySeparatorChar, 1)) || pathStr.EndsWith(new string(Path.AltDirectorySeparatorChar, 1)))
            {
                s = pathStr.Substring(pathStr.Length - 1);
            }
            else
            {
                s = pathStr;
            }
            // canonicalize path separators.
            s = s.Replace(Path.AltDirectorySeparatorChar, Path.DirectorySeparatorChar);
            return s;
        }
        protected static IEnumerable<string> Split(string pathStr)
        {
            var components = new List<string>();
            var fileName = Path.GetFileName(pathStr);
            // if the path has a trailing "/" then GetFileName() will return an empty string.
            if (!string.IsNullOrWhiteSpace(fileName))
            {
                components.Add(fileName);
            }
            for (var s = Path.GetDirectoryName(pathStr); !string.IsNullOrWhiteSpace(s); s = Path.GetDirectoryName(s))
            {
                components.Add(Path.GetFileName(s));
            }
            components.Reverse();
            return components;
        }

    }

    public class AbsoluteFileSystemPath : FileSystemPath, IEquatable<AbsoluteFileSystemPath>, IComparable<AbsoluteFileSystemPath>
    {
        private AbsoluteFileSystemPath(string normalized) :
            base(normalized)
        {
        }

        public static AbsoluteFileSystemPath Parse(string pathStr, bool permitImplicit = false)
        {
            if (!permitImplicit || IsAbsolutePath(pathStr))
            {
                return new AbsoluteFileSystemPath(NormalizeAbsolute(pathStr));
            }
            else
            {
                return FromRelative(RelativeFileSystemPath.Parse(pathStr, permitImplicit: true), FromCurrentDirectory());
            }
        }

        public static AbsoluteFileSystemPath FromCurrentDirectory()
        {
            return Parse(Directory.GetCurrentDirectory());
        }

        public static AbsoluteFileSystemPath FromRelative(RelativeFileSystemPath relative, AbsoluteFileSystemPath prefix = null)
        {
            return Join(prefix ?? FromCurrentDirectory(), relative);
        }

        public bool HasPrefix(AbsoluteFileSystemPath prefix)
        {
            return this.ToString().StartsWith(prefix.ToString(), StringComparison.InvariantCultureIgnoreCase);
        }

        public bool IsExistingFile
        {
            get
            {
                return File.Exists(this.ToString());
            }
        }

        public bool IsExistingDirectory
        {
            get
            {
                return Directory.Exists(this.ToString());
            }
        }


        public bool ExistsAsFile
        {
            get
            {
                return File.Exists(this.ToString());
            }
        }

        public bool ExistsAsDirectory
        {
            get
            {
                return Directory.Exists(this.ToString());
            }
        }

        public AbsoluteFileSystemPath ParentDirectoryPath
        {
            get
            {
                var parent = Path.GetDirectoryName(this.ToString());
                return parent == null ? null : Parse(parent);
            }
        }

        public bool Equals(AbsoluteFileSystemPath other)
        {
            return other.ToString() == this.ToString();
        }

        public int CompareTo(AbsoluteFileSystemPath other)
        {
            return String.Compare(this.ToString(), other.ToString(), StringComparison.OrdinalIgnoreCase);
        }

        public override bool Equals(object obj)
        {
            var other = obj as AbsoluteFileSystemPath;
            return other != null && Equals(other);
        }

        public override int GetHashCode()
        {
            return this.ToString().GetHashCode();
        }

        public IEnumerable<AbsoluteFileSystemPath> ListFiles(bool recurse = false)
        {
            return Directory.EnumerateFiles(this.ToString(), "*", recurse ? SearchOption.AllDirectories : SearchOption.TopDirectoryOnly)
                .Select(s => Parse(s))
                .Where(p => !p.ExistsAsDirectory);
        }

        public RelativeFileSystemPath ExtractRelative(AbsoluteFileSystemPath prefix)
        {
            if (prefix.Equals(this))
            {
                return RelativeFileSystemPath.Parse(".");
            }

            var prefixStr = prefix.ToString();
            var thisStr = this.ToString();
            if (!this.HasPrefix(prefix))
            {
                var msg = string.Format("Unable to extract relative directory given mismatched prefix (`{0}`) with source path (`{1}`).", prefixStr, thisStr);
                throw new ArgumentException(msg, "prefix");
            }

            var relStr = thisStr.Substring(prefixStr.Length + 1, thisStr.Length - prefixStr.Length - 1);
            return RelativeFileSystemPath.Parse(relStr);
        }

        public AbsoluteFileSystemPath CreateSiblingPath(string filename)
        {
            var rhs = RelativeFileSystemPath.Parse(filename, permitImplicit: true);
            return Join(this.ParentDirectoryPath, rhs);
        }

        public AbsoluteFileSystemPath CreateChildPath(string filename)
        {
            var rhs = RelativeFileSystemPath.Parse(filename, permitImplicit: true);
            return Join(this, rhs);
        }

        public RelativeFileSystemPath MapToBuildObjectPath(WorkingDirectory workDir = null)
        {
            // todo: this is a candidate for relocating to BuildObject
            if (workDir == null)
            {
                return this.ExtractRelative(NuBuildEnvironment.RootDirectoryPath);
            }
            else
            {
                return this.ExtractRelative(Parse(workDir.Root));
            }
        }

        private static string NormalizeAbsolute(string pathStr)
        {
            if (!IsAbsolutePath(pathStr))
            {
                var msg = string.Format("Attempt to create an AbsoluteFileSystemPath with a non-absolute path (`{0}`).", pathStr);
                throw new ArgumentException(msg, "pathStr");
            }
            return Normalize(Path.GetFullPath(pathStr));
        }
    }

    public class RelativeFileSystemPath : FileSystemPath, IEquatable<RelativeFileSystemPath>, IComparable<RelativeFileSystemPath>
    {
        private RelativeFileSystemPath(string normalized) :
            base(normalized)
        {
        }

        public static RelativeFileSystemPath Parse(string pathStr, bool permitImplicit = false)
        {
            return new RelativeFileSystemPath(NormalizeRelative(permitImplicit ? ImplicitToRelative(pathStr) : pathStr));
        }

        public bool Equals(RelativeFileSystemPath other)
        {
            return other.ToString() == this.ToString();
        }

        public int CompareTo(RelativeFileSystemPath other)
        {
            return String.Compare(this.ToString(), other.ToString(), StringComparison.OrdinalIgnoreCase);
        }

        public override bool Equals(object obj)
        {
            var other = obj as RelativeFileSystemPath;
            return other != null && Equals(other);
        }

        public override int GetHashCode()
        {
            return this.ToString().GetHashCode();
        }

        public new string ToString(string fmt)
        {
            if (string.Equals(fmt, "i", StringComparison.InvariantCultureIgnoreCase))
            {
                return this.ToStringImplicit();
            }
            if (string.Equals(fmt, "n", StringComparison.InvariantCultureIgnoreCase))
            {
                return this.ToString();
            }
            var msg = string.Format("Unrecognized ToString() formatting code ('{0}').", fmt);
            throw new ArgumentException(msg, "fmt");
        }

        public RelativeFileSystemPath ParentDirectoryPath
        {
            get
            {
                return Parse(Path.GetDirectoryName(this.ToString()));
            }
        }

        public bool HasPrefix(RelativeFileSystemPath prefix)
        {
            return this.ToString().StartsWith(prefix.ToString(), StringComparison.InvariantCultureIgnoreCase);
        }

        public RelativeFileSystemPath CreateSiblingPath(string filename)
        {
            var rhs = RelativeFileSystemPath.Parse(filename, permitImplicit: true);
            return Join(this.ParentDirectoryPath, rhs);
        }

        public RelativeFileSystemPath CreateChildPath(string filename)
        {
            var rhs = Parse(filename, permitImplicit: true);
            return Join(this, rhs);
        }

        public RelativeFileSystemPath MapToBuildObjectPath(RelativeFileSystemPath prefix = null)
        {
            // todo: this is a candidate for relocating to BuildObject
            if (prefix == null || this.HasPrefix(prefix))
            {
                return this;
            }
            return Join(prefix, this);
        }

        private static string ImplicitToRelative(string s)
        {
            return IsImplicitRelativePath(s) ? "." + Path.DirectorySeparatorChar + s : s;
        }

        private string ToStringImplicit()
        {
            var s = this.ToString();
            return s.Substring(2);
        }

        private static string NormalizeRelative(string pathStr)
        {
            // the normalization technique used below doesn't work for the path `.`.
            if (pathStr == "." || pathStr == "." + Path.DirectorySeparatorChar || pathStr == "." + Path.AltDirectorySeparatorChar)
            {
                return ".";
            }

            if (Path.IsPathRooted(pathStr))
            {
                var msg = string.Format("Attempt to create an AbsoluteFileSystemPath with an absolute path (`{0}`).", pathStr);
                throw new ArgumentException(msg, "pathStr");
            }



            var dummyPrefix = @"C:\";
            var s0 = Path.GetFullPath(Path.Combine(dummyPrefix, pathStr));
            var s1 = s0.Substring(dummyPrefix.Length, s0.Length - dummyPrefix.Length);

            // Path.GetFullPath() will slice off any leading ".." components needed. the following code is an attempt to address this issue 
            var components = Split(pathStr);
            var minLevel = 0;
            var level = 0;
            foreach (var s in components)
            {
                if (s == ".")
                {
                    continue;
                }
                else if (s == "..")
                {
                    --level;
                    if (level < minLevel)
                    {
                        minLevel = level;
                    }
                }
                else
                {
                    ++level;
                }
            }
            for (var i = 0; i < Math.Abs(minLevel); ++i)
            {
                s1 = Path.Combine("..", s1);
            }

            return Normalize(ImplicitToRelative(s1));
        }
    }
}
