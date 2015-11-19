namespace NuBuild
{
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
    }
}
