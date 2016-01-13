
namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;
    using System.IO;
    using System.Reflection;

    using Microsoft.CSharp.RuntimeBinder;
    using Microsoft.WindowsAzure.Storage;

    using NDepend.Path;

    using Newtonsoft.Json;

    public static class NuBuildEnvironment
    {
        public const string DotNuBuild = ".nubuild";
        public const string ConfigFileRelativePath = ".nubuild\\config.json";
        public const string LogPath = ".nubuild\\log.txt";

        public static IAbsoluteDirectoryPath InvocationPath { get; private set; }

        public static Options Options { get; private set; }
        private static IAbsoluteDirectoryPath rootDirectoryPath = null;


        public static void initialize(IDirectoryPath specifiedRootPath = null)
        {
            if (isInitialized())
            {
                throw new InvalidOperationException("Attempt to initialize NuBuildEnvironment twice.");
            }
            rootDirectoryPath = initNuBuildRoot(specifiedRootPath);
            Logger.Start(FileSystemPath.ImplicitToRelative(LogPath).ToRelativeFilePath().GetAbsolutePathFrom(rootDirectoryPath));
            Options = LoadConfig();
            InvocationPath = getInvocationPath(rootDirectoryPath);
            // NuBuild seems flakey unless invoked from the NuBuild root.
            Directory.SetCurrentDirectory(rootDirectoryPath.ToString());
        }

        public static bool isInitialized()
        {
            return rootDirectoryPath != null;
        }

        private static void throwIfNotInitialized()
        {
            if (!isInitialized())
            {
                throw new InvalidOperationException("NuBuildEnvironment is not yet intialized.");
            }
        }

        public static IAbsoluteDirectoryPath RootDirectoryPath
        {
            get
            {
                throwIfNotInitialized();
                return rootDirectoryPath;
            }
        }

        private static IAbsoluteDirectoryPath initNuBuildRoot(IDirectoryPath specifiedRootPath)
        {
            if (specifiedRootPath != null)
            {
                IAbsoluteDirectoryPath p;
                if (specifiedRootPath.IsRelativePath)
                {
                    p = ((IRelativeDirectoryPath)specifiedRootPath).GetAbsolutePathFrom(CurrentDirectoryPath);
                }
                else
                {
                    p = (IAbsoluteDirectoryPath)specifiedRootPath;
                }
                if (p.Exists && p.GetChildDirectoryWithName(DotNuBuild).Exists)
                {
                    Logger.WriteLine(string.Format("Specified NuBuild root path found at `{0}`.", p));
                    return p;
                }
                else
                {
                    throw new DirectoryNotFoundException(string.Format("Specified NuBuild root path (`{0}`) not found.", specifiedRootPath));
                }
            }
            else
            {
                var p = findNuBuildRoot();
                Logger.WriteLine(string.Format("NuBuild root found at `{0}`.", p));
                return p;
            }
        }

        public static IAbsoluteDirectoryPath CurrentDirectoryPath
        {
            get
            {
                return Directory.GetCurrentDirectory().ToAbsoluteDirectoryPath();
            }
        }

        public static IRelativeDirectoryPath ObjRootPath
        {
            get
            {
                var absPath = Path.Combine(RootDirectoryPath.ToString(), BuildEngine.theEngine.getObjRoot()).ToAbsoluteDirectoryPath();
                return absPath.GetRelativePathFrom(RootDirectoryPath);
            }
        }

        public static IAbsoluteDirectoryPath findNuBuildRoot()
        {
            var pwd = Directory.GetCurrentDirectory().ToAbsoluteDirectoryPath();
            for (var i = pwd; i != null; i = i.ParentDirectoryPath)
            {
                var p = i.GetChildDirectoryWithName(DotNuBuild);
                if (p.Exists)
                {
                    return i;
                }
            }

            throw new DirectoryNotFoundException(string.Format("Unable to find NuBuild root (`{0}`).", DotNuBuild));
        }

        public static string getDefaultIronRoot()
        {
            return RootDirectoryPath.ToString();
        }


        public static string getAssemblyPath()
        {
            string assyUri = Assembly.GetExecutingAssembly().CodeBase;
            string assyPath = new Uri(assyUri).LocalPath;
            return assyPath;
        }

        private static dynamic LoadConfig()
        {
            var path = System.IO.Path.Combine(RootDirectoryPath.ToString(), ConfigFileRelativePath).ToAbsoluteFilePath();
            var pathStr = path.ToString();
            if (path.Exists)
            {
                using (TextReader stream = File.OpenText(pathStr))
                {
                    var s = stream.ReadToEnd();
                    return Options.FromString(s);
                }
            }
            else
            {
                Logger.WriteLine(string.Format("Unable to find {0}; assuming empty document.", pathStr), "warning");
                return new Dictionary<string, object>();
            }
        }

        private static IAbsoluteDirectoryPath getInvocationPath(IAbsoluteDirectoryPath nuBuildRootPath)
        {
            var pwd = Directory.GetCurrentDirectory();
            return pwd.ToAbsoluteDirectoryPath().GetRelativePathFrom(nuBuildRootPath).GetAbsolutePathFrom(nuBuildRootPath);
        }
    }
}
