
namespace NuBuild
{
    using System;
    using System.Linq;
    using System.IO;
    using System.Reflection;

    using Microsoft.CSharp.RuntimeBinder;
    using Microsoft.WindowsAzure.Storage;

    using NDepend.Path;

    using YamlDotNet.Dynamic;

    public static class NuBuildEnvironment
    {
        public const string DotNuBuild = ".nubuild";
        public const string ConfigDotYamlRelativePath = ".nubuild\\config.yaml";
        public const string LogPath = ".nubuild\\log.txt";

        public static IAbsoluteDirectoryPath InvocationPath { get; private set; }
        private static CloudStorageAccount cloudStorageAccount = null;

        private static IAbsoluteDirectoryPath rootDirectoryPath = null;
        private static dynamic configDotYaml = null;

        private static bool? colorizeOutput;

        public static void initialize(IDirectoryPath specifiedRootPath = null)
        {
            if (isInitialized())
            {
                throw new InvalidOperationException("Attempt to initialize NuBuildEnvironment twice.");
            }
            rootDirectoryPath = initNuBuildRoot(specifiedRootPath);
            Logger.Start(FileSystemPath.ImplicitToRelative(LogPath).ToRelativeFilePath().GetAbsolutePathFrom(rootDirectoryPath));
            configDotYaml = loadConfigDotYaml();
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

        public static dynamic ConfigDotYaml
        {
            get
            {
                throwIfNotInitialized();
                return configDotYaml;
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

        public static bool ColorizeOutput
        {
            get
            {
                const bool defaultValue = true;
                if (colorizeOutput.HasValue)
                {
                    return colorizeOutput.Value;
                }

                bool result;
                try
                {
                    result = (bool)ConfigDotYaml.options.colorize_output;
                }
                catch (RuntimeBinderException)
                {
                    result = defaultValue;
                }
                colorizeOutput = result;
                return result;
            }

            set
            {
                colorizeOutput = value;
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

        public static CloudStorageAccount CloudStorageAccount
        {
            get
            {
                if (cloudStorageAccount == null)
                {
                    var connectionString = (string)ConfigDotYaml.credentials.storage;
                    cloudStorageAccount = CloudStorageAccount.Parse(connectionString);
                }
                return cloudStorageAccount;
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

        static private dynamic loadConfigDotYaml()
        {
            var a = System.IO.Path.Combine(RootDirectoryPath.ToString(), ConfigDotYamlRelativePath).ToAbsoluteFilePath();
            var s = a.ToString();
            if (a.Exists)
            {
                return new DynamicYaml(YamlDoc.LoadFromFile(s));
            }
            else
            {
                Logger.WriteLine(string.Format("Unable to find {0}; assuming empty document.", s), "warning");
                return new DynamicYaml(YamlDoc.LoadFromString("---\n"));
            }
        }

        static private IAbsoluteDirectoryPath getInvocationPath(IAbsoluteDirectoryPath nuBuildRootPath)
        {
            var pwd = Directory.GetCurrentDirectory();
            return pwd.ToAbsoluteDirectoryPath().GetRelativePathFrom(nuBuildRootPath).GetAbsolutePathFrom(nuBuildRootPath);
        }
    }
}
