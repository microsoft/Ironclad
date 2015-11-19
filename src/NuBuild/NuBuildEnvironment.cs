
namespace NuBuild
{
    using System;
    using System.Linq;
    using System.IO;
    using System.Reflection;

    using Microsoft.WindowsAzure.Storage;

    using NDepend.Path;

    using YamlDotNet.Dynamic;

    public static class NuBuildEnvironment
    {
        public const string DotNuBuild = ".nubuild";
        public const string ConfigDotYamlRelativePath = ".nubuild\\config.yaml";
        private static CloudStorageAccount cloudStorageAccount = null;

        public static dynamic ConfigDotYaml { get; private set; }
        public static IAbsoluteDirectoryPath RootDirectoryPath { get; private set; }

        static NuBuildEnvironment()
        {
            RootDirectoryPath = findNuBuildRoot();
            ConfigDotYaml = loadConfigDotYaml();
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

        public static IAbsoluteDirectoryPath findNuBuildRoot()
        {
            var pwd = Directory.GetCurrentDirectory().ToAbsoluteDirectoryPath();
            for (var i = pwd; i != null; i = i.ParentDirectoryPath)
            {
                var p = i.GetChildDirectoryWithName(DotNuBuild);
                if (p.Exists)
                {
                    Logger.WriteLine(string.Format("[NuBuild] NuBuild root found at `{0}`.", i));
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
                Logger.WriteLine(string.Format("[NuBuild] Unable to find {0}; assuming empty document.", s));
                return new DynamicYaml(YamlDoc.LoadFromString("---\n"));
            }
        }
    }
}
