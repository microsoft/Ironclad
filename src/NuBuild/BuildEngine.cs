//--
// <copyright file="BuildEngine.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.IO;

    internal class BuildEngine
    {
        public const string VerveTrustedSpecDir = "Trusted\\Spec";

        private static BuildEngine _theEngine = new BuildEngine();

        private PathNormalizer pathNormalizer;
        private SourcePathIncludeContext vervePathContext;
        private string ironRoot;
        private Hasher hasher;
        private Repository repository;
        private CloudExecutionQueue cloudExecutionQueue;
        private string cloudReportQueueName;
        private ItemCacheCloud cloudItemCache;
        private IItemCache itemCache;
        private string localCacheLocation = "nucache";

        public BuildEngine()
        {
            this.pathNormalizer = new PathNormalizer();
            this.hasher = new Hasher();
        }

        public static BuildEngine theEngine
        {
            get { return _theEngine; }
        }

        internal Repository Repository
        {
            get { return this.repository; }
            set { this.repository = value; }
        }

        internal CloudExecutionQueue CloudExecutionQueue
        {
            get { return this.cloudExecutionQueue; }
            set { this.cloudExecutionQueue = value; }
        }

        internal string CloudReportQueueName
        {
            get { return this.cloudReportQueueName; }
            set { this.cloudReportQueueName = value; }
        }

        internal ItemCacheCloud CloudCache
        {
            get { return this.cloudItemCache; }
            set { this.cloudItemCache = value; }
        }

        internal IItemCache ItemCache
        {
            get { return this.itemCache; }
            set { this.itemCache = value; }
        }

        public SourcePathIncludeContext getVervePathContext()
        {
            if (this.vervePathContext == null)
            {
                Util.Assert(this.ironRoot != null);
                this.vervePathContext = new SourcePathIncludeContext();
                this.vervePathContext.addDirectory(VerveTrustedSpecDir);
                this.vervePathContext.addDirectory("Checked\\Nucleus\\Base");
                this.vervePathContext.addDirectory("Checked\\Nucleus\\GC");
                this.vervePathContext.addDirectory("Checked\\Nucleus\\Devices");
                this.vervePathContext.addDirectory("Checked\\Nucleus\\Main");

                this.vervePathContext.addDstExtension(BeatExtensions.BEATIFC_EXTN);
                this.vervePathContext.addDstExtension(BeatExtensions.BEATIMP_EXTN);
                this.vervePathContext.addDstExtension(BoogieAsmVerifyVerb.BASMIFC_EXTN);
                this.vervePathContext.addDstExtension(BoogieAsmVerifyVerb.BASMIMP_EXTN);
            }

            return this.vervePathContext;
        }

        public IContextGeneratingVerb getVerveContextVerb(PoundDefines poundDefines)
        {
            return new StaticContextVerb(this.getVervePathContext(), "Verve", poundDefines);
        }

        ////public TransitiveIncludesCache getDafnyIncludeCache()
        ////{
        ////    return dafnyIncludeCache;
        ////}

        ////public TransitiveIncludesCache getBeatIncludeCache(IIncludePathContext context)
        ////{
        ////    if (!contextToCache.ContainsKey(context))
        ////    {
        ////        contextToCache[context] = new TransitiveIncludesCache(new BeatIncludes(context));
        ////    }
        ////    return contextToCache[context];
        ////}

        public string getIronRoot()
        {
            return this.ironRoot;
        }

        internal void setIronRoot(string ironRoot)
        {
            this.ironRoot = this.pathNormalizer.normalizeAbsolutePath(ironRoot);
        }

        // Normalize the case of an ironRoot-relative path to the case present in the filesystem.
        internal string normalizeIronPath(string ironRelPath)
        {
            string abspath = this.pathNormalizer.normalizeAbsolutePath(Path.GetFullPath(Path.Combine(this.ironRoot, ironRelPath)));
            Util.Assert(abspath.StartsWith(this.ironRoot));
            return abspath.Substring(this.ironRoot.Length);
        }

        internal string getObjRoot()
        {
            return "nuobj";
        }

        internal string getSrcRoot()
        {
            return "src";
        }

        internal string getVirtualRoot()
        {
            return this.getObjRoot() + "\\virtual";  // Should never exist in filesystem!
        }

        internal string getToolsRoot()
        {
            return "tools";
        }

        internal string getBinToolsRoot()
        {
            return "bin_tools";
        }

        internal void setLocalCache(string path)
        {
            this.localCacheLocation = path;
        }

        internal string getLocalCache()
        {
            return this.localCacheLocation;
        }

        internal IHasher getHasher()
        {
            return this.hasher;
        }
    }
}
