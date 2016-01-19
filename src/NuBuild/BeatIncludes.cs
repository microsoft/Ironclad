//--
// <copyright file="BeatIncludes.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Diagnostics;
    using System.IO;
    using System.Linq;
    using System.Text.RegularExpressions;

    internal class BeatIncludes
    {
        private static CachedHash<IIncludePathContext, FetchModuleCache> fetchModuleCaches
            = new CachedHash<IIncludePathContext, FetchModuleCache>(delegate(IIncludePathContext context)
                {
                    return new FetchModuleCache(context);
                });

        private IIncludePathContext includePathSearcher;

        public BeatIncludes(IIncludePathContext includePathSearcher)
        {
            this.includePathSearcher = includePathSearcher;
        }

        public enum ImportFilter
        {
            ForBeatOrBasm,
            ForBasmOnly
        }

        public static List<LabeledInclude> parseLabeledIncludes(IIncludePathContext context, BuildObject beatsrc)
        {
            ////Logger.WriteLine("parseLabeledIncludes " + beatsrc.getRelativePath() + " context " + context.GetHashCode());

            List<LabeledInclude> outlist = new List<LabeledInclude>();
            ////Regex re = new Regex("^\\s*import\\s*([^\\s,]*(,\\s*[^\\s,]*)*)\\s*;");
            // TODO allow commented-out imports until Beat accepts (ignores) them in ifcs files.
            Regex import_re = new Regex("^[\\s/-]*private-import\\s*([^\\s,]*(,\\s*[^\\s,]*)*)\\s*;");
            Regex basmonly_re = new Regex("^[\\s/-]*private-basmonly-import\\s*([^\\s,]*(,\\s*[^\\s,]*)*)\\s*;");
            FetchModuleCache fmcache = fetchModuleCaches.get(context);
            using (TextReader tr = BuildEngine.theEngine.Repository.OpenRead(beatsrc))
            {
                while (true)
                {
                    string line = tr.ReadLine();
                    if (line == null)
                    {
                        break;
                    }

                    Match match = import_re.Match(line);
                    if (match.Success)
                    {
                        outlist.Add(new LabeledInclude(ImportFilter.ForBeatOrBasm, fmcache.get(match.Groups[1].ToString())));
                    }

                    match = basmonly_re.Match(line);
                    if (match.Success)
                    {
                        outlist.Add(new LabeledInclude(ImportFilter.ForBasmOnly, fmcache.get(match.Groups[1].ToString())));
                    }
                }

                ////Logger.WriteLine(string.Format("{0} includes {1} things", dfysource.getFilesystemPath(), outlist.Count));
                return outlist;
            }
        }

        public List<LabeledInclude> getLabeledIncludes(BuildObject beatsrc)
        {
            ////return caches.get(includePathSearcher).get(beatsrc);
            return this.computeLabeledIncludes(beatsrc);
        }

        public IEnumerable<BuildObject> getBasmIncludes(BuildObject beatsrc)
        {
            return this.computeLabeledIncludes(beatsrc).Select(li => li.buildObject);
        }

        protected List<LabeledInclude> computeLabeledIncludes(BuildObject beatsrc)
        {
            return BuildEngine.theEngine.getHasher().getParsedIncludes(this.includePathSearcher, beatsrc);
        }

        private BuildObject fetchModule(string module)
        {
            ////Logger.WriteLine("fetchmodule " + module + " ctx " + includePathSearcher.GetHashCode());
            string includedModule = module.Trim();
            BuildObject path = this.includePathSearcher.search(includedModule);
            if (path == null)
            {
                throw new SourceConfigurationError(
                    string.Format(
                        "Cannot find module {0} in search path {1}",
                        includedModule,
                        this.includePathSearcher));
            }

            return path;
        }

        public class LabeledInclude
        {
            public ImportFilter importFilter;
            public BuildObject buildObject;

            public LabeledInclude(ImportFilter importFilter, BuildObject buildObject)
            {
                this.importFilter = importFilter;
                this.buildObject = buildObject;
            }
        }

        private class FetchModuleCache
        {
            private CachedHash<string, BuildObject> cache;
            private BeatIncludes beatIncludes;

            public FetchModuleCache(IIncludePathContext context)
            {
                this.beatIncludes = new BeatIncludes(context);
                this.cache = new CachedHash<string, BuildObject>(this.fetchModule);
            }

            public BuildObject get(string module)
            {
                return this.cache.get(module);
            }

            private BuildObject fetchModule(string module)
            {
                return this.beatIncludes.fetchModule(module);
            }
        }
    }
}
