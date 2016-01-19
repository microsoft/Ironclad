//--
// <copyright file="Hasher.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    /// <summary>
    /// Strange mixture of hash-related functionality and a
    /// mapping from build objects to the verbs that created them?
    /// Actually, looks like everything here would more appropriately be elsewhere.
    /// DONE: Move outputToVerbMap to Scheduler.
    /// DONE: Move marshalledFilesystemPaths to Repository.
    /// TODO: Move contextResolutionCache to boogie/asm something or other.
    /// TODO: Move parsedIncludesCache to BeatIncludes?
    /// </summary>
    internal class Hasher : IHasher
    {
        private CachedHash<Tuple<IIncludePathContext, string, ModPart>, BuildObject> contextResolutionCache;

        private CachedHash<Tuple<IIncludePathContext, BuildObject>, List<BeatIncludes.LabeledInclude>> parsedIncludesCache;

        public Hasher()
        {
            this.contextResolutionCache = new CachedHash<Tuple<IIncludePathContext, string, ModPart>, BuildObject>(
                delegate(Tuple<IIncludePathContext, string, ModPart> key)
                {
                    return key.Item1.search(key.Item2, key.Item3);
                });

            this.parsedIncludesCache = new CachedHash<Tuple<IIncludePathContext, BuildObject>, List<BeatIncludes.LabeledInclude>>(
                delegate(Tuple<IIncludePathContext, BuildObject> key)
                {
                    return BeatIncludes.parseLabeledIncludes(key.Item1, key.Item2);
                });
        }

        public BuildObject search(IIncludePathContext context, string modName, ModPart modPart)
        {
            return this.contextResolutionCache.get(new Tuple<IIncludePathContext, string, ModPart>(context, modName, modPart));
        }

        public List<BeatIncludes.LabeledInclude> getParsedIncludes(IIncludePathContext context, BuildObject beatsrc)
        {
            return this.parsedIncludesCache.get(new Tuple<IIncludePathContext, BuildObject>(context, beatsrc));
        }
    }
}
