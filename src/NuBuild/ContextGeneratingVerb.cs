//--
// <copyright file="ContextGeneratingVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;

    internal abstract class ContextGeneratingVerb
        : Verb, IContextGeneratingVerb
    {
        public const string CONTEXT_EXTN = ".ctxt";    // Virtual, so it shouldn't appear in filesystem.
        private int version = 1;

        private string nickname;
        private PoundDefines poundDefines;
        private BuildObject outputObj;

        /// <param name="nickname">NB nickname will need to be unique over a run; it's used as the verb AbstractIdentifier, and
        /// hence hash identity in caches.</param>
        public ContextGeneratingVerb(string nickname, PoundDefines poundDefines)
        {
            this.nickname = nickname;
            this.poundDefines = poundDefines;
        }

        public PoundDefines getPoundDefines()
        {
            return this.poundDefines;
        }

        public string getContextIdentifier()
        {
            return this.nickname;
        }

        public override AbstractId getAbstractIdentifier()
        {
            return new AbstractId(this.GetType().Name, this.version, this.getContextIdentifier());
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new BuildObject[] { this.getContextOutput() };
        }

        public BuildObject getContextOutput()
        {
            if (this.outputObj == null)
            {
                this.outputObj = new VirtualBuildObject(
                    Path.Combine(BuildEngine.theEngine.getVirtualRoot(), Util.mungeClean(this.getAbstractIdentifier().ToString()) + CONTEXT_EXTN));
            }

            return this.outputObj;
        }
    }

    internal static class ContextGeneratingVerbExtensions
    {
        internal static IIncludePathContext fetchIfAvailable(this IContextGeneratingVerb verb, ref DependencyDisposition ddisp)
        {
            try
            {
                return ((ContextContents)
                    BuildEngine.theEngine.Repository.FetchVirtual(verb.getContextOutput())).Context;
            }
            catch (ObjectNotReadyException)
            {
                // Oh, we don't even have the context object yet.
                ddisp = ddisp.combine(DependencyDisposition.Incomplete);
            }
            catch (ObjectFailedException)
            {
                ddisp = ddisp.combine(DependencyDisposition.Failed);
            }

            return null;
        }
    }
}
