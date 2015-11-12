//--
// <copyright file="VerbOutputsContext.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    internal class VerbOutputsContext
        : IncludePathContext
    {
        private IVerb sourceVerb;
        private string descr;
        private HashSet<BuildObject> dafnyOutputs;
        private bool assertSuspiciousDafnyImpls;

        public VerbOutputsContext(IVerb sourceVerb, bool assertSuspiciousDafnyImpls)
        {
            this.sourceVerb = sourceVerb;
            this.descr = "VerbOutputs(" + sourceVerb + ")";
            this.assertSuspiciousDafnyImpls = assertSuspiciousDafnyImpls;
        }

        private HashSet<BuildObject> DafnyOutputs
        {
            get
            {
                if (this.dafnyOutputs == null)
                {
                    this.dafnyOutputs = new HashSet<BuildObject>(this.sourceVerb.getOutputs());
                }

                return this.dafnyOutputs;
            }
        }

        public override string ToString()
        {
            return this.descr;
        }

        public override BuildObject search(string basename, ModPart modPart)
        {
            // Kinda linear.
            ////Logger.WriteLine("Looking for " + basename);
            foreach (BuildObject obj in this.DafnyOutputs)
            {
                if (BeatExtensions.whichPart(obj) != modPart)
                {
                    continue;
                }

                ////Logger.WriteLine("  trying " + obj.getFileNameWithoutExtension() + " from " + obj);

                if (string.Equals(obj.getFileNameWithoutExtension(), basename, StringComparison.OrdinalIgnoreCase))
                {
                    if (this.assertSuspiciousDafnyImpls)
                    {
                        DafnyCCVerb.AssertSmellsImplementy(obj);
                    }

                    return obj;
                }
            }

            return null;
        }
    }
}
