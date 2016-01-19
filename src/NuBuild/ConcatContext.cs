//--
// <copyright file="ConcatContext.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    internal class ConcatContext
        : IncludePathContext
    {
        private List<IIncludePathContext> contexts;
        private string descr;
        
        public ConcatContext(IEnumerable<IIncludePathContext> contexts)
        {
            this.contexts = new List<IIncludePathContext>(contexts);
            this.descr = "Context(" + string.Join(",", this.contexts) + ")";
        }

        public override string ToString()
        {
            return this.descr;
        }

        public override BuildObject search(string basename, ModPart modPart = ModPart.Ifc)
        {
            foreach (IIncludePathContext context in this.contexts)
            {
                BuildObject obj = context.search(basename, modPart);
                if (obj != null)
                {
                    return obj;
                }
            }

            return null;
        }
    }
}
