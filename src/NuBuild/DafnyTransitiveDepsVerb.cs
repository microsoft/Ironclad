//--
// <copyright file="DafnyTransitiveDepsVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    internal class DafnyTransitiveDepsVerb
        : TransitiveDepsVerb
    {
        public DafnyTransitiveDepsVerb(BuildObject input)
            : base(input)
        {
        }

        protected override TransitiveDepsVerb factory(BuildObject obj)
        {
            return new DafnyTransitiveDepsVerb(obj);
        }

        protected override IIncludeFactory getIncludeFactory()
        {
            return new DafnyIncludes();
        }
    }
}
