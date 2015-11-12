//--
// <copyright file="ContextContents.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    internal class ContextContents
        : VirtualContents
    {
        private IIncludePathContext context;

        public ContextContents(IIncludePathContext context)
        {
            this.context = context;
        }

        public IIncludePathContext Context
        {
            get { return this.context; }
        }
    }
}
