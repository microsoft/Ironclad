//--
// <copyright file="IncludePathContext.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    internal abstract class IncludePathContext
        : IIncludePathContext
    {
        public abstract BuildObject search(string basename, ModPart modPart = ModPart.Ifc);

        public override int GetHashCode()
        {
            return ToString().GetHashCode();
        }

        public override bool Equals(object obj)
        {
            return ToString().Equals(obj.ToString());
        }
    }
}
