//--
// <copyright file="IIncludePathContext.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    internal interface IIncludePathContext
    {
        BuildObject search(string basename, ModPart modPart = ModPart.Ifc);
    }
}
