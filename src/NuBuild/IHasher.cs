//--
// <copyright file="IHasher.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    /// <summary>
    /// REVIEW: Why is this an interface?
    /// </summary>
    internal interface IHasher
    {
        BuildObject search(IIncludePathContext context, string modName, ModPart modPart);

        List<BeatIncludes.LabeledInclude> getParsedIncludes(IIncludePathContext context, BuildObject beatsrc);
    }
}
