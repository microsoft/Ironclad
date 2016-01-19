//--
// <copyright file="IIncludeFactory.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    internal interface IIncludeFactory
    {
        IEnumerable<BuildObject> getIncludes(BuildObject path);
    }
}
