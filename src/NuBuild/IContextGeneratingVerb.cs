//--
// <copyright file="IContextGeneratingVerb.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    internal interface IContextGeneratingVerb
        : IVerb
    {
        string getContextIdentifier();

        PoundDefines getPoundDefines();

        BuildObject getContextOutput();
    }
}
