//--
// <copyright file="IAsmProducer.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    internal interface IAsmProducer : IVerb
    {
        BuildObject getAsmFile();
    }
}
