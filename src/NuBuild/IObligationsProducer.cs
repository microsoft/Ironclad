//--
// <copyright file="IObligationsProducer.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
 
    internal interface IObligationsProducer : IVerb
    {
        BuildObject getObligationSet();

        ////BuildObject getIdentifier();
    }
}
