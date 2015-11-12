//--
// <copyright file="IVerificationResultParser.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    internal interface IVerificationResultParser
    {
        void parseOutput(
            string s,
            out int parseFailures,
            out int verificationFailures,
            out int timeouts);
    }
}
