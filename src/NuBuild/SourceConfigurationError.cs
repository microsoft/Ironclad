//--
// <copyright file="SourceConfigurationError.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    internal class SourceConfigurationError : Exception
    {
        public SourceConfigurationError(string msg)
            : base(msg)
        {
        }
    }
}
