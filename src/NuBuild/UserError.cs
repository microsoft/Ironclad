//--
// <copyright file="UserError.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    internal class UserError : Exception
    {
        public UserError(string msg)
            : base(msg)
        {
        }
    }
}
