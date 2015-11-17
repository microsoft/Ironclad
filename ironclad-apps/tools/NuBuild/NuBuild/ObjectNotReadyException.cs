//--
// <copyright file="ObjectNotReadyException.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    internal class ObjectNotReadyException : Exception
    {
        public ObjectNotReadyException(BuildObject obj)
            : base(obj.ToString())
        {
        }
    }
}
