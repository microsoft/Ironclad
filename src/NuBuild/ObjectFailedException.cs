//--
// <copyright file="ObjectFailedException.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    internal class ObjectFailedException : Exception
    {
        public ObjectFailedException(BuildObject obj, Failed failed)
            : base(obj.ToString() + ": " + failed.ToString())
        {
        }
    }
}
