//--
// <copyright file="ObjectMissingFromCacheException.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    internal class ObjectMissingFromCacheException : Exception
    {
        private string itemHash;

        public ObjectMissingFromCacheException(string itemHash, string msg)
            : base(string.Format("item {0} missing from cache: {1}", itemHash, msg))
        {
            this.itemHash = itemHash;
        }
    }
}
