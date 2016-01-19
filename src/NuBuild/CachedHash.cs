//--
// <copyright file="CachedHash.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    internal class CachedHash<HashedObjectType, ValueType>
    {
        private Dictionary<HashedObjectType, ValueType> hashCache;
        private HashFunc hashFunc;
        private FailureBehavior failureBehavior;
        private CachabilityTestFunc cachabilityTest;

        public CachedHash(
            HashFunc hashFunc,
            FailureBehavior failureBehavior = FailureBehavior.AssertFailures,
            CachabilityTestFunc cachabilityTest = null)
        {
            this.hashCache = new Dictionary<HashedObjectType, ValueType>();
            this.hashFunc = hashFunc;
            this.failureBehavior = failureBehavior;
            this.cachabilityTest = cachabilityTest;
        }

        public delegate ValueType HashFunc(HashedObjectType hashObj);

        public delegate bool CachabilityTestFunc(ValueType value);

        public enum FailureBehavior
        {
            IgnoreFailures,
            AssertFailures
        }

        public ValueType get(HashedObjectType hashObj)
        {
            if (!this.hashCache.ContainsKey(hashObj))
            {
                ValueType value = this.hashFunc(hashObj);
                if (value == null)
                {
                    Util.Assert(this.failureBehavior == FailureBehavior.IgnoreFailures);
                    return value;
                }
                else if (this.cachabilityTest != null && !this.cachabilityTest(value))
                {
                    return value;
                }
                else
                {
                    this.hashCache[hashObj] = value;
                }
            }

            return this.hashCache[hashObj];
        }
    }
}
