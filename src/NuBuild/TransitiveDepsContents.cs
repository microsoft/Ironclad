//--
// <copyright file="TransitiveDepsContents.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;
    using System.Text;
    using System.Threading.Tasks;

    internal class TransitiveDepsContents : VirtualContents
    {
        OrderPreservingSet<BuildObject> _shallowDeps, _transitiveDeps;

        public IEnumerable<BuildObject> shallowDeps
        {
            get { return this._shallowDeps; }
        }

        public IEnumerable<BuildObject> transitiveDeps
        {
            get { return this._transitiveDeps; }
        }

        public TransitiveDepsContents(OrderPreservingSet<BuildObject> shallowDeps, OrderPreservingSet<BuildObject> transitiveDeps)
        {
            this._shallowDeps = shallowDeps;
            this._transitiveDeps = transitiveDeps;
        }

        ////public override string getConcreteSummary()
        ////{
        ////    return "(" + String.Join(",", transitiveDeps) + ")";
        ////}
    }
}
