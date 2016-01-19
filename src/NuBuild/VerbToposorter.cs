//--
// <copyright file="VerbToposorter.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    /// <summary>
    /// Mechanism for ordering verbs topologically.
    /// Used by the Scheduler and related components.
    /// </summary>
    internal class VerbToposorter
        : IComparer<IVerb>
    {
        /// <summary>
        /// Mapping of verbs to their verb depth.
        /// </summary>
        private Dictionary<IVerb, int> verbDepth;

        /// <summary>
        /// Initializes a new instance of the <see cref="VerbToposorter"/>
        /// class.
        /// </summary>
        public VerbToposorter()
        {
            this.verbDepth = new Dictionary<IVerb, int>();
        }

        /// <summary>
        /// Compares two verbs topologically.
        /// </summary>
        /// <remarks>
        /// This is the IComparer.Compare method.
        /// </remarks>
        /// <param name="x">One verb to compare.</param>
        /// <param name="y">The other verb to compare.</param>
        /// <returns>
        /// A signed integer that indicates the relative values of x and y,
        /// see IComparer.Compare interface.
        /// </returns>
        public int Compare(IVerb x, IVerb y)
        {
            int rc;
            int c0 = this.GetDepth(x) - this.GetDepth(y);
            if (c0 != 0)
            {
                rc = c0;
            }
            else
            {
                // Break depth ties alphabetically.
                rc = x.ToString().CompareTo(y.ToString());
            }

            ////Logger.WriteLine(String.Format("Compare({0},{1})=={2}", x, y, rc));
            return rc;
        }

        /// <summary>
        /// Gets the "depth" (dependency order) of a verb.
        /// </summary>
        /// <param name="verb">The verb in question.</param>
        /// <returns>The verb depth.</returns>
        private int GetDepth(IVerb verb)
        {
            if (this.verbDepth.ContainsKey(verb))
            {
                return this.verbDepth[verb];
            }

            int depth;
            DafnyVerifyOneVerb vone = verb as DafnyVerifyOneVerb;
            if (vone != null)
            {
                int deepestParent = -1;
                foreach (SourcePath sourcePath in vone.getDirectIncludes())
                {
                    IVerb parent = new DafnyVerifyOneVerb(sourcePath);
                    int parentDepth = this.GetDepth(parent);
                    deepestParent = Math.Max(deepestParent, parentDepth);
                }

                depth = deepestParent + 1;
            }
            else
            {
                // Right now we only care about ordering the DafnyVerifyOneVerbs
                // wrt one another. Other verbs will be constrained by build
                // dependency anyway.
                depth = 0;
            }

            this.verbDepth[verb] = depth;
            return depth;
        }
    }
}
