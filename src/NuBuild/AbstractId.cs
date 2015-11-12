//--
// <copyright file="AbstractId.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;

    internal class AbstractId
    {
        private const int MASTER_VERSION = 3;   // Bump this to invalidate every verb in all caches.

        private string verbName;
        private int version;
        private string abstractOnly;

        // PoundDefines should appear in both abstract and concrete descriptions:
        // abstract because we run one verb with multiple poundDefine configurations,
        // and concrete because the variation appears only in this parameter to the
        // verb, not in any input file contents.
        private PoundDefines poundDefines;
        private string concrete;

        public AbstractId(string verbName, int version, string abstractOnly, PoundDefines poundDefines = null, string concrete = null)
        {
            this.verbName = verbName;
            this.version = version + MASTER_VERSION;
            this.abstractOnly = abstractOnly;
            this.poundDefines = poundDefines == null ? PoundDefines.empty() : poundDefines;
            this.concrete = concrete;
        }

        public override bool Equals(object obj)
        {
            AbstractId other = obj as AbstractId;
            if (other != null)
            {
                return this.verbName == other.verbName
                    && this.version == other.version
                    && this.abstractOnly == other.abstractOnly
                    && this.poundDefines.Equals(other.poundDefines)
                    && this.concrete == other.concrete;
            }
            else
            {
                return false;
            }
        }

        public override int GetHashCode()
        {
            return this.ToString().GetHashCode();
        }

        public override string ToString()
        {
            if (this.concrete == null)
            {
                return string.Format("{0}(#{1},{2},{3})", this.verbName, this.version, this.abstractOnly, this.poundDefines.getAbstractIdString());
            }
            else
            {
                return string.Format("{0}(#{1},{2},{3},{4})", this.verbName, this.version, this.abstractOnly, this.poundDefines.getAbstractIdString(), this.concrete);
            }
        }

        public int CompareTo(object other)
        {
            return this.ToString().CompareTo(((AbstractId)other).ToString());
        }

        public string getConcreteId()
        {
            // The entire purpose of this class is to avoid encoding the input filename in a verb's concrete identity,
            // instead encoding it via the input's hash. That enables two verbs to have the same hash when they have
            // the same configuration, and hence converge -- we can reuse the outputs.
            // Except that the design is presently flawed: they'd have the same output contents, but not the same
            // output locations. Until we work that out, I'm neutering this convergence opportunity to preserve
            // soundness. (--jonh)
            return this.ToString();

            ////if (this.concrete == null) {
            ////    return string.Format("{0}(#{1},{2})", this.verbName, this.version, this.poundDefines);
            ////} else {
            ////    return string.Format("{0}(#{1},{2},{3})", this.verbName, this.version, this.poundDefines, this.concrete);
            ////}
        }
    }
}
