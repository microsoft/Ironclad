//--
// <copyright file="PoundDefines.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    internal class PoundDefines
    {
        private List<string> definedSymbols;
        private string descr;

        public PoundDefines(IEnumerable<string> definedSymbols)
        {
            this.definedSymbols = new List<string>(definedSymbols);
            this.definedSymbols.Sort();

            // NB the null list gets a *null* ToString, which is interpreted as no appLabel.
            this.descr = this.definedSymbols.Count == 0 ? null : "#" + string.Join(",", this.definedSymbols);
        }

        public override string ToString()
        {
            return this.descr;
        }

        public string getAbstractIdString()
        {
            return this.descr == null ? string.Empty : ", " + this.descr;
        }

        public override int GetHashCode()
        {
            return this.descr.GetHashCode();
        }

        public override bool Equals(object obj)
        {
            PoundDefines other = obj as PoundDefines;
            if (other != null)
            {
                return (this.descr == null && other.descr == null)
                    || (this.descr != null && this.descr.Equals(other.descr));
            }
            else
            {
                return false;
            }
        }

        internal static string toAppLabel(PoundDefines poundDefines)
        {
            return poundDefines == null ? null : poundDefines.ToString();
        }

        internal static PoundDefines empty()
        {
            return new PoundDefines(new string[] { });
        }

        internal IEnumerable<string> ToDefArgs()
        {
            List<string> args = new List<string>();
            foreach (string symbol in this.definedSymbols)
            {
                args.Add("-def");
                args.Add(symbol);
            }

            return args;
        }
    }
}
