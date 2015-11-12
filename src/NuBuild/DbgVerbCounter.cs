namespace NuBuild
{
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

    // I used this class to determine how much effort we were wasting
    // re-computing verb.getDependencies.
    internal class DbgVerbCounter
    {
        public enum DbgVerbCondition { DVWake, DVDepsIncomplete, DVDepsStale, DVDepsNonstale, DVTotal }
        private Dictionary<Tuple<IVerb, DbgVerbCondition>, int> dbgCounts = new Dictionary<Tuple<IVerb, DbgVerbCondition>, int>();

        public void dbgDisplayCounts()
        {
            List<Tuple<IVerb, DbgVerbCondition>> keys = new List<Tuple<IVerb, DbgVerbCondition>>(dbgCounts.Keys);
            keys.Sort();
            foreach (Tuple<IVerb, DbgVerbCondition> key in keys)
            {
                Logger.WriteLine(string.Format("{0:20}: {1}", key, dbgCounts[key]));
            }
        }

        public void consider(IVerb verb, DbgVerbCondition cond)
        {
            consider_inner(new Tuple<IVerb, DbgVerbCondition>(verb, cond));
            consider_inner(new Tuple<IVerb, DbgVerbCondition>(verb, DbgVerbCondition.DVTotal));
        }

        private void consider_inner(Tuple<IVerb, DbgVerbCondition> key)
        {
            if (!dbgCounts.ContainsKey(key))
            {
                dbgCounts[key] = 0;
            }

            dbgCounts[key] += 1;
        }
    }
}
