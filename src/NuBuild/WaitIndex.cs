//--
// <copyright file="WaitIndex.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;

    /// <summary>
    /// Used by the Scheduler to track waiting verbs and their dependencies.
    /// </summary>
    internal class WaitIndex
    {
        private Dictionary<IVerb, WaitRecord> waitingVerbs;
        private Dictionary<BuildObject, HashSet<WaitRecord>> fwdDeps;

        public WaitIndex()
        {
            this.waitingVerbs = new Dictionary<IVerb, WaitRecord>();
            this.fwdDeps = new Dictionary<BuildObject, HashSet<WaitRecord>>();
        }

        public int Count()
        {
            return this.waitingVerbs.Count;
        }

        public void dbgDisplayIndex(Scheduler dbgScheduler)
        {
            List<WaitRecord> waitRecords = new List<WaitRecord>(this.waitingVerbs.Values);
            for (int i = 0; i < waitRecords.Count(); i++)
            {
                WaitRecord wr = waitRecords[i];
                List<int> depNums = new List<int>();
                List<BuildObject> unknownDeps = new List<BuildObject>();
                List<string> unscheduledDeps = new List<string>();
                foreach (BuildObject dep in wr.knownDeps)
                {
                    IVerb depOnVerb = dbgScheduler.getParent(dep);
                    if (depOnVerb == null)
                    {
                        unknownDeps.Add(dep);
                    }
                    else if (!this.waitingVerbs.ContainsKey(depOnVerb))
                    {
                        unscheduledDeps.Add(
                            string.Format(
                                "{0} waiting on {1} {2}",
                                dep,
                                depOnVerb,
                                dbgScheduler.dbgGetVerbStatus(depOnVerb)));
                    }
                    else
                    {
                        WaitRecord depWr = this.waitingVerbs[depOnVerb];
                        depNums.Add(waitRecords.IndexOf(depWr));
                    }
                }

                Logger.WriteLine(
                    string.Format(
                        "{0}. {1} waits on ({2}), {3} unknown, {4} unscheduled",
                        i,
                        wr.verb,
                        string.Join(",", depNums),
                        unknownDeps.Count(),
                        unscheduledDeps.Count()));

                this.dbgPreview("Unknown", unknownDeps.Select(it => it.ToString()), 3);
                this.dbgPreview("Unscheduled", unscheduledDeps, 20);
            }
        }

        internal void insert(IVerb verb, IEnumerable<BuildObject> knownDeps)
        {
            // Insert one fwd pointer for each obj verb is already known to
            // depend upon. The fact that this verb is waiting implies that
            // one of these deps is stale here and needs built/fetched.
            WaitRecord waitRecord = new WaitRecord(verb, knownDeps);
            foreach (BuildObject dep in knownDeps)
            {
                if (!this.fwdDeps.ContainsKey(dep))
                {
                    this.fwdDeps.Add(dep, new HashSet<WaitRecord>());
                }

                this.fwdDeps[dep].Add(waitRecord);
            }

            this.waitingVerbs.Add(verb, waitRecord);
            this.Say("sleeps " + verb);
        }

        // Remove any verb with obj in its dependency set.
        internal IEnumerable<IVerb> awaken(BuildObject obj)
        {
            this.Say("awaken " + obj);
            HashSet<WaitRecord> wokenRecords;
            HashSet<IVerb> result = new HashSet<IVerb>();
            if (this.fwdDeps.ContainsKey(obj))
            {
                wokenRecords = this.fwdDeps[obj];
                this.fwdDeps.Remove(obj);

                // Remove all the other index pointers for each removed verb.
                foreach (WaitRecord waitRecord in wokenRecords)
                {
                    foreach (BuildObject dep in waitRecord.knownDeps)
                    {
                        if (this.fwdDeps.ContainsKey(dep))
                        {
                            this.fwdDeps[dep].Remove(waitRecord);
                        }
                    }

                    result.Add(waitRecord.verb);
                    this.waitingVerbs.Remove(waitRecord.verb);
                    this.Say("  wakes " + waitRecord.verb);
                }
            }
            else
            {
                result = new HashSet<IVerb>();
            }

            return result;
        }

        internal bool isWaiting(IVerb verb)
        {
            return this.waitingVerbs.ContainsKey(verb);
        }

        private void dbgPreview(string s, IEnumerable<string> items, int max)
        {
            int i = 0;
            foreach (string o in items)
            {
                Logger.WriteLine(
                    string.Format(
                        "  {0} {1}/{2} {3}",
                        s,
                        i,
                        items.Count(),
                        o));
                i += 1;
                if (i == max)
                {
                    break;
                }
            }
        }
 
        private void Say(string msg)
        {
            ////Logger.WriteLine("[wtidx] " + msg);
        }

        private class WaitRecord
        {
            public IVerb verb;
            public IEnumerable<BuildObject> knownDeps;

            public WaitRecord(IVerb verb, IEnumerable<BuildObject> knownDeps)
            {
                this.verb = verb;
                this.knownDeps = knownDeps;
            }
        }
    }
}
