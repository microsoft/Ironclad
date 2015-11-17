using System;
using System.Linq;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using System.Numerics;

public class Set<A>
{
    private bool full; 
    private Dictionary<A,A> map = new Dictionary<A,A>(); 

    public Set(bool full = false)
    {
        this.full = full;
    }

    public Set(Set<A> s)
    {
        this.full = s.full;
        this.map = new Dictionary<A,A>(s.map);
    }

    public Set(IEnumerable<A> elems)
    {
        this.full = false;
        this.map = elems.ToDictionary(a => a);
    }

    public bool Contains(A a) { return full || map.ContainsKey(a); }

    public void Add(A a)
    {
        if (!full) map[a] = a;
    }

    public bool IntersectFrom(Set<A> s)
    {
        if (s.full)
        {
            return false;
        }
        else if (full)
        {
            full = false;
            map = new Dictionary<A,A>(s.map);
            return true;
        }
        else
        {
            List<A> toRemove = map.Keys.Where(a => !s.Contains(a)).ToList();
            toRemove.ForEach(a => map.Remove(a));
            return toRemove.Count > 0;
        }
    }

    public override bool Equals(object o)
    {
        Set<A> s = o as Set<A>;
        return s != null && full == s.full && map.Count == s.map.Count
            && map.Keys.ToList().TrueForAll(s.map.ContainsKey);
    }

    public override string ToString()
    {
        return full ? "*" : String.Join(" ", map.Keys);
    }

    public override int GetHashCode()
    {
        return map.GetHashCode();
    }
}

public abstract class Analyze
{
    protected List<string> inVars;
    protected List<string> outVars;
    protected List<RtlStmt> stmts;
    protected Dictionary<string,int> labels = new Dictionary<string,int>();
    protected List<List<int>> preds = new List<List<int>>();
    protected List<List<int>> succs = new List<List<int>>();
    protected List<Dictionary<string,int>> liveVars = new List<Dictionary<string,int>>(); //- set of live vars before each stmt; also record distance to next use
    protected List<Set<string>> defVars = new List<Set<string>>(); //- set of definitely-defined vars after each stmt

    public Analyze(List<string> inVars, List<string> outVars, List<RtlStmt> stmts)
    {
        this.inVars = inVars;
        this.outVars = outVars;
        this.stmts = stmts;
        ComputeControl();
        ComputeLiveVars();
        ComputeDefVars();
    }

    void ComputeControl()
    {
        for (int i = 0; i < stmts.Count; i++)
        {
            RtlLabel label = stmts[i] as RtlLabel;
            if (label != null)
            {
                labels.Add(label.label, i);
            }
        }
        stmts.ForEach(_ => preds.Add(new List<int>()));
        for (int i = 0; i < stmts.Count; i++)
        {
            RtlJump jump = stmts[i] as RtlJump;
            RtlReturn ret = stmts[i] as RtlReturn;
            List<int> succs_i = new List<int>();
            succs.Add(succs_i);
            if (jump != null)
            {
                int target = labels[jump.label];
                succs[i].Add(target);
                preds[target].Add(i);
            }
            if (ret == null && i + 1 < stmts.Count && (jump == null || jump.cond != null))
            {
                succs[i].Add(i + 1);
                preds[i + 1].Add(i);
            }
        }
    }

    void Dataflow(bool forward, bool addAll, Action<int> init, Func<int,RtlStmt,bool> work)
    {
        bool[] workSet = new bool[stmts.Count];
        Stack<int> workList = new Stack<int>();
        for (int i = 0; i < stmts.Count; i++)
        {
            if (i == 0 || addAll)
            {
                workSet[i] = true;
                workList.Push((forward && addAll) ? (stmts.Count - i - 1) : i);
            }
            init(i);
        }
        while (workList.Count != 0)
        {
            int i = workList.Pop();
            workSet[i] = false;
            bool changed = work(i, stmts[i]);
            if (changed)
            {
                foreach (int p in (forward ? succs : preds)[i])
                {
                    if (!workSet[p])
                    {
                        workSet[p] = true;
                        workList.Push(p);
                    }
                }
            }
        }
    }

    void ComputeLiveVars()
    {
        Func<int,RtlStmt,bool> work = (i, stmt) =>
        {
            bool changed = false;
            List<string> uses = stmt.Uses();
            List<string> defs = stmt.Defs();
            Dictionary<string,int> live = liveVars[i];
            Action<string,int> addLiveVar = (x, dist) =>
            {
                bool contains = live.ContainsKey(x);
                if (!contains || (contains && dist < live[x]))
                {
                    changed = true;
                    live[x] = dist;
                }
            };
            uses.ForEach(x => addLiveVar(x, 0));
            if (stmt is RtlReturn)
            {
                foreach (string x in outVars)
                {
                    if (!defs.Contains(x))
                    {
                        addLiveVar(x, 1);
                    }
                }
            }
            foreach (int s in succs[i])
            {
                foreach (var keyVal in liveVars[s])
                {
                    string x = keyVal.Key;
                    if (!defs.Contains(x))
                    {
                        addLiveVar(x, keyVal.Value + 1);
                    }
                }
            }
            return changed;
        };
        Dataflow(false, true, i => { liveVars.Add(new Dictionary<string,int>()); }, work);
    }

    void ComputeDefVars()
    {
        Func<int,RtlStmt,bool> work = (i, stmt) =>
        {
            List<string> defs = stmt.Defs();
            Set<string> def = new Set<string>(i == 0 ? new Set<string>(inVars) : defVars[i]);
            List<int> ps = preds[i];
            preds[i].ForEach(p => def.IntersectFrom(defVars[p]));
            defs.ForEach(x => def.Add(x));
            bool changed = !def.Equals(defVars[i]);
            defVars[i] = def;
            return changed;
        };
        //- null set represents all variables
        Dataflow(true, false, i => { defVars.Add(new Set<string>(true)); }, work);
    }
}

public class Optimize: Analyze
{
    bool[] liveStmts;

    public Optimize(List<string> inVars, List<string> outVars, List<RtlStmt> stmts):
        base(inVars, outVars, stmts)
    {
        ComputeLiveStmts();
    }

    void ComputeLiveStmts()
    {
        liveStmts = new bool[stmts.Count];
        Stack<int> workList = new Stack<int>();
        liveStmts[0] = true;
        workList.Push(0);
        while (workList.Count != 0)
        {
            int i = workList.Pop();
            foreach (int s in succs[i])
            {
                if (!liveStmts[s])
                {
                    liveStmts[s] = true;
                    workList.Push(s);
                }
            }
        }
    }

    public List<RtlStmt> Run()
    {
        //- eliminate dead code
        return stmts.Where((_, i) => liveStmts[i]).ToList();
    }
}
