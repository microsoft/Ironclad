using System;
using System.Linq;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using System.Numerics;

public abstract class RtlExp
{
    public List<string> Vars()
    {
        var vars = new List<string>();
        AddVars(vars);
        return vars;
    }

    public virtual RtlExp Subst(Dictionary<string,string> map)
    {
        Util.Assert(Vars().Count == 0);
        return this;
    }

    public virtual void AddVars(List<string> vars) {}
    public virtual string AsOperand() { return ToString(); }
}

public class RtlLiteral: RtlExp
{
    public readonly string str;
    public RtlLiteral(string s) { this.str = s; }

    public override void AddVars(List<string> vars) {}
    public override RtlExp Subst(Dictionary<string, string> map) { return this; }
    
    public override string ToString()
    {
        return str;
    }
}

public class RtlVar: RtlExp
{
    public readonly string x;
    public readonly bool isGhost;
    public readonly Microsoft.Dafny.Type type; //- used to declare local ghost variables; may be null if no declaration required
    public RtlVar(string x, bool isGhost, Microsoft.Dafny.Type t = null) { this.x = x; this.isGhost = isGhost; this.type = t; }
    public string getName() { return x; }
    //- no register allocation for ghost variables
    public override void AddVars(List<string> vars)
    {
        if (!isGhost)
        {
            vars.Add(x);
        }
    }
    public override string ToString()
    {
        return x;
    }
    public override string AsOperand()
    {
        return isGhost ? x.ToString() : ("OReg(" + x + ")");
    }

    public override RtlExp Subst(Dictionary<string, string> map)
    {
        return map.ContainsKey(x) ? new RtlVar(map[x], this.isGhost, this.type) : this;
    }
}

public class RtlInt: RtlExp
{
    public readonly BigInteger i;
    public RtlInt(int i) { this.i = new BigInteger(i); }
    public RtlInt(BigInteger i) { this.i = i; }
    public override string ToString() { return i.ToString(); }
    public override string AsOperand() { return "OConst(" + i + ")"; }
}

public class RtlBinary: RtlExp
{
    public readonly string op;
    public readonly RtlExp e0;
    public readonly RtlExp e1;
    public RtlBinary(string op, RtlExp e0, RtlExp e1)
    {
        this.op = op;
        this.e0 = e0;
        this.e1 = e1;
    }

    public override void AddVars(List<string> vars)
    {
        e0.AddVars(vars);
        e1.AddVars(vars);
    }

    public override RtlExp Subst(Dictionary<string,string> map)
    {
        return new RtlBinary(op, e0.Subst(map), e1.Subst(map));
    }

    public override string ToString()
    {
        Func<RtlExp,string> f = e => (e is RtlVar || e is RtlInt) ? e.ToString() : "(" + e + ")";
        return f(e0) + " " + op + " " + f(e1);
    }
}

public class RtlApply: RtlExp
{
    public readonly string op;
    public readonly ReadOnlyCollection<RtlExp> args;
    public RtlApply(string op, IEnumerable<RtlExp> args)
    {
        this.op = op;
        this.args = args.ToList().AsReadOnly();
    }

    public override void AddVars(List<string> vars)
    {
        args.ToList().ForEach(e => e.AddVars(vars));
    }

    public override RtlExp Subst(Dictionary<string,string> map)
    {
        return new RtlApply(op, args.Select(e => e.Subst(map)));
    }

    public override string ToString()
    {
        return op + "(" + String.Join(", ", args.Select(e => e.ToString())) + ")";
    }
}

public class RtlExpComputed: RtlExp
{
    public readonly ReadOnlyCollection<RtlExp> args;
    public readonly Func<RtlExpComputed,string> toString;
    
    public RtlExpComputed(Func<RtlExpComputed,string> toString, IEnumerable<RtlExp> args = null)
    {
        this.toString = toString;
        this.args = ((args == null) ? new List<RtlExp>() : args.ToList()).AsReadOnly();
    }

    public override void AddVars(List<string> vars)
    {
        args.ToList().ForEach(e => e.AddVars(vars));
    }

    public override RtlExp Subst(Dictionary<string,string> map)
    {
        return new RtlExpComputed(toString, args.Select(e => e.Subst(map)));
    }

    public override string ToString()
    {
        return toString(this);
    }
}

public abstract class RtlStmt
{
    public Func<string> comment;

    public RtlStmt WithComment(string comment) { this.comment = () => comment; return this; }
    public RtlStmt WithComment(Func<string> comment) { this.comment = comment; return this; }

    public List<string> Defs()
    {
        var vars = new List<string>();
        AddDefs(vars);
        return vars;
    }

    public List<string> Uses()
    {
        var vars = new List<string>();
        AddUses(vars);
        return vars;
    }

    public List<string> Vars()
    {
        var vars = new List<string>();
        AddDefs(vars);
        AddUses(vars);
        return vars;
    }

    public virtual RtlStmt Subst(Dictionary<string,string> map)
    {
        Util.Assert(Vars().Count == 0);
        return this;
    }
    public virtual void AddDefs(List<string> vars) {}
    public virtual void AddUses(List<string> vars) {}
}

public class RtlComment: RtlStmt
{
    public RtlComment(string comment)
    {
        this.comment = () => comment;
    }

    public RtlComment(Func<string> comment)
    {
        this.comment = comment;
    }

    public override string ToString()
    {
        return "";
    }
}

public class RtlIndent: RtlStmt
{
    public bool Positive;

    public RtlIndent(bool Positive)
    {
        this.Positive = Positive;
    }

    public override string ToString()
    {
        return "";
    }
}

public class RtlGhostMove: RtlStmt
{
    public readonly ReadOnlyCollection<RtlVar> outs;
    public readonly ReadOnlyCollection<RtlExp> ins;

    public RtlGhostMove(IEnumerable<RtlVar> outs, IEnumerable<RtlExp> ins)
    {
        this.outs = outs.ToList().AsReadOnly();
        this.ins = ins.ToList().AsReadOnly();
    }

    public override string ToString()
    {
        return String.Join(", ", outs) + (outs.Count == 0 ? "" : " := ") + String.Join(", ", ins) + ";";
    }
}

public class RtlGhostCall: RtlGhostMove
{
    public readonly string op;

    public RtlGhostCall(string op, IEnumerable<RtlVar> outs, IEnumerable<RtlExp> args):
        base(outs, args)
    {
        this.op = op;
    }

    public override string ToString()
    {
        return "call " + String.Join(", ", outs) + (outs.Count == 0 ? "" : " := ") + op + "(" + String.Join(", ", ins) + ");";
    }
}

public class RtlGhostStmtComputed: RtlStmt
{
    public readonly Func<RtlGhostStmtComputed,string> toString;
    public readonly ReadOnlyCollection<RtlExp> args;

    public RtlGhostStmtComputed(Func<RtlGhostStmtComputed,string> toString, IEnumerable<RtlExp> args)
    {
        this.toString = toString;
        this.args = args.ToList().AsReadOnly();
    }

    public override string ToString()
    {
        return toString(this);
    }
}

public class RtlAssert: RtlStmt
{
    public readonly bool isLoop;
    public readonly RtlExp e; //- ghost expression, does not count as a use
    public RtlAssert(RtlExp e, bool isLoop = false) { this.e = e; this.isLoop = isLoop; }

    public override RtlStmt Subst(Dictionary<string,string> map)
    {
        return this;
    }

    public override string ToString()
    {
        return (isLoop ? "invariant " : "assert ") + e + ";";
    }
}
