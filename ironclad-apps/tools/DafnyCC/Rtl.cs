using System;
using System.Linq;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using System.Numerics;

public class RtlMem: RtlExp
{
    public readonly RtlExp ptr;
    public readonly RtlExp scale; 
    public readonly RtlExp index; 
    public readonly RtlExp offset; 

    public RtlMem(RtlExp ptr, string offset):this(ptr, new RtlLiteral(offset)) { }
    public RtlMem(RtlExp ptr, RtlExp offset):this(ptr, null, null, offset) { }

    public RtlMem(RtlExp ptr, RtlExp scale, RtlExp index, RtlExp offset)
    {
        if (index is RtlInt)
        {
            Util.Assert(scale is RtlInt && offset is RtlInt);
            offset = new RtlInt(((RtlInt)offset).i + ((RtlInt)scale).i * ((RtlInt)index).i);
            scale = null;
            index = null;
        }
        this.ptr = ptr;
        this.scale = scale;
        this.index = index;
        this.offset = offset;
    }

    public override void AddVars(List<string> vars)
    {
        ptr.AddVars(vars);
        if (index != null)
        {
            index.AddVars(vars);
        }
    }

    public override RtlExp Subst(Dictionary<string,string> map)
    {
        return new RtlMem(ptr.Subst(map), scale, (index == null) ? null : index.Subst(map), offset);
    }

    public override string ToString() { return "INVALID_BOOGIE_CODE+RtlMem"; }

    public override string AsOperand()
    {
        return (index == null)
            ? "OMem(MReg(" + ptr + ", " + offset + "))"
            : (index is RtlInt)
            ? "OMem(MReg(" + ptr + ", " + scale + " * " + index + " + " + offset + "))"
            : "OMem(MIndex(" + ptr + ", " + scale + ", " + index + ", " + offset + "))";
    }
}

public class RtlLoopStart: RtlStmt
{
    public RtlLoopStart() {}
    public override string ToString() { return ""; }
}


public class RtlStmtGroup: RtlStmt
{
    public readonly ReadOnlyCollection<RtlStmt> stmts;

    public RtlStmtGroup(IEnumerable<RtlStmt> stmts)
    {
        this.stmts = stmts.ToList().AsReadOnly();
        comment = () => String.Join(Environment.NewLine + "// ", stmts.Select(s => s.comment == null ? "" : s.comment()));
    }

    public override RtlStmt Subst(Dictionary<string,string> map)
    {
        return new RtlStmtGroup(stmts.Select(s => s.Subst(map)));
    }
    public override void AddDefs(List<string> vars)
    {
        stmts.ToList().ForEach(s => s.AddDefs(vars));
    }
    public override void AddUses(List<string> vars)
    {
        stmts.ToList().ForEach(s => s.AddUses(vars));
    }
    public override string ToString()
    {
        return String.Join(Environment.NewLine, stmts.Select(s => s.ToString()));;
    }
}

public class RtlArg
{
    public readonly bool isIn;
    public readonly bool isOut;
    public readonly RtlExp e;
    public string pinReg; 

    public RtlArg(bool isIn, bool isOut, RtlExp e, string pinReg = null)
    {
        this.isIn = isIn;
        this.isOut = isOut;
        this.e = e;
        this.pinReg = pinReg;
    }

    public virtual RtlArg Subst(Dictionary<string,string> map)
    {
        return new RtlArg(isIn, isOut, e.Subst(map), pinReg);
    }

    public override string ToString() { return e.ToString(); }
    public virtual string AsOperand() { return isOut ? e.ToString() : e.AsOperand(); }
}

public class RtlInst: RtlStmt
{
    public readonly string op; 
    public readonly ReadOnlyCollection<RtlArg> args;
    public readonly bool ghost;
    public readonly string envIns;
    public readonly string envOuts;

    public RtlInst(string op, IEnumerable<RtlArg> args, bool ghost, string envIns = null, string envOuts = null)
    {
        this.op = op;
        this.args = args.ToList().AsReadOnly();
        this.ghost = ghost;
        this.envIns = envIns;
        this.envOuts = envOuts;
    }

    public RtlInst(string op, IEnumerable<RtlVar> outs, IEnumerable<RtlVar> insOuts, IEnumerable<RtlExp> ins, bool ghost,
        string envIns = null, string envOuts = null):
        this(op, outs.Select(x => new RtlArg(false, true, x)).Concat(
            insOuts.Select(x => new RtlArg(true, true, x)).Concat(
                ins.Select(x => new RtlArg(true, false, x)))),
            ghost, envIns, envOuts)
    {
    }

    public override void AddDefs(List<string> vars)
    {
        if (!ghost)
        {
            args.ToList().ForEach(x => {if (x.isOut) x.e.AddVars(vars);});
        }
    }

    public override void AddUses(List<string> vars)
    {
        if (!ghost)
        {
            args.ToList().ForEach(x => {if (x.isIn) x.e.AddVars(vars);});
        }
    }

    public override RtlStmt Subst(Dictionary<string,string> map)
    {
        return ghost ? this : new RtlInst(op, args.Select(e => e.Subst(map)), ghost, envIns, envOuts).WithComment(comment);
    }

    public override string ToString()
    {
        if (op == null)
        {
            var ins = args.Where(x => x.isIn);
            var outs = args.Where(x => x.isOut).ToList();
            return String.Join(", ", outs) + (outs.Count == 0 ? "" : " := ") + String.Join(", ", ins) + ";";
        }
        else
        {
            return "call r" + envOuts + " := " + op + "(r" + envIns + ", " + String.Join(", ", args.Select(e => e.AsOperand())) + ");";
        }
    }
}

public class RtlCallInOut: RtlInst
{
    public int index;
    public readonly bool isRet; 

    public RtlCallInOut(int index, bool isRet, RtlExp e):
        base(null, new RtlArg[] { new RtlArg(!isRet, isRet, e) }, false)
    {
        this.index = index;
        this.isRet = isRet;
    }

    public override RtlStmt Subst(Dictionary<string,string> map)
    {
        return new RtlCallInOut(index, isRet, args[0].e.Subst(map)).WithComment(comment);
    }

    public override string ToString()
    {
        return "INVALID_BOOGIE_CODE_RtlAssignStack;";
    }
}

public class RtlCall: RtlInst
{
    public RtlCall(string op, IEnumerable<RtlVar> outs, IEnumerable<RtlExp> args, bool ghost):
        base(op, outs, new RtlVar[0], args, ghost)
    {
    }

    public override void AddDefs(List<string> vars)
    {
        
    }

    public override void AddUses(List<string> vars)
    {
        
    }

    public override RtlStmt Subst(Dictionary<string, string> map)
    {
        
        return this;
    }

    public override string ToString()
    {
        Func<ReadOnlyCollection<object>,string> commaList = ss => String.Concat(ss.Select(s => ", " + s));
        var ins = args.Where(x => x.isIn);
        var outs = args.Where(x => x.isOut).ToList();
        if (ghost)
        {
            return "call " + String.Join(", ", outs) + (outs.Count == 0 ? "" : " := ") + op + "(" + String.Join(", ", ins) + ");";
        }
        else
        {
            string inouts = "stk, statics, io, mems, $commonVars, $gcVars, $toAbs, $absMem, $stacksFrames, objLayouts, heap";
            string call_string = "call alignCall(r.regs[ESP]);" + System.Environment.NewLine;
            call_string += "{: call r, stk := logical_Call(r, core_state, stk);" + System.Environment.NewLine;
            call_string += "call r, " + inouts + String.Concat(outs.Select(s => ", " + s))
                + " := " + op + "(r, core_state, " + inouts + String.Concat(ins.Select(s => ", " + s)) + "); :}";
            return call_string;
        }
    }
}

public class RtlStmtComputed: RtlInst
{
    public readonly Func<RtlStmtComputed,string> toString;
    
    public RtlStmtComputed(Func<RtlStmtComputed,string> toString, IEnumerable<RtlArg> args, bool ghost):
        base(null, args, ghost)
    {
        this.toString = toString;
    }

    public override RtlStmt Subst(Dictionary<string, string> map)
    {
        
        return ghost ? this :
            new RtlStmtComputed(toString, args.Select(e => e.Subst(map)), ghost).WithComment(comment);
    }

    public override string ToString()
    {
        return toString(this);
    }
}

public class RtlLabel: RtlStmt
{
    public readonly string label;
    public readonly bool loop; 
    public RtlLabel(string label, bool loop = false) { this.label = label; this.loop = loop; }

    public override string ToString()
    {
        return label + ":";
    }
}

public class RtlJump: RtlStmt
{
    public readonly string label;
    public readonly RtlBinary cond; 
    public RtlJump(string label, RtlBinary cond)
    {
        this.label = label;
        this.cond = cond;
        Util.Assert(cond == null || !(cond.e0 is RtlInt && cond.e1 is RtlInt)); 
    }

    public override void AddUses(List<string> vars)
    {
        if (cond != null)
        {
            cond.AddVars(vars);
        }
    }

    public override RtlStmt Subst(Dictionary<string,string> map)
    {
        return new RtlJump(label, (cond == null) ? null : (RtlBinary)cond.Subst(map)).WithComment(comment);
    }

    public override string ToString()
    {
        if (cond == null)
        {
            return "goto " + label + ";";
        }
        else
        {
            string jop;
            switch (cond.op)
            {
                case "==": jop = "Je"; break;
                case "!=": jop = "Jne"; break;
                case "<":  jop = "Jb"; break;
                case "<=": jop = "Jbe"; break;
                case ">":  jop = "Ja"; break;
                case ">=": jop = "Jae"; break;
                default: throw new Exception("not implemented: " + cond.op);
            }
            return "call r := instr_Cmp(r, " + cond.e0 + ", " + cond.e1.AsOperand() + "); if ("
                + jop + "(r.efl)) { goto " + label + "; }";
        }
    }
}

public class RtlReturn: RtlStmt
{
    public readonly ReadOnlyCollection<RtlVar> args;

    public RtlReturn(IEnumerable<RtlVar> args)
    {
        this.args = args.ToList().AsReadOnly();
    }

    public override void AddUses(List<string> vars)
    {
        args.ToList().ForEach(x => x.AddVars(vars));
    }

    public override RtlStmt Subst(Dictionary<string,string> map)
    {
        return new RtlReturn(args.Select(e => (RtlVar)(e.Subst(map)))).WithComment(comment);
    }

    public override string ToString()
    {
        string ret = "{: call r := logical_Ret(r, core_state, stk); return; :}";
        return ret;
    }
}

