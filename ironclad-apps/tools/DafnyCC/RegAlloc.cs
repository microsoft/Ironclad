using System;
using System.Linq;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using System.Numerics;
using Type = Microsoft.Dafny.Type;


public class RegAlloc : Analyze
{
    public const int stackGcOffset = 0x111000; 

    DafnySpec dafnySpec;
    internal CompileMethod compileMethod;
    public readonly List<string> regs;
    public readonly List<string> initAssign;
    public readonly List<string> retAssign;
    public readonly Dictionary<string, int> inInts = new Dictionary<string, int>();
    public readonly Dictionary<string, int> inPtrs = new Dictionary<string, int>();
    public readonly Dictionary<string, int> outInts = new Dictionary<string, int>();
    public readonly Dictionary<string, int> outPtrs = new Dictionary<string, int>();
    public readonly Dictionary<string, int> spillInts = new Dictionary<string, int>();
    public readonly Dictionary<string, int> spillPtrs = new Dictionary<string, int>();
    public readonly Dictionary<string, Type> varTypes = new Dictionary<string, Type>();
    public int callIntArgs = 0;
    public int callPtrArgs = 0;
    public int callIntRets = 0;
    public int callPtrRets = 0;
    
    List<List<string>> assigned; 

    public int IPSize;
    public int IPWords;

    
    public RegAlloc(
        DafnySpec dafnySpec,
        CompileMethod compileMethod,
        List<string> inVars,
        List<string> outVars,
        List<Formal> inIntList,
        List<Formal> outIntList,
        List<Formal> inPtrList,
        List<Formal> outPtrList,
        Dictionary<string,RtlVar> allVars,
        List<RtlStmt> stmts):
        base(inVars, outVars, stmts)
    {
        this.dafnySpec = dafnySpec;
        this.compileMethod = compileMethod;
        
        IPSize = ((DafnyCC)dafnySpec).IPSize; 
        IPWords = IPSize/4;

        if (compileMethod.dafnycc.useFramePointer)
        {
            regs = new List<string>(new string[] { "EAX", "ECX", "EDX", "EBX", "ESI", "EDI" });
        }
        else
        {
            regs = new List<string>(new string[] { "EAX", "ECX", "EDX", "EBX", "ESI", "EDI", "EBP" });
        }
        initAssign = new List<string>(new string[regs.Count]);
        retAssign = new List<string>(new string[regs.Count]);
        for (int i = 0; i < inIntList.Count; i++)
        {
            inInts.Add(compileMethod.GhostVar(inIntList[i].Name), 4 * i);
        }
        for (int i = 0; i < outIntList.Count; i++)
        {
            outInts.Add(compileMethod.GhostVar(outIntList[i].Name), 4 * i);
        }
        for (int i = 0; i < inPtrList.Count; i++)
        {
            string x = compileMethod.GhostVar(inPtrList[i].Name);
            inPtrs.Add(x, 4 * i);
        }
        for (int i = 0; i < outPtrList.Count; i++)
        {
            string x = compileMethod.GhostVar(outPtrList[i].Name);
            outPtrs.Add(x, 4 * i);
        }
        allVars.ToList().ForEach(p => varTypes.Add(p.Key, p.Value.type));
        /* for now, just use the stack for simplicity
        if (inVars.Count >= 1)
        {
            initAssign[regs.IndexOf("ECX")] = inVars[0];
        }
        if (inVars.Count >= 2)
        {
            initAssign[regs.IndexOf("EDX")] = inVars[1];
        }
        if (inVars.Count >= 3)
        {
            initAssign[regs.IndexOf("EBX")] = inVars[2];
        }
        if (inVars.Count >= 4)
        {
            throw new Exception("not implemented: more than two arguments");
        }
        if (outVars.Count >= 1)
        {
            retAssign[regs.IndexOf("EAX")] = outVars[0];
        }
        if (outVars.Count >= 2)
        {
            retAssign[regs.IndexOf("ESI")] = outVars[1];
        }
        if (outVars.Count >= 3)
        {
            throw new Exception("not implemented: more than two return values");
        }
        */
        
        
        
        
    }

    public static string Reg(string s)
    {
        return "r.regs[" + s + "]";
    }

    public string TypeString(Type t)
    {
        return dafnySpec.TypeString(t);
    }

    public bool IsPtr(string x)
    {
        return CompileMethod.IsPtrType(varTypes[x]);
    }

    public bool IsArray(string x)
    {
        return DafnySpec.IsArrayType(varTypes[x]);
    }

    public int ArgsRetsCount() { return Math.Max(callIntArgs + callIntRets, callPtrArgs + callPtrRets); }
    public int LocalsCount() { return Math.Max(spillInts.Count, spillPtrs.Count); }
    public int InsOutsCount() { return Math.Max(inInts.Count + outInts.Count, inPtrs.Count + outPtrs.Count); }

    
    public int FrameCount()
    {
        return ArgsRetsCount() + LocalsCount();
    }

    
    public int FrameVisibleCount()
    {
        return ArgsRetsCount() + LocalsCount() + IPWords + InsOutsCount() + compileMethod.dafnycc.framePointerCount;
    }

    public int LocalsOffset() { return ArgsRetsCount() * 4; }
    public int OutsOffset() { return LocalsOffset() + 4 * LocalsCount() + /*return address*/ IPSize + 4 * compileMethod.dafnycc.framePointerCount; }
    public int InIntsOffset() { return OutsOffset() + 4 * outInts.Count; }
    public int InPtrsOffset() { return OutsOffset() + 4 * outPtrs.Count; }

    private string StackOMem(int offset) { return "OMem(MReg(ESP, " + offset + "))"; }
    private string StackOMemPtr(int offset) { return StackOMem(offset + stackGcOffset); }

    private RtlExp Spill(string x)
    {
        Func<int> offset;
        var isPtr = IsPtr(x);
        if (inInts.ContainsKey(x)) { offset = () => InIntsOffset() + inInts[x]; }
        else if (outInts.ContainsKey(x)) { offset = () => OutsOffset() + outInts[x]; }
        else if (inPtrs.ContainsKey(x)) { offset = () => InPtrsOffset() + inPtrs[x]; }
        else if (outPtrs.ContainsKey(x)) { offset = () => OutsOffset() + outPtrs[x]; }
        else
        {
            Util.DebugWriteLine(" *** SPILL: " + x);
            var spilled = isPtr ? spillPtrs : spillInts;
            if (!spilled.ContainsKey(x))
            {
                spilled.Add(x, spilled.Count * 4);
            }
            offset = () => LocalsOffset() + spilled[x];
        }
        return new RtlExpComputed(e => isPtr ? StackOMemPtr(offset()) : StackOMem(offset()));
    }

    static int debugTag = 0;
    public List<RtlStmt> Alloc()
    {
        assigned = new List<List<string>>(new List<string>[stmts.Count]);
        Func<int, string> slotMem = offset => "stk.map[r.regs[ESP] + " + offset + "]";
        Func<RtlExp, string> spillLoc = e => "EvalPtr(r, " + e.AsOperand() + ")";
        Func<RtlExp, string> spillMem = e => "stk.map[" + spillLoc(e) + "]";
        Stack<int> workList = new Stack<int>();

        List<RtlStmt> newStmts = new List<RtlStmt>();
        Action<string, string> move = (string dest, string src) =>
        {
            if (dest != src)
            {
                newStmts.Add(new RtlInst("instr_Mov", new RtlVar[] { new RtlVar(dest, false) },
                    new RtlVar[0], new RtlExp[] { new RtlVar(src, false) }, false)
                    .WithComment("regalloc_move:: " + dest + " := " + src));
            }
        };
        Action<string, RtlExp, string> sLoad = (string dest, RtlExp src, string var) =>
        {
            int dbgTag = debugTag++;
            Util.DebugWriteLine("sLoad: dest = " + dest + " " + dbgTag);
            newStmts.Add(new RtlStmtComputed((inst =>
                {
                    var eDst = inst.args[0].e;
                    string opPtr = inst.args[1].e.AsOperand();
                    string ptr = "EvalPtr(r, " + opPtr + ")";
                    return IsPtr(var)
                        ? "call r, mems := heapLoadStack(r, core_state, stk, statics, io, mems, "
                            + "$commonVars, $gcVars, $absMem, $toAbs, $stacksFrames, objLayouts, "
                            + eDst + ", " + opPtr + ", " + ptr + ");"
                            + Environment.NewLine
                            + "    " + var + "__abs := frameGet($stacksFrames, " + ptr + ");"
                        : "call r := logical_Load(r, core_state, stk, " + eDst + ", " + opPtr + ");";
                }),
                new RtlArg[] { new RtlArg(true, false, new RtlVar(dest, false)),
                    new RtlArg(true, false, src) }, false)
                .WithComment(() => "regalloc_stack_load:: " + dest + " := " + src + "  // var = " + var + " " + dbgTag));
        };
        Action<RtlExp, string, string> sStore = (RtlExp dest, string src, string var) =>
        {
            newStmts.Add(new RtlStmtComputed((inst =>
                {
                    string opPtr = inst.args[0].e.AsOperand();
                    string opVal = inst.args[1].e.AsOperand();
                    string ptr = "EvalPtr(r, " + opPtr + ")";
                    string val = "Eval(r, " + opVal + ")";
                    return IsPtr(var)
                        ? "call mems, $stacksFrames := "
                            + "heapStoreStack(r, core_state, stk, statics, io, mems, "
                            + "$commonVars, $gcVars, $absMem, $toAbs, $stacksFrames, objLayouts, "
                            + opPtr + ", " + opVal + ", " + ptr + ", " + var + "__abs);"
                        : "call stk := logical_Store(r, core_state, stk, " + opPtr + ", " + opVal + ");";
                }),
                new RtlArg[] { new RtlArg(true, false, dest),
                    new RtlArg(true, false, new RtlVar(src, false)) }, false)
                .WithComment(() => "regalloc_stack_store:: " + dest + " := " + src + "  // var = " + var));
        };

        workList.Push(0);
        while (workList.Count > 0)
        {
            int i = workList.Pop();
            RtlStmt stmt = stmts[i];
            stmt.Uses().ForEach(x =>
                preds[i].ForEach(p =>
                     { if (!defVars[p].Contains(x)) throw new Exception(
                        "variable " + x + " is used before it is assigned"); }));
            Util.DebugWriteLine(i + ": " + stmt);
            List<string> vars = stmt.Vars();
            List<string> assignment = new List<string>((i == 0) ? initAssign :
                preds[i].ConvertAll(p => assigned[p]).Find(a => a != null));
            Util.DebugWriteLine("  " + String.Join(", ", assignment));
            RtlInst inst = stmt as RtlInst;
            List<Tuple<string,string>> pinVars = (inst == null) ? new List<Tuple<string,string>>() :
                inst.args.Where(arg => arg.pinReg != null && arg.e is RtlVar)
                    .Select(arg => Tuple.Create(((RtlVar)arg.e).x, arg.pinReg)).ToList();
            for (int r = 0; r < regs.Count; r++)
            {
                
                string rx = assignment[r];
                if (rx != null && !liveVars[i].ContainsKey(rx))
                {
                    assignment[r] = null;
                }
                
                if (pinVars.Exists(p => p.Item1 == rx))
                {
                    assignment[r] = null;
                }
                
                foreach (var p in pinVars)
                {
                    if (p.Item2 == regs[r])
                    {
                        assignment[r] = p.Item1;
                    }
                }
            }
            if (stmt is RtlCall)
            {
                RtlCall call = (RtlCall)stmt;
                if (!call.ghost)
                {
                    for (int r = 0; r < regs.Count; r++)
                    {
                        
                        assignment[r] = null;
                    }
                    /*
                    Func<RtlExp, bool> shouldSkip = (RtlExp e) => ((e is RtlVar) && ((RtlVar)e).isGhost);
                    int[] outsToReg = new int[2] { regs.IndexOf("EAX"), regs.IndexOf("ESI") };
                    int[] argsToReg = new int[3] { regs.IndexOf("ECX"), regs.IndexOf("EDX"), regs.IndexOf("EBX") };
                    
                    for (int r = 0; r < regs.Count; r++)
                    {
                        string rx = assignment[r];
                        if (rx != null && (call.outs.Where(v => v.ToString() == rx).Count() != 0 || call.args.Where(v => v.ToString() == rx).Count() != 0))
                        {
                            assignment[r] = null;
                        }
                    }
                    for (int idx = 0; idx < 2; idx++)
                    {
                        if (call.outs.Count >= idx + 1 && !shouldSkip(call.outs[idx]))
                        {
                            int r = outsToReg[idx];
                            string rx = assignment[r];
                            if (rx != null)
                            {
                                sStore(Spill(rx), regs[r]);
                            }
                            assignment[r] = call.outs[idx].ToString();
                        }
                    }
                    for (int idx = 0; idx < 3; idx++)
                    {
                        if (call.args.Count >= idx + 1 && !shouldSkip(call.args[idx]))
                        {
                            int r = argsToReg[idx];
                            string rx = assignment[r];
                            if (rx != null)
                            {
                                sStore(Spill(rx), regs[r]);
                            }
                            assignment[r] = call.args[idx].ToString();
                        }
                    }
                    */
                }
            }
            else if (stmt is RtlReturn)
            {
                for (int r = 0; r < regs.Count; r++)
                {
                    
                    assignment[r] = null;
                }
            }
            else if (inst == null || !inst.ghost)
            {
                foreach (string x in vars)
                {
                    Tuple<int, int> bestEvict = null; 
                    for (int r = 0; r < regs.Count; r++)
                    {
                        var rx = assignment[r];
                        if (rx == x)
                        {
                            goto done;
                        }
                        if (!vars.Contains(rx))
                        {
                            int thisEvict = (rx == null) ? Int32.MaxValue : liveVars[i][rx];
                            if (bestEvict == null || thisEvict > bestEvict.Item2)
                            {
                                
                                bestEvict = Tuple.Create(r, thisEvict);
                            }
                        }
                    }
                    string ex = assignment[bestEvict.Item1];
                    if (ex != null)
                    {
                        Spill(ex);
                    }
                    assignment[bestEvict.Item1] = x;
                    done: {}
                }
            }
            Util.DebugWriteLine("  vars =  " + String.Join(", ", vars));
            Util.DebugWriteLine("  preds = " + String.Join(", ", preds[i]));
            Util.DebugWriteLine("  succs = " + String.Join(", ", succs[i]));
            Util.DebugWriteLine("  live =  " + String.Join(", ", liveVars[i].Keys.Select(x => Tuple.Create(x, liveVars[i][x]))));
            Util.DebugWriteLine("  assign: " + String.Join(", ", assignment));
            assigned[i] = assignment;
            succs[i].Where(s => assigned[s] == null).ToList().ForEach(workList.Push);
        }
        for (int i = 0; i < stmts.Count; i++)
        {
            
            RtlJump jump = stmts[i] as RtlJump;
            if (jump != null && jump.cond != null)
            {
                List<string> assignment1 = assigned[i];
                List<string> assignment2 = assigned[labels[jump.label]];
                List<string> condVars = jump.cond.Vars();
                for (int r = 0; r < regs.Count; r++)
                {
                    string x1 = assignment1[r];
                    string x2 = assignment2[r];
                    if (x1 != null && x2 != null && condVars.Contains(x1) && x1 != x2)
                    {
                        assignment2[r] = null; 
                        Spill(x2);
                    }
                }
            }
        }

        Action<List<string>, Dictionary<string, int>, Dictionary<string, int>, Dictionary<string, string>> transition =
            (List<string> assignment2, Dictionary<string, int> live, Dictionary<string, int> liveAlt, Dictionary<string, string> varToReg) =>
            {
                
                
                
                Util.DebugWriteLine("start transition");
                
                
                varToReg.Keys.Where(x => x != null && !live.ContainsKey(x) && !liveAlt.ContainsKey(x)).ToList()
                    .ForEach(x => varToReg.Remove(x));
                
                bool done;
                do
                {
                    done = true;
                    for (int rx = 0; rx < regs.Count; rx++)
                    {
                        string x = assignment2[rx];
                        string reg = regs[rx];
                        if (x != null && varToReg.ContainsKey(x) && varToReg[x] != reg
                            && !varToReg.ContainsValue(reg))
                        {
                            Util.DebugWriteLine("move " + x + ": " + regs[rx] + " <- " + varToReg[x]);
                            move(regs[rx], varToReg[x]);
                            varToReg[x] = reg;
                            done = false;
                        }
                    }
                } while (!done);
                
                List<string> toSpill = new List<string>();
                foreach (var current in varToReg)
                {
                    string x = current.Key;
                    int rx = regs.IndexOf(current.Value);
                    Util.DebugWriteLine("current = " + x + " -> " + regs[rx]);
                    Util.DebugWriteLine("assign  = " + assignment2[rx] + " -> " + regs[rx]);
                    if (assignment2[rx] != x && (live.ContainsKey(x) || liveAlt.ContainsKey(x)))
                    {
                        Util.DebugWriteLine("spilling " + x + " from " + regs[rx]);
                        toSpill.Add(x);
                        sStore(Spill(x), regs[rx], x);
                    }
                }
                toSpill.ForEach(x => varToReg.Remove(x));
                Util.DebugWriteLine("live   = " + String.Join(", ", live));
                
                for (int rx = 0; rx < regs.Count; rx++)
                {
                    string x = assignment2[rx];
                    if (x != null && live.ContainsKey(x))
                    {
                        Util.DebugWriteLine("assign  = " + x + " -> " + regs[rx]);
                        if (varToReg.ContainsKey(x))
                        {
                            Util.Assert(varToReg[x] == regs[rx]);
                        }
                        else
                        {
                            Util.DebugWriteLine("loading  " + x + " to   " + regs[rx]);
                            sLoad(regs[rx], Spill(x), x);
                            Util.DebugWriteLine("loaded   " + x + " to   " + regs[rx]);
                            varToReg.Add(x, regs[rx]);
                        }
                    }
                }
            };

        Util.DebugWriteLine("spilled: " + String.Join(", ", spillInts.Keys));

        Action<string> DebugWriteLine = s =>
        {
            
        };

        if (stmts.Count > 0)
        {
            transition(assigned[0], liveVars[0], liveVars[0], new Dictionary<string,string>());
        }
        for (int i = 0; i < stmts.Count; i++)
        {
            
            
            
            List<string> assignment = assigned[i];
            RtlStmt stmt = stmts[i];
            List<string> vars = stmt.Vars();
            List<string> uses = stmt.Uses();
            Dictionary<string, string> varToReg = new Dictionary<string, string>();
            Util.DebugWriteLine(i + ":  " + stmt);
            Util.DebugWriteLine("  assignment: " + String.Join(", ", assignment));
            Util.DebugWriteLine("  vars:" + String.Join(", ", vars));
            Util.DebugWriteLine("  uses:" + String.Join(", ", uses));
            DebugWriteLine(i + ":  " + stmt.GetType() + ": " + stmt);
            DebugWriteLine("  vars =  " + String.Join(", ", vars));
            DebugWriteLine("  uses =  " + String.Join(", ", uses));
            DebugWriteLine("  preds = " + String.Join(", ", preds[i]));
            DebugWriteLine("  succs = " + String.Join(", ", succs[i]));
            DebugWriteLine("  live =  " + String.Join(", ", liveVars[i].Keys.Select(x => Tuple.Create(x, liveVars[i][x]))));
            DebugWriteLine("  defs =  " + String.Join(", ",  defVars[i]));
            DebugWriteLine("  assign: " + String.Join(", ", assignment));
            Action<int,int> transitionTarget = (int target, int altTarget) =>
            {
                Util.DebugWriteLine("transition from " + i + " to " + target);
                transition(assigned[target], liveVars[target], liveVars[altTarget], varToReg);
            };
            
            
            int r;
            for (r = 0; r < regs.Count; r++)
            {
                string x = assignment[r];
                if (x != null)
                {
                    varToReg.Add(x, regs[r]);
                }
            }
            r = 0;
            foreach (string x in vars)
            {
                if (varToReg.ContainsKey(x) || stmt is RtlReturn)
                {
                    continue;
                }
                int rx = assignment.IndexOf(x);
                if (rx < 0)
                {
                    rx = assignment.IndexOf(null, r);
                    Util.Assert(rx >= 0);
                    Util.DebugWriteLine(i + ": MOVE(1): " + x);
                    sLoad(regs[rx], Spill(x), x);
                    r = rx + 1;
                }
                varToReg.Add(x, regs[rx]);
            }
            
            Util.DebugWriteLine("vars = " + String.Join(", ", vars));
            List<string> defs = stmt.Defs();
            stmt = stmt.Subst(varToReg);
            Dictionary<string, string> regToVar = new Dictionary<string, string>();
            varToReg.ToList().ForEach(p => regToVar.Add(p.Value, p.Key));
            RtlJump jump = stmt as RtlJump;
            RtlReturn ret = stmt as RtlReturn;
            RtlLabel label = stmt as RtlLabel;
            RtlCall call = stmt as RtlCall;
            RtlCallInOut inOut = stmt as RtlCallInOut;
            if (ret != null)
            {
                Util.DebugWriteLine("RETURN: " + outVars.Count);
                
                
                for (int rr = 0; rr < regs.Count; rr++)
                {
                    string rx = assignment[rr];
                    if (rx != null)
                    {
                        newStmts.Add(new RtlComment("spill variable " + rx + " from register " + regs[rr]));
                        sStore(Spill(rx), regs[rr], rx);
                    }
                }
            }
            if (jump == null)
            {
                List<string> spilledArgs = new List<string>();
                
                if (inOut != null)
                {
                    string reg = ((RtlVar)(inOut.args[0].e)).getName();
                    string var = regToVar[reg];
                    bool isPtr = IsPtr(var);
                    int offset = 4 * inOut.index;
                    RtlExp slot = new RtlExpComputed(e => isPtr ? StackOMemPtr(offset) : StackOMem(offset));
                    newStmts.Add(new RtlComment(inOut.comment));
                    if (inOut.isRet)
                    {
                        if (isPtr)
                        {
                            callPtrRets = Math.Max(callPtrRets, inOut.index + 1);
                        }
                        else
                        {
                            callIntRets = Math.Max(callIntRets, inOut.index + 1);
                            
                            newStmts.Add(new RtlInst(null,
                                new RtlVar[] {new RtlVar(var, true)}, new RtlVar[0],
                                new RtlExp[] {new RtlLiteral(
                                    CompileMethod.IntToTyped(varTypes[var], slotMem(offset)))},
                                true));
                        }
                        Util.DebugWriteLine("  var = " + var + " live = " + String.Join(",", liveVars[i].Keys) + " live' = " + String.Join(",", liveVars[i + 1].Keys));
                        if (i + 1 >= liveVars.Count || liveVars[i + 1].ContainsKey(var))
                        {
                            Util.DebugWriteLine("sLoad inOut: " + reg + " " + slot + " " + var);
                            sLoad(reg, slot, var);
                        }
                    }
                    else
                    {
                        if (isPtr)
                        {
                            callPtrArgs = Math.Max(callPtrArgs, inOut.index + 1);
                        }
                        else
                        {
                            callIntArgs = Math.Max(callIntArgs, inOut.index + 1);
                        }
                        sStore(slot, reg, var);
                    }
                }
                else
                {
                    newStmts.Add(stmt);
                    
                    defs.Where(x => !IsPtr(x)).ToList()
                        .ForEach(x => newStmts.Add(new RtlInst(null,
                            new RtlVar[] {new RtlVar(x, true)}, new RtlVar[0],
                            new RtlExp[] {new RtlLiteral(
                                CompileBase.IntToTyped(varTypes[x], Reg(varToReg[x])))},
                            true)));
                }
                
                Util.DebugWriteLine("sLoad spilled: " + String.Join(", ", spilledArgs.Select(arg => "(" + varToReg[arg] + " <- " + arg + ")")));
                spilledArgs.ForEach(arg => sLoad(varToReg[arg], Spill(arg), arg));
            }
            if (label != null && label.loop)
            {
                List<RtlExp> typeInvs = new List<RtlExp>();
                newStmts.Add(new RtlComment("loop invariants"));
                foreach (string x in liveVars[i].Keys)
                {
                    if (defVars[i].Contains(x))
                    {
                        compileMethod.AddTypeWellFormed(typeInvs, x, false, varTypes[x]);
                        string save_x = x;
                        RtlExp loc = varToReg.ContainsKey(x) ? new RtlVar(Reg(varToReg[x]), false)
                            : (RtlExp)new RtlExpComputed(e => spillMem(Spill(save_x)));
                        if (IsPtr(x))
                        {
                            string absData = "Abs_" + TypeString(varTypes[x]) + "(" + x + ")";
                            if (varToReg.ContainsKey(x))
                            {
                                newStmts.Add(new RtlAssert(new RtlLiteral(
                                    "HeapAbsData(heap, " + x + "__abs) == " + absData), true));
                                newStmts.Add(new RtlAssert(new RtlExpComputed(e =>
                                    "HeapValue(objLayouts, true, $toAbs, " + loc + ", " + save_x + "__abs)"), true));
                                if (IsArray(x))
                                {
                                    newStmts.Add(new RtlAssert(new RtlLiteral(
                                        x + "__abs == " + x + ".arrAbs"), true));
                                }
                            }
                            else
                            {
                                newStmts.Add(new RtlAssert(new RtlExpComputed(e =>
                                    "StackAbsSlot(heap, $stacksFrames, " + spillLoc(Spill(save_x)) + ") == " + absData), true));
                                if (IsArray(x))
                                {
                                    newStmts.Add(new RtlAssert(new RtlExpComputed(e =>
                                        "frameGet($stacksFrames, " + spillLoc(Spill(save_x)) + ") == " + save_x + ".arrAbs"), true));
                                }
                            }
                        }
                        else
                        {
                            newStmts.Add(new RtlAssert(CompileMethod.IntEqTyped(varTypes[x],
                                new RtlVar(x, false),
                                new RtlExpComputed(e => loc.ToString())), true));
                        }
                    }
                }
                typeInvs.ForEach(e => newStmts.Add(new RtlAssert(e, true)));
            }
            
            bool fallThru = (ret == null && i + 1 < stmts.Count && (jump == null || jump.cond != null));
            if (jump != null)
            {
                
                
                
                transitionTarget(labels[jump.label], fallThru ? (i + 1) : labels[jump.label]);
                newStmts.Add(stmt);
            }
            if (fallThru)
            {
                transitionTarget(i + 1, i + 1);
            }
        }
        return newStmts;
    }

    public Dictionary<string, string> MakeMap(List<string> assignment)
    {
        Dictionary<string, string> map = new Dictionary<string, string>();
        for (int i = 0; i < regs.Count; i++)
        {
            if (assignment[i] != null)
            {
                map.Add(assignment[i], regs[i]);
            }
        }
        return map;
    }
}
