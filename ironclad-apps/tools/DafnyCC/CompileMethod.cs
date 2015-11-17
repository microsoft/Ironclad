using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using Type = Microsoft.Dafny.Type;
using System.Numerics;

public class CompileMethod: CompileMethodGhost
{
    public readonly DafnyCC dafnycc;
    Dictionary<string,string> jumpOps = new Dictionary<string,string>();
    Dictionary<string,string> jumpOpsNot = new Dictionary<string,string>();
    RegAlloc alloc;
    List<string> whileEnd = new List<string>();
    List<string> instructionProcArgs = null;
    
    public int IPSize;

    public CompileMethod(DafnySpec dafnySpec, Method method, TypeApply typeApply,
        TextWriter writer, TextWriter iwriter, string moduleName, List<string> imports):
        base(dafnySpec, method, typeApply, writer, iwriter, moduleName, imports)
    {
        dafnycc = (DafnyCC)dafnySpec;
        IPSize = dafnycc.IPSize;

        jumpOps.Add("Eq", "==");
        jumpOps.Add("Neq", "!=");
        jumpOps.Add("Lt", "<");
        jumpOps.Add("Gt", ">");
        jumpOps.Add("Le", "<=");
        jumpOps.Add("Ge", ">=");

        jumpOpsNot.Add("Eq", "!=");
        jumpOpsNot.Add("Neq", "==");
        jumpOpsNot.Add("Lt", ">=");
        jumpOpsNot.Add("Gt", "<=");
        jumpOpsNot.Add("Le", ">");
        jumpOpsNot.Add("Ge", "<");
    }

    public static string ProcName(bool isGhost, string x) { return DafnyCC.ProcName(isGhost, x); }

    string NewLabel()
    {
        return "L" + (tempCount++);
    }

    public RtlVar AsVarOrTemp(Expression exp)
    {
        RtlVar var = AsVar(exp);
        if (var == null)
        {
            var = TempVar(exp.Type);
            AddExpression(var, exp);
        }
        return var;
    }

    BigInteger? AsInt(Expression exp)
    {
        exp = GetExp(exp);
        LiteralExpr literal = exp as LiteralExpr;
        BinaryExpr binary = exp as BinaryExpr;
        if (literal != null)
        {
            if (literal.Value == null)
            {
                throw new Exception("unexpected null literal");
                
            }
            else if (literal.Value is bool)
            {
                return new BigInteger(((bool)(literal.Value)) ? 1 : 0);
            }
            else
            {
                return (BigInteger)(literal.Value);
            }
        }
        else if (binary != null)
        {
            BigInteger? i1 = AsInt(binary.E0);
            BigInteger? i2 = AsInt(binary.E1);
            if (i1 != null && i2 != null)
            {
                switch (binary.Op)
                {
                    case BinaryExpr.Opcode.Add: return i1 + i2;
                    case BinaryExpr.Opcode.Sub: return i1 - i2;
                    case BinaryExpr.Opcode.Mul: return i1 * i2;
                }
            }
            return null;
        }
        else
        {
            return null;
        }
    }

    RtlExp AsSimple(Expression exp)
    {
        exp = GetExp(exp);
        RtlVar var = AsVar(exp);
        BigInteger? i = AsInt(exp);
        if (var != null)
        {
            return var;
        }
        else if (i != null)
        {
            return new RtlInt((BigInteger)i);
        }
        else
        {
            return null;
        }
    }

    RtlExp AsSimpleOrTemp(Expression exp)
    {
        RtlExp re = AsSimple(exp);
        if (re == null)
        {
            RtlVar var = TempVar(exp.Type);
            AddExpression(var, exp);
            re = var;
        }
        return re;
    }

    //- group stmts[startIndex..stmts.Count-1] into single statement
    public void GroupStatements(int startIndex)
    {
        List<RtlStmt> group = new List<RtlStmt>();
        while (stmts.Count > startIndex)
        {
            group.Add(stmts[startIndex]);
            stmts.RemoveAt(startIndex);
        }
        stmts.Add(new RtlStmtGroup(group));
    }

    void Move(RtlVar dest, RtlExp src, bool isPtr)
    {
        RtlVar src_var = src as RtlVar;
        string comment = "move:: " + dest + " := " + src + "  // isPtr = " + isPtr;
        if (!dest.isGhost)
        {
            if (src is RtlMem)
            {
                throw new Exception("internal error: Move RtlMem"); 
            }
            string ins = "instr_Mov";
            stmts.Add(new RtlInst(ins, new RtlVar[] { dest }, new RtlVar[0], new RtlExp[] { src }, false)
                .WithComment(comment));
        }
        if (dest.isGhost || isPtr)
        {
            stmts.Add(new RtlInst(null, new RtlVar[] { dest }, new RtlVar[0], new RtlExp[] { src }, true)
                .WithComment(comment));
        }
        if (isPtr && src_var != null)
        {
            RtlVar dest_abs = new RtlVar(dest.x + "__abs", dest.isGhost, dest.type);
            RtlVar src_abs = new RtlVar(src_var.x + "__abs", src_var.isGhost, src_var.type);
            stmts.Add(new RtlInst(null, new RtlVar[] { dest_abs }, new RtlVar[0], new RtlExp[] { src_abs }, true)
                .WithComment(comment));
        }
    }






    void Label(string label, bool loop = false)
    {
        stmts.Add(new RtlLabel(label, loop).WithComment("label:: " + label + "  // isLoop = " + loop));
    }

    void JumpIfHasType(string label, RtlVar e0, string constructor, Type targetType, bool jumpIf)
    {
        int start = stmts.Count;
        string targetTag = "Tag_" + TypeString(AppType(targetType)) + "_" + constructor;
        RtlVar objTag = TempVar(Type.Int);
        stmts.Add(new RtlStmtComputed(
            s => "call r, mems := loadTag_" + TypeString(AppType(targetType))
                + "(r, core_state, stk, statics, io, mems, $commonVars, "
                + "$gcVars, $toAbs, $absMem, $stacksFrames, objLayouts, heap, "
                + s.args[0] + ", " + new RtlMem(s.args[1].e, "4").AsOperand() + ", "
                + e0 + ", " + e0 + "__abs, " + RegAlloc.Reg(s.args[1].ToString()) + ");",
            new List<RtlArg> { new RtlArg(false, true, objTag), new RtlArg(true, false, e0) }, false)
            .WithComment("datatype_isConstructor:: " + targetTag));
        GroupStatements(start);
        Jump(label, new RtlBinary(
            (jumpIf ? "==" : "!="), objTag, new RtlLiteral("OConst(" + targetTag + ")")));
    }

    void Jump(string label, RtlBinary e = null)
    {
        if (e != null)
        {
            RtlInt ri0 = e.e0 as RtlInt;
            RtlInt ri1 = e.e1 as RtlInt;
            if (ri0 != null && ri1 != null)
            {
                //- would be illegal x86 instruction, so optimize away
                var i0 = ri0.i;
                var i1 = ri1.i;
                bool b;
                switch (e.op)
                {
                    case "==": b = i0 == i1; break;
                    case "!=": b = i0 != i1; break;
                    case "<":  b = i0 <  i1; break;
                    case "<=": b = i0 <= i1; break;
                    case ">":  b = i0 >  i1; break;
                    case ">=": b = i0 >= i1; break;
                    default: throw new Exception("not implemented: " + e.op);
                }
                if (!b)
                {
                    return; //- branch not taken
                }
                e = null; //- branch taken
            }
            else if (ri0 != null)
            {
                //- would be illegal x86 instruction, so swap operands
                string op;
                switch (e.op)
                {
                    case "==": op = "=="; break;
                    case "!=": op = "!="; break;
                    case "<":  op = ">"; break;
                    case "<=": op = ">="; break;
                    case ">":  op = "<"; break;
                    case ">=": op = "<="; break;
                    default: throw new Exception("not implemented: " + e.op);
                }
                e = new RtlBinary(op, e.e1, e.e0);
            }
        }
        stmts.Add(new RtlJump(label, e).WithComment("jump_to_label:: " + label + " condition = " + e));
    }

    void Jump(string label, Expression exp, bool jumpIf = true)
    {
        exp = GetExp(exp);
        RtlExp e = AsSimple(exp);
        BinaryExpr binary = exp as BinaryExpr;
        UnaryExpr unary = exp as UnaryExpr;
        MemberSelectExpr memberSelect = exp as MemberSelectExpr;
        if (e != null)
        {
            Jump(label, new RtlBinary(jumpIf ? "!=" : "==", e, new RtlInt(0)));
        }
        else if (binary != null && jumpOps.ContainsKey(binary.Op.ToString()))
        {
            Type t = AppType(binary.E0.Type);
            UserDefinedType ut = t as UserDefinedType;
            if (!t.Equals(AppType(binary.E1.Type)))
            {
                throw new Exception("not supported: comparison of values with different types");
            }
            else if (t is SeqType && (binary.Op == BinaryExpr.Opcode.Eq || binary.Op == BinaryExpr.Opcode.Neq))
            {
                var tmp = TempVar(Type.Bool);
                var m = dafnySpec.GetSeqMethod(AppType(t), "seq_Equal");
                AddCall(new List<RtlVar> { tmp }, false, true, m.Item1,
                    new List<RtlVar> { null, null },
                    new List<Expression> { binary.E0, binary.E1 },
                    m.Item1.Outs, m.Item2);
                jumpIf = (jumpIf == (binary.Op == BinaryExpr.Opcode.Eq));
                Jump(label, new RtlBinary(jumpIf ? "!=" : "==", tmp, new RtlInt(0)));
            }
            else if (t is IntType || t is BoolType || (ut != null && ut.Name == "array"))
            {
                RtlExp e0 = AsSimpleOrTemp(binary.E0);
                RtlExp e1 = AsSimpleOrTemp(binary.E1);
                Jump(label, new RtlBinary(
                    (jumpIf ? jumpOps : jumpOpsNot)[binary.Op.ToString()], e0, e1));
            }
            else
            {
                throw new Exception("not supported: comparison of values of type " + t);
            }
        }
        else if (binary != null && binary.Op == BinaryExpr.Opcode.Iff && jumpIf)
        {
            Jump(label, DafnySpec.MakeBinaryExpr(BinaryExpr.Opcode.Or, BinaryExpr.ResolvedOpcode.Or, Type.Bool,
                DafnySpec.MakeBinaryExpr(BinaryExpr.Opcode.And, BinaryExpr.ResolvedOpcode.And, Type.Bool, binary.E0, binary.E1),
                DafnySpec.MakeBinaryExpr(BinaryExpr.Opcode.And, BinaryExpr.ResolvedOpcode.And, Type.Bool,
                    new UnaryOpExpr(binary.tok, UnaryOpExpr.Opcode.Not, binary.E0),
                    new UnaryOpExpr(binary.tok, UnaryOpExpr.Opcode.Not, binary.E1))), jumpIf);
        }
        else if (binary != null && binary.Op == BinaryExpr.Opcode.Imp)
        {
            Jump(label, DafnySpec.MakeBinaryExpr(BinaryExpr.Opcode.Or, BinaryExpr.ResolvedOpcode.Or, Type.Bool,
                new UnaryOpExpr(binary.tok, UnaryOpExpr.Opcode.Not, binary.E0), binary.E1), jumpIf);
        }
        else if (binary != null && (
                    (binary.Op == BinaryExpr.Opcode.Or && jumpIf)
                 || (binary.Op == BinaryExpr.Opcode.And && !jumpIf)))
        {
            Jump(label, binary.E0, jumpIf);
            Jump(label, binary.E1, jumpIf);
        }
        else if (binary != null && (
                    (binary.Op == BinaryExpr.Opcode.Or && !jumpIf)
                 || (binary.Op == BinaryExpr.Opcode.And && jumpIf)))
        {
            string skip = NewLabel();
            Jump(skip, binary.E0, !jumpIf);
            Jump(label, binary.E1, jumpIf);
            Label(skip);
        } 
        else if (unary != null && unary is UnaryOpExpr && ((UnaryOpExpr)unary).Op == UnaryOpExpr.Opcode.Not)
        {
            Jump(label, unary.E, !jumpIf);
        }
        else if (memberSelect != null && memberSelect.Member is Field && memberSelect.MemberName.EndsWith("?"))
        {
          string constructor = memberSelect.MemberName.Substring(0, memberSelect.MemberName.Length - 1);
            RtlVar e0 = AsVarOrTemp(memberSelect.Obj);
            JumpIfHasType(label, e0, constructor, memberSelect.Obj.Type, jumpIf);
        }
        else
        {
            RtlVar tmp = TempVar(exp.Type);
            AddExpression(tmp, exp);
            Jump(label, new RtlBinary(jumpIf ? "!=" : "==", tmp, new RtlInt(0)));
        }
    }

    void ArrayLength(RtlVar dest, RtlExp eArr)
    {
        string abs = eArr + "__abs";
        int start = stmts.Count;
        stmts.Add(new RtlStmtComputed(
            s => "call r, mems := loadArrayElement(r, core_state, stk, statics, io, mems, $commonVars, "
                + "$gcVars, $toAbs, $absMem, $stacksFrames, objLayouts, heap, "
                + s.args[0] + ", " + new RtlMem(s.args[1].e, new RtlInt(4)).AsOperand() + ", "
                + "(0 - 1), " + abs + ", " + RegAlloc.Reg(s.args[1].ToString()) + ");",
            new List<RtlArg> { new RtlArg(false, true, dest), new RtlArg(true, false, eArr) }, false)
            .WithComment("loadArrayElement"));
        GroupStatements(start);
    }

    string BinaryInstOp(BinaryExpr.Opcode op)
    {
        string wrapped_op = "instr_" + op.ToString();
        switch (op)
        {
            case BinaryExpr.Opcode.Add:
            case BinaryExpr.Opcode.Sub:
            case BinaryExpr.Opcode.Mul:
                return wrapped_op + "Checked";
            default:
                return wrapped_op;
        }
    }

    void AddBoolViaJump(RtlVar dest, Expression exp)
    {
        //- dest = 0
        //- if (e1 == e2) goto skip
        //-   dest = 1
        //- skip:
        Move(dest, new RtlInt(0), false);
        string skip = NewLabel();
        Jump(skip, exp, false);
        Move(dest, new RtlInt(1), false);
        Label(skip);
    }

    void AddBinary(RtlVar dest, string op, Expression exp0, Expression exp1,
        List<string> pinRegs = null, string envIn = null, string envOut = null)
    {
        exp0 = GetExp(exp0);
        exp1 = GetExp(exp1);
        RtlVar x0 = AsVar(exp0);
        RtlVar x1 = AsVar(exp1);
        RtlExp e1 = AsSimple(exp1);
        if (x0 == null)
        {
            RtlVar tmp = TempVar(exp0.Type);
            AddExpression(tmp, exp0);
            x0 = tmp;
        }
        else if (x0.getName() != dest.getName())
        {
            if ((x1 != null && x1.getName() != dest.getName()) || (x1 == null && e1 != null))
            {
                //- a := b - c;
                //- ==>
                //-   a := b;
                //-   a := a - c;
                Move(dest, x0, false);
                x0 = dest;
            }
            else
            {
                //- a := b - a;
                //- ==>
                //-   tmp := b;
                //-   tmp := tmp - a;
                //-   a := tmp;
                RtlVar tmp = TempVar(exp0.Type);
                Move(tmp, x0, false);
                x0 = tmp;
            }
        }
        if (e1 == null)
        {
            RtlVar tmp = TempVar(exp1.Type);
            AddExpression(tmp, exp1);
            e1 = tmp;
        }
        var inst = new RtlInst(
            op,
            new RtlVar[0],
            new RtlVar[] { x0 },
            new RtlExp[] { e1 },
            false, envIn, envOut);
        if (pinRegs != null)
        {
            for (int i = 0; i < 2; i++)
            {
                inst.args[i].pinReg = pinRegs[i];
            }
        }
        stmts.Add(inst.WithComment("binary_assignment:: " + dest + " := " + op + "(" + x0 + ", " + x1 + ")"));
        if (x0.getName() != dest.getName())
        {
            Move(dest, x0, false);
        }
    }

    SeqTree AddBuildSequenceRec(Expression exp, List<Tuple<bool,Expression>> flatExps)
    {
        BinaryExpr binary = exp as BinaryExpr;
        SeqDisplayExpr seqDisplay = exp as SeqDisplayExpr;
        if (seqDisplay != null)
        {
            foreach (Expression ei in seqDisplay.Elements)
            {
                flatExps.Add(Tuple.Create(false, ei));
            }
            return new SeqTree(null, null, seqDisplay.Elements.Count);
        }
        else if (binary != null && binary.ResolvedOp == BinaryExpr.ResolvedOpcode.Concat)
        {
            var s0 = AddBuildSequenceRec(binary.E0, flatExps);
            var s1 = AddBuildSequenceRec(binary.E1, flatExps);
            return new SeqTree(s0, s1, -1);
        }
        else
        {
            //- leaf of the append tree (assumed to be a sequence)
            flatExps.Add(Tuple.Create(true, exp));
            return null;
        }
    }

    void AddBuildSequence(RtlVar dest, Expression exp)
    {
        List<Tuple<bool,Expression>> flatExps = new List<Tuple<bool,Expression>>();
        var tree = AddBuildSequenceRec(exp, flatExps);
        
        var m = dafnycc.GetSeqBuildMethod(AppType(exp.Type), tree, flatExps.ConvertAll(x => x.Item1));
        AddCall(new List<RtlVar> { dest }, false, true, m.Item1, flatExps.ConvertAll(x => x.Item2), m.Item1.Outs, m.Item2);
    }

    void AddFieldSelect(RtlVar dest, RtlVar obj, Type objType, string fieldName, Type fieldType, RtlExp expGhost)
    {
        string typeAndField = TypeString(AppType(objType)) + "_" + fieldName;
        string abs = obj + "__abs";
        string offset = "Offset_" + typeAndField;
        int start = stmts.Count;
        stmts.Add(new RtlStmtComputed(
            s => "call r, mems := loadField_" + typeAndField
                + "(r, core_state, stk, statics, io, mems, $commonVars, "
                + "$gcVars, $toAbs, $absMem, $stacksFrames, objLayouts, heap, "
                + s.args[0] + ", " + new RtlMem(s.args[1].e, offset).AsOperand() + ", "
                + obj + ", " + abs + ", " + RegAlloc.Reg(s.args[1].ToString()) + ");",
            new List<RtlArg> { new RtlArg(false, true, dest), new RtlArg(true, false, obj) }, false)
            .WithComment("datatype_loadField:: " + fieldName));
        GroupStatements(start);
        if (IsPtrType(AppType(fieldType)))
        {
            RtlVar dest_abs = new RtlVar(dest + "__abs", dest.isGhost, dest.type);
            RtlExp src_abs = new RtlLiteral("$absMem[" + abs + "][" + offset + " div 4 + 1]");
            stmts.Add(new RtlInst(null, new RtlVar[] { dest }, new RtlVar[0], new RtlExp[] { expGhost }, true));
            stmts.Add(new RtlInst(null, new RtlVar[] { dest_abs }, new RtlVar[0], new RtlExp[] { src_abs }, true));
        }
    }

    public void AddMatch<Case>(RtlVar dest, Expression src, List<Case> cases,
        Func<Case,Expression> bodyExp, Func<Case,List<Statement>> bodyStmts)
        where Case:MatchCase
    {
        //- match src { case c1(ps1) => s1 ... cn(psn) => sn }
        //-   -->
        //- var x := src;
        //- if x is c1 { var ps1 := ...x.f1...; s1 } else
        //- if x is c2 { var ps2 := ...x.f2...; s2 } else
        //-            { var ps3 := ...x.f3...; s3 }
        string end = NewLabel();
        RtlVar x = TempVar(src.Type);
        AddExpression(x, src);
        for (int k = 0; k < cases.Count; k++)
        {
            Case c = cases[k];
            bool isLast = (k == cases.Count - 1);
            string skip = NewLabel();
            if (!isLast)
            {
                JumpIfHasType(skip, x, c.Ctor.Name, src.Type, false);
            }
            var oldRenamer = PushRename();
            for (int i = 0; i < c.Arguments.Count; i++)
            {
                var a = c.Arguments[i];
                var f = c.Ctor.Formals[i];
                AddVarDecl(a.Name, a.Type, a.IsGhost);
                RtlExp ghostExp = new RtlLiteral("(" + f.Name + "#" + c.Ctor.Name + "(" + x + "))");
                if (a.IsGhost)
                {
                    MoveGhost(AsVar(a), ghostExp);
                }
                else
                {
                    AddFieldSelect(AsVar(a), x, src.Type, f.Name, f.Type, ghostExp);
                }
            }
            if (bodyExp != null)
            {
                AddExpression(dest, bodyExp(c));
            }
            if (bodyStmts != null)
            {
                bodyStmts(c).ForEach(AddStatement);
            }
            if (!isLast)
            {
                Jump(end);
                Label(skip);
            }
            PopRename(oldRenamer);
        }
        Label(end);
    }

    void AddExpression(RtlVar dest, Expression exp)
    {
        Util.Assert(!isPrinting);
        Util.Assert(!dest.isGhost);
        exp = GetExp(exp);
        Util.DebugWriteLine("exp: " + exp.GetType());
        StmtExpr stmtExpr = exp as StmtExpr;
        RtlVar var = AsVar(exp);
        BigInteger? intExp = AsInt(exp);
        BinaryExpr binary = exp as BinaryExpr;
        UnaryExpr unary = exp as UnaryExpr;
        ITEExpr ite = exp as ITEExpr;
        LetExpr letExp = exp as LetExpr;
        MatchExpr matchExp = exp as MatchExpr;
        FunctionCallExpr funCall = exp as FunctionCallExpr;
        DatatypeValue dataVal = exp as DatatypeValue;
        MemberSelectExpr memberSelect = exp as MemberSelectExpr;
        SeqSelectExpr seqSelect = exp as SeqSelectExpr;
        SeqUpdateExpr seqUpdate = exp as SeqUpdateExpr;
        SeqDisplayExpr seqDisplay = exp as SeqDisplayExpr;

        if (stmtExpr != null)
        {
            
            if (stmtExprEnabled)
            {
                if (ignoreStmtExpr == 0)
                {
                    AddGhostStatement(stmtExpr.S, null);
                }
                AddExpression(dest, stmtExpr.E);
                return;
            }
            else
            {
                throw new Exception("not implemented: cannot handle statement expression here");
            }
        }

        if (var != null)
        {
            Util.DebugWriteLine("dest = " + dest + " var = " + var);
            Move(dest, var, IsPtrType(AppType(exp.Type)));
        }
        else if (intExp != null)
        {
            Move(dest, new RtlInt((BigInteger)intExp), false);
        }
        else if (binary != null)
        {
            switch (binary.ResolvedOp)
            {
                case BinaryExpr.ResolvedOpcode.Concat:
                {
                    AddBuildSequence(dest, exp);
                    return;
                }
            }
            if (IsPtrType(AppType(binary.E0.Type)) || IsPtrType(AppType(binary.E1.Type)))
            {
                throw new Exception("binary operators only implemented for integer and bool types");
            }
            if (jumpOps.ContainsKey(binary.Op.ToString()))
            {
                AddBoolViaJump(dest, exp);
            }
            else
            {
                switch (binary.Op)
                {
                    case BinaryExpr.Opcode.And:
                    case BinaryExpr.Opcode.Or:
                    case BinaryExpr.Opcode.Imp:
                    case BinaryExpr.Opcode.Iff:
                        AddBoolViaJump(dest, exp);
                        break;
                    case BinaryExpr.Opcode.Mul:
                    case BinaryExpr.Opcode.Div:
                    case BinaryExpr.Opcode.Mod:
                    {
                        bool nonlinear = !(IsConstant(binary.E0) || IsConstant(binary.E1));
                        bool isDivMod = (binary.Op == BinaryExpr.Opcode.Div || binary.Op == BinaryExpr.Opcode.Mod);
                        string sop = isDivMod ? "DivMod" : binary.Op.ToString();
                        var m = dafnySpec.FindMethod((nonlinear ? "Method_" : "method_") + sop);
                        //Expression zero = new LiteralExpr(binary.tok, 0); 
                        AddCallInstruction(
                            (binary.Op == BinaryExpr.Opcode.Mod) ? new List<RtlVar> { dest, TempVar(Type.Int) } :
                                new List<RtlVar> { TempVar(Type.Int), dest },
                            m.Ins, DafnySpec.SimpleSanitizedName(m),
                            isDivMod ? new List<Expression> { null, binary.E0, binary.E1 } :
                                new List<Expression> { binary.E0, binary.E1 },
                            m.Attributes,
                            isDivMod ? new List<RtlExp> { new RtlInt(0), null, null } : null);
                        break;
                    }
                    default:
                        AddBinary(dest, BinaryInstOp(binary.Op), binary.E0, binary.E1);
                        break;
                }
            }
        }
        else if (unary != null && unary is UnaryOpExpr && ((UnaryOpExpr)unary).Op == UnaryOpExpr.Opcode.Not)
        {
            AddBoolViaJump(dest, exp);
        } 
        else if (unary != null && unary is UnaryOpExpr && ((UnaryOpExpr)unary).Op == UnaryOpExpr.Opcode.Cardinality)
        {
            var m = dafnySpec.GetSeqMethod(AppType(unary.E.Type), "seq_Length");
            AddCall(new List<RtlVar> { dest }, false, false, m.Item1, new List<Expression> { unary.E },
                m.Item1.Outs, m.Item2);
        }
        else if (ite != null)
        {
            //- if (!e) goto skip1
            //-   then-body
            //-   goto skip2
            //- skip1:
            //-   else-body
            //- skip2:
            string skip1 = NewLabel();
            Jump(skip1, ite.Test, false);
            AddExpression(dest, ite.Thn);
            string skip2 = NewLabel();
            Jump(skip2);
            Label(skip1);
            AddExpression(dest, ite.Els);
            Label(skip2);
        }
        else if (letExp != null)
        {
            if (!letExp.Exact)
            {
                throw new Exception("not implemented: LetExpr: " + letExp);
            }
            for (int i = 0; i < letExp.LHSs.Count; i++)
            {
                var lhs = letExp.LHSs[i];
                var rhs = letExp.RHSs[i];
                string name = GhostVar(lhs.Var.Name);
                if (allVars.Keys.Contains(name))
                {
                    AddRename(lhs.Var.Name);
                    name = GhostVar(lhs.Var.Name);
                }
                RtlVar lhsVar = new RtlVar(name, lhs.Var.IsGhost, AppType(lhs.Var.Type));
                allVars.Add(name, lhsVar);
                AddExpression(lhsVar, rhs);
            }
            AddExpression(dest, letExp.Body);
        }
        else if (matchExp != null)
        {
            if (matchExp.MissingCases.Count != 0)
            {
                throw new Exception("not implemented: MatchExpr with missing cases: " + matchExp);
            }
            AddMatch(dest, matchExp.Source, matchExp.Cases, c => c.Body, null);
        }
        else if (funCall != null)
        {
            if (Attributes.Contains(funCall.Function.Attributes, "dafnycc_inline"))
            {
                TypeApply app = dafnySpec.Compile_Function(funCall.Function,
                    funCall.TypeArgumentSubstitutions.ToDictionary(p => p.Key, p => AppType(p.Value)));
                string funName = FunName(SimpleName(app.AppName()));
                Dictionary<IVariable,Expression> substMap = new Dictionary<IVariable,Expression>();
                for (int i = 0; i < funCall.Function.Formals.Count; i++)
                {
                    substMap.Add(funCall.Function.Formals[i], funCall.Args[i]);
                }
                Translator.Substituter subst = new Translator.Substituter(null, substMap, new Dictionary<TypeParameter,Type>(), null);
                Expression body = subst.Substitute(funCall.Function.Body);
                AddExpression(dest, body);
                List<RtlExp> rtlArgs = funCall.Args.ConvertAll(e => GhostExpression(e));
                stmts.Add(new RtlAssert(new RtlBinary("==", dest, new RtlApply(funName, rtlArgs))));
                return;
            }
            string name = SimpleName(funCall.Function.Name);
            switch (name)
            {
                case "and":
                case "or":
                case "xor":
                {
                    string op = "instr_" + Char.ToUpper(name[0]) + name.Substring(1);
                    AddBinary(dest, op, funCall.Args[0], funCall.Args[1]);
                    break;
                }
                default:
                {
                    TypeApply app = dafnySpec.Compile_Function(funCall.Function,
                        funCall.TypeArgumentSubstitutions.ToDictionary(p => p.Key, p => AppType(p.Value)));
                    AddCall(new List<RtlVar> { dest }, false, DafnySpec.IsHeapFunction(funCall.Function),
                        funCall.Function, funCall.Args,
                        new List<Formal> { new Formal(funCall.tok, "__result", funCall.Type, false, false) }, app);
                    SymdiffLinearityPoint();
                    break;
                }
            }
        }
        else if (dataVal != null)
        {
            List<Expression> args = new List<Expression> { dataVal }.Concat(dataVal.Arguments).ToList();
            List<Formal> ins = new List<Formal> { new Formal(dataVal.tok, "data", AppType(dataVal.Type), true, true) }
                .Concat(dataVal.Ctor.Formals).ToList();
            string name = dafnySpec.Compile_Constructor(dataVal.Type, dataVal.Ctor.Name,
                dataVal.InferredTypeArgs, typeApply.typeArgs).AppName();
            AddCall(new List<RtlVar> { dest }, false, true, ins, "Alloc_" + name, args,
                new List<Formal> { new Formal(dataVal.tok, "ret", AppType(dataVal.Type), false, false) });
        } 
        else if (memberSelect != null && memberSelect.Member is Field && memberSelect.MemberName.EndsWith("?"))
        {
            AddBoolViaJump(dest, exp);
        } 
        else if (memberSelect != null && memberSelect.Member is Field && DafnySpec.IsArrayType(AppType(memberSelect.Obj.Type))
            && memberSelect.MemberName == "Length")
        {
            RtlVar eArr = AsVarOrTemp(memberSelect.Obj);
            ArrayLength(dest, eArr);
        } 
        else if (memberSelect != null && memberSelect.Member is Field && !memberSelect.Member.IsStatic && AppType(memberSelect.Obj.Type) is UserDefinedType
            && memberSelect.Member is DatatypeDestructor)
        {
            RtlVar e0 = AsVarOrTemp(memberSelect.Obj);
            if (minVerify)
            {
                //- run-time type check
                string fail = NewLabel();
                string ok = NewLabel();
                DatatypeDestructor field = (DatatypeDestructor) memberSelect.Member;
                JumpIfHasType(ok, e0, field.EnclosingCtor.Name, memberSelect.Obj.Type, true);
                Label(fail, true);
                Jump(fail);
                Label(ok, false);
            }
            AddFieldSelect(dest, e0, memberSelect.Obj.Type, memberSelect.MemberName, exp.Type, GhostExpression(exp));
        }
        else if (seqSelect != null)
        {
            if (seqSelect.SelectOne && DafnySpec.IsArrayType(AppType(seqSelect.Seq.Type)))
            {
                RtlVar eArr = AsVarOrTemp(seqSelect.Seq);
                RtlExp eInd = AsSimpleOrTemp(seqSelect.E0);
                if (minVerify)
                {
                    //- run-time bounds check
                    string fail = NewLabel();
                    string ok = NewLabel();
                    RtlVar eLen = TempVar(Type.Int);
                    ArrayLength(eLen, eArr);
                    Jump(ok, new RtlBinary("<", eInd, eLen));
                    Label(fail, true);
                    Jump(fail);
                    Label(ok, false);
                }
                string abs = eArr + "__abs";
                int start = stmts.Count;
                stmts.Add(new RtlStmtComputed(
                    s => "call r, mems := loadArrayElement(r, core_state, stk, statics, io, mems, $commonVars, "
                        + "$gcVars, $toAbs, $absMem, $stacksFrames, objLayouts, heap, "
                        + s.args[0] + ", "
                        + new RtlMem(s.args[1].e, new RtlInt(4), s.args[2].e, new RtlInt(8)).AsOperand() + ", "
                        + eInd + ", " + abs + ", " + RegAlloc.Reg(s.args[1].ToString()) + ");",
                    new List<RtlArg> {
                        new RtlArg(false, true, dest),
                        new RtlArg(true, false, eArr),
                        new RtlArg(true, false, eInd)
                    }, false)
                    .WithComment("loadArrayElement"));
                GroupStatements(start);
            }
            else if (seqSelect.SelectOne)
            {
                var m = dafnySpec.GetSeqMethod(AppType(seqSelect.Seq.Type), "seq_Index");
                AddCall(new List<RtlVar> { dest }, false, true, m.Item1, new List<Expression> { seqSelect.Seq, seqSelect.E0 },
                    m.Item1.Outs, m.Item2);
            }
            else
            {
                RtlVar seq;
                if (DafnySpec.IsArrayType(AppType(seqSelect.Seq.Type)))
                {
                    seq = TempVar(seqSelect.Type);
                    var m = dafnySpec.FindMethod("seq_FromArray");
                    AddCall(new List<RtlVar> { seq }, false, true, m,
                        new List<Expression>() { seqSelect.Seq }, m.Outs);
                }
                else
                {
                    seq = AsVarOrTemp(seqSelect.Seq);
                }
                if (seqSelect.E0 != null && seqSelect.E1 != null)
                {
                    var m = dafnySpec.GetSeqMethod(AppType(seqSelect.Type), "seq_TakeDrop");
                    AddCall(new List<RtlVar> { dest }, false, true, m.Item1,
                        new List<RtlVar> { seq, null, null },
                        new List<Expression> { null, seqSelect.E0, seqSelect.E1 },
                        m.Item1.Outs, m.Item2);
                }
                else if (seqSelect.E1 != null)
                {
                    var m = dafnySpec.GetSeqMethod(AppType(seqSelect.Type), "seq_Take");
                    AddCall(new List<RtlVar> { dest }, false, true, m.Item1,
                        new List<RtlVar> { seq, null },
                        new List<Expression> { null, seqSelect.E1 },
                        m.Item1.Outs, m.Item2);
                }
                else if (seqSelect.E0 != null)
                {
                    var m = dafnySpec.GetSeqMethod(AppType(seqSelect.Type), "seq_Drop");
                    AddCall(new List<RtlVar> { dest }, false, true, m.Item1,
                        new List<RtlVar> { seq, null },
                        new List<Expression> { null, seqSelect.E0 },
                        m.Item1.Outs, m.Item2);
                }
                else
                {
                    Move(dest, seq, true);
                }
            }
        }
        else if (seqUpdate != null)
        {
            if (seqUpdate.ResolvedUpdateExpr != null) {
                AddExpression(dest, seqUpdate.ResolvedUpdateExpr);
            } else {
                var m = dafnySpec.GetSeqMethod(AppType(seqSelect.Seq.Type), "seq_Update");
                AddCall(new List<RtlVar> { dest }, false, true, m.Item1,
                    new List<Expression> { seqUpdate.Seq, seqUpdate.Index, seqUpdate.Value },
                    m.Item1.Outs, m.Item2);
            }
        }
        else if (seqDisplay != null)
        {
            AddBuildSequence(dest, exp);
            return;
        }
        else
        {
            throw new Exception("not implemented: " + dest + " := " + exp);
        }
    }

    void AddAssignmentRhs(RtlVar dest, AssignmentRhs rhs)
    {
        Util.DebugWriteLine("dest = " + dest + " rhs: " + rhs.GetType());
        ExprRhs expRhs = rhs as ExprRhs;
        TypeRhs typRhs = rhs as TypeRhs;
        if (expRhs != null)
        {
            AddExpression(dest, expRhs.Expr);
        }
        else if (typRhs != null && DafnySpec.IsArrayType(AppType(typRhs.Type)) && typRhs.ArrayDimensions.Count == 1)
        {
            List<Formal> ins = new List<Formal> { new Formal(Bpl.Token.NoToken, "count", Type.Int, true, false) };
            AddCall(new List<RtlVar> { dest }, false, true, ins, "AllocArrayOfInt",
                new List<Expression> { typRhs.ArrayDimensions[0] },
                new List<Formal> { new Formal(Bpl.Token.NoToken, "ret", AppType(typRhs.Type), false, false) });
        }
        else
        {
            throw new Exception("not implemented: " + rhs + ": " + rhs.GetType());
        }
    }

    RtlExp AssignmentRhsAsSimpleOrTemp(Type t, AssignmentRhs rhs)
    {
        ExprRhs expRhs = rhs as ExprRhs;
        if (expRhs != null)
        {
            RtlExp re = AsSimple(expRhs.Expr);
            if (re != null)
            {
                return re;
            }
        }
        RtlVar tmp = TempVar(t);
        AddAssignmentRhs(tmp, rhs);
        return tmp;
    }

    void AssignSeqLhs(RtlVar eSeq, RtlExp eInd, RtlExp eVal)
    {
        if (minVerify)
        {
            
            string fail = NewLabel();
            string ok = NewLabel();
            RtlVar eLen = TempVar(Type.Int);
            ArrayLength(eLen, eSeq);
            Jump(ok, new RtlBinary("<", eInd, eLen));
            Label(fail, true);
            Jump(fail);
            Label(ok, false);
        }
        string abs = eSeq + "__abs";
        RtlExp dest = new RtlMem(eSeq, new RtlInt(4), eInd, new RtlInt(8));
        int start = stmts.Count;
        stmts.Add(new RtlStmtComputed(
            s => "call mems, $absMem := storeArrayElement(r, core_state, stk, statics, io, mems, "
                + "$commonVars, $gcVars, $toAbs, $absMem, $stacksFrames, objLayouts, heap, "
                + s.args[1].AsOperand() + ", " + s.args[2].AsOperand() + ", "
                + eInd + ", " + eVal + ", " + abs + ", " + RegAlloc.Reg(s.args[0].ToString()) + ");",
            new List<RtlArg> {
                new RtlArg(true, false, eSeq),
                new RtlArg(true, false, dest), //- make sure dest, eVal are loaded before call to storeArrayElement
                new RtlArg(true, false, eVal)  //-   (otherwise, invariants fail)
                }, false)
            .WithComment("storeArrayElement"));
        GroupStatements(start);
    }

    Tuple<RtlVar,Action> AssignLhs(Expression lhs)
    {
        IdentifierExpr idExp = lhs as IdentifierExpr;
        SeqSelectExpr seqSelect = lhs as SeqSelectExpr;
        if (idExp != null)
        {
            return Tuple.Create(AsVar(idExp), (Action)(() => {}));
        }
        else if (seqSelect != null && seqSelect.SelectOne && DafnySpec.IsArrayType(AppType(seqSelect.Seq.Type)))
        {
            RtlVar eSeq = AsVarOrTemp(seqSelect.Seq);
            RtlExp eInd = AsSimpleOrTemp(seqSelect.E0);
            RtlVar tmp = TempVar(lhs.Type);
            return Tuple.Create(tmp, (Action)(() => { AssignSeqLhs(eSeq, eInd, tmp); }));
        }
        else
        {
            throw new Exception("not implemented: assignment to " + lhs);
        }
    }

    List<Tuple<string,string>> InstructionAttributes(Attributes attrs)
    {
        for (; attrs.Name != "instruction"; attrs = attrs.Prev) {}
      
        return attrs.Args.ConvertAll(a => ((string)((StringLiteralExpr)a).Value)).ConvertAll(a => a.Contains("@")
            ? Tuple.Create(a.Substring(0, a.IndexOf('@')), a.Substring(a.IndexOf('@') + 1))
            : Tuple.Create(a, (string)null));
    }

    public RtlMem AsRtlMem(Expression e)
    {
        BinaryExpr bin = e as BinaryExpr;
        if (bin != null && bin.Op == BinaryExpr.Opcode.Add && AsSimple(bin.E1) is RtlInt)
        {
            return new RtlMem(AsVarOrTemp(bin.E0), AsSimple(bin.E1));
        }
        else
        {
            return new RtlMem(AsVarOrTemp(e), new RtlInt(0));
        }
    }

    public void AddCallInstruction(List<RtlVar> destVars, List<Formal> ins, string name, List<Expression> args,
        Attributes attrs, List<RtlExp> rtlExps = null)
    {
        name = GhostProcName(name);
        var operands = InstructionAttributes(attrs);
        bool strictOperands = Attributes.Contains(attrs, "strict_operands");
        bool modifiesIo = Attributes.Contains(attrs, "modifies_io");
        string envArgs = ", objLayouts, $S, $toAbs, $absMem, $commonVars, $gcVars, init, stk, statics, core_state, ptMem, mems, $stacksFrames";
        string envIn = modifiesIo ? ", io" + envArgs : "";
        string envOut = modifiesIo ? ", io" : "";
        for (int i = 0; i < args.Count; i++)
        {
            RtlExp re = (rtlExps == null) ? null : rtlExps[i];
            envIn += ", " + ((re != null) ? re.ToString() : GhostExpression(args[i]).ToString());
        }
        envOut += String.Concat(destVars.Select(x => ", " + x));
        if (instructionProcArgs != null)
        {
            var operandString = String.Concat(instructionProcArgs.Select(arg => ", " + arg));
            stmts.Add(new RtlGhostStmtComputed(s => "call r" + envOut + " := " + name + "(r" + envIn + operandString + ");", new RtlExp[0]));
        }
        else if (destVars.Count == 1 && args.Count == 2 && operands.Count == 2
            && operands[0].Item1 == "inout" && operands[1].Item1 == "in"
            && !strictOperands)
        {
            //- optimized path for binary expressions
            AddBinary(destVars[0], name, args[0], args[1], operands.ConvertAll(o => o.Item2), envIn, envOut);
        }
        else
        {
            List<RtlArg> rtlArgs = new List<RtlArg>();
            int kIn = 0;
            int kOut = 0;
            foreach (var opn in operands)
            {
                RtlExp re = (rtlExps == null) ? null : rtlExps[kIn];
                RtlArg arg;
                switch (opn.Item1)
                {
                    case "in":
                        if (strictOperands && (re == null || re is RtlInt))
                        {
                            var tmp = TempVar(Type.Int);
                            if (re == null) { AddExpression(tmp, args[kIn]); }
                            else { Move(tmp, re, false); }
                            arg = new RtlArg(true, false, tmp);
                        }
                        else
                        {
                            arg = new RtlArg(true, false, re != null ? re : AsSimpleOrTemp(args[kIn]));
                        }
                        kIn++;
                        break;
                    case "inout":
                        if (re == null) { AddExpression(destVars[kOut], args[kIn]); }
                        else { Move(destVars[kOut], re, false); }
                        kIn++;
                        arg = new RtlArg(true, true, destVars[kOut++]);
                        break;
                    case "out": arg = new RtlArg(false, true, destVars[kOut++]); break;
                    case "mem": arg = new RtlArg(true, false, re != null ? re : AsRtlMem(args[kIn])); kIn++; break;
                    default: throw new Exception("expected 'in', 'inout', 'out', or 'mem' on instruction attributes");
                }
                arg.pinReg = opn.Item2;
                rtlArgs.Add(arg);
            }
            stmts.Add(new RtlInst(name, rtlArgs, false, envIn, envOut));
        }
    }

    public void AddCall(List<RtlVar> destVars, bool isGhost, bool isHeap, List<Formal> ins, string name,
        List<RtlVar> argVars, List<Expression> args, List<Formal> rets)
    {
        if (isGhost)
        {
            AddGhostCall(destVars, name, args, isHeap);
            return;
        }
        Util.Assert(args.Count == ins.Count);
        Util.Assert(args.Count == argVars.Count);
        Util.Assert(rets != null || destVars.Count == 1);
        List<RtlExp> rtlArgs = new List<RtlExp>();
        int numIntRets = (rets == null) ? 1 : rets.Count(x => !x.IsGhost && !IsPtrType(AppType(x.Type)));
        int numPtrRets = (rets == null) ? 1 : rets.Count(x => !x.IsGhost && IsPtrType(AppType(x.Type)));
        int argIntIndex = numIntRets;
        int argPtrIndex = numPtrRets;
        List<RtlStmt> argStmts = new List<RtlStmt>();
        for (int i = 0; i < args.Count; i++)
        {
            Util.Assert(argVars[i] != null || args[i] != null);
            Util.Assert(argVars[i] == null || args[i] == null);
            var arg = args[i];
            var formal = ins[i];
            RtlVar argVar = (argVars[i] != null) ? argVars[i] : AsVar(arg);
            bool isPtr = IsPtrType((argVars[i] != null) ? argVars[i].type : AppType(arg.Type));
            if (formal.IsGhost)
            {
                rtlArgs.Add(GhostExpression(arg));
            }
            else
            {
                if (argVar != null)
                {
                    rtlArgs.Add(argVar);
                }
                else
                {
                    RtlVar tmp = TempVar(args[i].Type);
                    AddExpression(tmp, args[i]);
                    rtlArgs.Add(tmp);
                }
                argStmts.Add(new RtlCallInOut(isPtr ? argPtrIndex : argIntIndex, false, rtlArgs[i])
                    .WithComment("push argument #" + i + " at index " + (isPtr ? argPtrIndex : argIntIndex)
                        + " isPtr = " + isPtr + " argument = " + rtlArgs[i]));
                if (isPtr)
                {
                    argPtrIndex++;
                }
                else
                {
                    argIntIndex++;
                }
            }
        }
        name = ProcName(isGhost, name);
        if (name == procName)
        {
            throw new Exception("recursive calls not supported in non-ghost procedure: " + method.Name);
        }
        stmts.AddRange(argStmts);
        calledMethods.Add(name);
        stmts.Add(new RtlCall(name, destVars, rtlArgs, isGhost)
            .WithComment("call:: " + String.Join(",", destVars) + " := " + name
                + "(" + String.Join(", ", rtlArgs.ToList()) + ")  // isGhost = " + isGhost));
        if (rets != null)
        {
            int retIntIndex = 0;
            int retPtrIndex = 0;
            Util.Assert(rets.Count == destVars.Count);
            for (int i = 0; i < rets.Count; i++)
            {
                Util.Assert(destVars[i] == null || destVars[i].isGhost || !rets[i].IsGhost);
                if (!rets[i].IsGhost)
                {
                    RtlVar dest = destVars[i];
                    if (dest == null || dest.isGhost)
                    {
                        dest = TempVar(rets[i].Type);
                    }
                    bool isPtr = IsPtrType(AppType(rets[i].Type));
                    stmts.Add(new RtlCallInOut(isPtr ? retPtrIndex : retIntIndex, true, dest)
                        .WithComment("pop return value #" + i + " at index " + (isPtr ? retPtrIndex : retIntIndex)
                            + " into destination " + destVars[i] + " isPtr = " + isPtr));
                    if (isPtr)
                    {
                        retPtrIndex++;
                    }
                    else
                    {
                        retIntIndex++;
                    }
                }
            }
        }
        else
        {
            stmts.Add(new RtlCallInOut(0, true, destVars[0])
                .WithComment("pop single return value from function into destination:: " + destVars[0]));
        }
    }

    public void AddCall(List<RtlVar> destVars, bool isGhost, bool isHeap, List<Formal> ins, string name, List<Expression> args, List<Formal> rets)
    {
        AddCall(destVars, isGhost, isHeap, ins, name, new RtlVar[args.Count].ToList(), args, rets);
    }

    private void AddCall<T>(List<RtlVar> destVars, bool isGhost, bool isHeap, T target, List<Expression> args, List<Formal> rets) where T : MemberDecl, ICallable
    {
        AddCall(destVars, isGhost, isHeap, target.Ins, DafnySpec.SimpleSanitizedName(target), args, rets);
    }

    private void AddCall<T>(List<RtlVar> destVars, bool isGhost, bool isHeap, T target,
        List<RtlVar> argVars, List<Expression> args, List<Formal> rets, TypeApply typeApply)  where T : MemberDecl, ICallable
    {
        rets = rets.ConvertAll(x => new Formal(x.tok, x.Name, typeApply.AppType(x.Type), x.InParam, x.IsGhost));
        Method method = target as Method;
        Function fun = target as Function;
        Attributes attrs = (method != null) ? method.Attributes : (fun != null) ? fun.Attributes : null;
        if (Attributes.Contains(attrs, "instruction"))
        {
            AddCallInstruction(destVars, target.Ins, DafnySpec.SimpleSanitizedName(target), args,
                attrs);
        }
        else
        {
            AddCall(destVars, isGhost, isHeap, target.Ins, SimpleName(typeApply.AppName()), argVars, args, rets);
        }
    }

    private void AddCall<T>(List<RtlVar> destVars, bool isGhost, bool isHeap, T target,
        List<Expression> args, List<Formal> rets, TypeApply typeApply) where T : MemberDecl, ICallable
    {
        AddCall(destVars, isGhost, isHeap, target, new RtlVar[args.Count].ToList(), args, rets, typeApply);
    }

    void AddReturn(List<AssignmentRhs> rhss)
    {
        Util.Assert(!isGhost);
        if (rhss != null)
        {
            Util.Assert(method.Outs.Count == rhss.Count);
            for (int i = 0; i < method.Outs.Count; i++)
            {
                RtlVar dest = new RtlVar(GhostVar(method.Outs[i].Name, false), method.Outs[i].IsGhost, AppType(method.Outs[i].Type));
                AddAssignmentRhs(dest, rhss[i]);
            }
        }
        
        if (instructionProcArgs == null)
        {
            stmts.Add(new RtlReturn(method.Outs.Select(x => new RtlVar(GhostVar(x.Name), x.IsGhost, AppType(x.Type))))
                .WithComment("return"));
        }
    }

    void AddVarDecl(string varName, Type t, bool isGhost)
    {
        string name = GhostVar(varName);
        if (allVars.Keys.Contains(name))
        {
            AddRename(varName);
            name = GhostVar(varName);
        }
        allVars.Add(name, new RtlVar(name, isGhost, AppType(t)));
    }

    public override void AddResolvedGhostStatement(Statement stmt, Attributes attrs)
    {
        MatchStmt matchStmt = stmt as MatchStmt;

        if (matchStmt != null)
        {
            
            if (matchStmt.MissingCases.Count != 0)
            {
                throw new Exception("not implemented: MatchStmt with missing cases: " + matchStmt);
            }
            
            
            
            
            
            
            var cases = matchStmt.Cases;
            RtlVar x = TempVar(matchStmt.Source.Type);
            MoveGhost(x, GhostExpression(matchStmt.Source));
            foreach (MatchCaseStmt c in cases)
            {
                var oldRenamer = PushRename();
                for (int i = 0; i < c.Arguments.Count; i++)
                {
                    var a = c.Arguments[i];
                    var f = c.Ctor.Formals[i];
                    AddGhostVarDecl(a.Name, a.Type, true);
                    RtlExp ghostExp = new RtlLiteral("(" + f.Name + "#" + c.Ctor.Name + "(" + x + "))");
                    MoveGhost(AsVar(a), ghostExp);
                }
                stmts.Add(new RtlGhostStmtComputed(s => "if (" + x + " is " + c.Ctor.Name + ") {",
                    new RtlExp[] {}));
                Indent();
                c.Body.ForEach(s => AddGhostStatement(s, attrs));
                Unindent();
                stmts.Add(new RtlGhostStmtComputed(s => "}", new RtlExp[0]));
                PopRename(oldRenamer);
            }
        }
        else
        {
            base.AddResolvedGhostStatement(stmt, attrs);
        }
    }

    void AddResolvedStatement(Statement stmt)
    {
        Util.DebugWriteLine("stmt: " + stmt.GetType());
        Util.Assert(!isGhost);
        Util.Assert(!stmt.IsGhost || stmt is CalcStmt);
        BlockStmt block = stmt as BlockStmt;
        IfStmt ifStmt = stmt as IfStmt;
        WhileStmt whileStmt = stmt as WhileStmt;
        BreakStmt breakStmt = stmt as BreakStmt;
        ReturnStmt returnStmt = stmt as ReturnStmt;
        AssertStmt assertStmt = stmt as AssertStmt;
        AssignStmt assignStmt = stmt as AssignStmt;
        CallStmt callStmt = stmt as CallStmt;
        VarDeclStmt varDecl = stmt as VarDeclStmt;
        MatchStmt matchStmt = stmt as MatchStmt;
        CalcStmt calcStmt = stmt as CalcStmt;
        ForallStmt forallStmt = stmt as ForallStmt;
        PrintStmt printStmt = stmt as PrintStmt;

        if (block != null)
        {
            var oldRenamer = PushRename();
            block.Body.ForEach(AddStatement);
            PopRename(oldRenamer);
        }
        else if (varDecl != null)
        {
            foreach (var varLocal in varDecl.Locals) { 
                AddVarDecl(varLocal.Name, varLocal.Type, varLocal.IsGhost);
            }
            if (varDecl.Update != null) {
                Util.Assert(varDecl.Update is UpdateStmt);
                //Util.Assert(varDecl.Update.Lhss.Count() == 1);
                //AddAssignmentRhs(AsVar(varDecl.Update.Lhss[0]), ((UpdateStmt)varDecl.Update).Rhss[0]);
                AddStatement(varDecl.Update);
            }
        }
        else if (assignStmt != null)
        {
            IdentifierExpr idExp = assignStmt.Lhs as IdentifierExpr;
            SeqSelectExpr seqSelect = assignStmt.Lhs as SeqSelectExpr;
            if (idExp != null)
            {
                AddAssignmentRhs(AsVar(assignStmt.Lhs), assignStmt.Rhs);
            }
            else if (seqSelect != null && seqSelect.SelectOne && DafnySpec.IsArrayType(AppType(seqSelect.Seq.Type)))
            {
                RtlVar eSeq = AsVarOrTemp(seqSelect.Seq);
                RtlExp eInd = AsSimpleOrTemp(seqSelect.E0);
                RtlExp eVal = AssignmentRhsAsSimpleOrTemp(assignStmt.Lhs.Type, assignStmt.Rhs);
                AssignSeqLhs(eSeq, eInd, eVal);
            }
            else
            {
                throw new Exception("not implemented: assignment to " + assignStmt.Lhs);
            }
        }
        else if (callStmt != null)
        {
            var lhss = callStmt.Lhs.ConvertAll(AssignLhs);
            AddCall(lhss.ConvertAll(lhs => lhs.Item1), stmt.IsGhost, DafnySpec.IsHeapMethod(callStmt.Method),
                callStmt.Method, callStmt.Args, callStmt.Method.Outs, dafnySpec.Compile_Method(callStmt.Method,
                    callStmt.MethodSelect.TypeArgumentSubstitutions().ToDictionary(p => p.Key, p => AppType(p.Value))));
            lhss.ForEach(lhs => lhs.Item2());
            SymdiffLinearityPoint();
        }
        else if (ifStmt != null)
        {
            //- if (!e) goto skip1
            //-   then-body
            //-   goto skip2
            //- skip1:
            //-   else-body
            //- skip2:
            string skip1 = NewLabel();
            Jump(skip1, ifStmt.Guard, false);
            AddStatement(ifStmt.Thn);
            if (ifStmt.Els == null)
            {
                Label(skip1);
            }
            else
            {
                string skip2 = NewLabel();
                Jump(skip2);
                Label(skip1);
                AddStatement(ifStmt.Els);
                Label(skip2);
            }
        }
        else if (whileStmt != null)
        {
            //- goto begin
            //- loop:
            //-   body
            //- begin:
            //-   assert ...;
            //-   if (e) goto loop
            //- end:
            string loop = NewLabel();
            string begin = NewLabel();
            string end = NewLabel();
            whileEnd.Add(end);
            Jump(begin);
            Label(loop);
            AddStatement(whileStmt.Body);
            Label(begin, true);
            foreach (MaybeFreeExpression mexp in whileStmt.Invariants)
            {
                Util.Assert(!mexp.IsFree);
                if (!minVerify)
                {
                    bool old_stmtExprEnabled = stmtExprEnabled;
                    stmtExprEnabled = false; 
                    stmts.Add(new RtlAssert(GhostExpression(mexp.E), true));
                    stmtExprEnabled = old_stmtExprEnabled;
                }
            }
            SymdiffLinearityPoint();
            stmts.Add(new RtlLoopStart());
            Jump(loop, whileStmt.Guard);
            whileEnd.RemoveAt(whileEnd.Count - 1);
            Label(end);
        }
        else if (breakStmt != null && breakStmt.TargetLabel == null)
        {
            Jump(whileEnd[whileEnd.Count - breakStmt.BreakCount]);
        }
        else if (returnStmt != null)
        {
            AddReturn(returnStmt.rhss);
        }
        else if (assertStmt != null)
        {
            if (minVerify)
            {
                return;
            }
            stmts.Add(new RtlAssert(GhostExpression(assertStmt.Expr)));
        }
        else if (matchStmt != null)
        {
            if (matchStmt.MissingCases.Count != 0)
            {
                throw new Exception("not implemented: MatchStmt with missing cases: " + matchStmt);
            }
            AddMatch(null, matchStmt.Source, matchStmt.Cases, null, c => c.Body);
        }
        else if (calcStmt != null)
        {
            AddGhostStatement(calcStmt, null);
        }
        else if (forallStmt != null)
        {
            AddGhostStatement(forallStmt, null);
        }
        else if (printStmt != null)
        {
            Util.Assert(printStmt.Args.Count == 1);
            var m = dafnySpec.FindMethod("print_int");
            AddCall(new List<RtlVar>(), false, true, m,
                new List<Expression>() { printStmt.Args[0] }, m.Outs);
        }
        else
        {
            throw new Exception("not implemented: " + stmt);
        }
    }

    void AddStatement(Statement stmt)
    {
        Util.Assert(!isPrinting);
        if (isGhost || (stmt.IsGhost && !(stmt is CalcStmt)))
        {
            AddGhostStatement(stmt, null);
            return;
        }
        stmts.Add(new RtlComment("###LINE: " + stmt.Tok.filename + ": " + stmt.Tok.line));
        List<Statement> resolved = ResolveStmt(stmt);
        if (resolved != null)
        {
            resolved.ForEach(AddStatement);
        }
        else
        {
            AddResolvedStatement(stmt);
        }
    }

    public static bool IsPtrType(Type t)
    {
        return DafnySpec.IsPtrType(t);
    }

    protected void WriteDefaultRelationalRequires(bool isRelational)
    {
        if (isRelational)
        {
            iwriter.WriteLine("    requires public(io_old._inCtr);");
            iwriter.WriteLine("    requires public(io_old._outCtr);");
        }
    }

    protected void WriteDefaultRelationalEnsures(bool isRelational)
    {
        if (isRelational)
        {
            iwriter.WriteLine("    ensures  public(io._inCtr);");
            iwriter.WriteLine("    ensures  public(io._outCtr);");
        }
        else if (dafnycc.relational)
        {
            iwriter.WriteLine("    ensures  io._inCtr == io_old._inCtr && io._outCtr == io_old._outCtr;");
        }
    }

    protected void WriteAllVars()
    {
        allVars.Keys
            .Where(x => !method.Ins.Select(y => GhostVar(y.Name)).ToList().Contains(x)
                && !method.Outs.Select(y => GhostVar(y.Name)).ToList().Contains(x)).ToList()
            .ForEach(x => writer.WriteLine("    var " + x + ":" + TypeString(allVars[x].type) + ";"));
        allVars.Where(x => !x.Value.isGhost && IsPtrType(x.Value.type))
            .ToList().ForEach(x => writer.WriteLine("    var " + x.Key + "__abs:int;"));
    }

    public void CompileInstruction()
    {
        string name = GhostProcName(DafnySpec.SimpleSanitizedName(method));
        bool strictOperands = Attributes.Contains(method.Attributes, "strict_operands");
        List<RtlExp> reqs = method.Req.ConvertAll(a => GhostExpression(a.E, false, false, a.Attributes)); 
        List<RtlExp> enss = method.Ens.ConvertAll(a => GhostExpression(a.E, false, false, a.Attributes));
        AddTypeWellFormed(reqs, method.Ins);
        AddTypeWellFormed(enss, method.Outs);

        List<Tuple<string,string>> operands = InstructionAttributes(method.Attributes);
        List<Tuple<Formal,string>> ins = new List<Tuple<Formal,string>>();
        List<Tuple<Formal,string>> outs = new List<Tuple<Formal,string>>();

        int kIn = 0, kOut = 0;
        List<string> parms = new List<string>();
        List<string> args = new List<string>();
        Func<string,string> opnName = s => "$opn_" + DafnySpec.CleanName(s);
        string outRegs = "";
        List<string> opnReqs = new List<string>();
        List<string> allPins = operands.ConvertAll(p => p.Item2).Where(p => p != null).ToList();
        foreach (var r in operands)
        {
            string arg;
            Action<string,Func<string,string>> opnReq = (a, f) =>
            {
                if (r.Item2 != null) { opnReqs.Add(a + " == " + f(r.Item2)); }
                else if (allPins.Count > 0) { opnReqs.Add(String.Join(" && ", allPins.Select(pin => a + " != " + f(pin)))); }
            };
            switch (r.Item1)
            {
                case "in":
                    arg = opnName(method.Ins[kIn].Name);
                    parms.Add(arg + ":opn");
                    opnReq(arg, s => "OReg(" + s + ")");
                    ins.Add(Tuple.Create(method.Ins[kIn], "Eval(r_old, " + arg + ")"));
                    kIn++;
                    break;
                case "inout":
                    arg = opnName(method.Ins[kIn].Name);
                    parms.Add(arg + ":int");
                    opnReq(arg, s => s);
                    ins.Add(Tuple.Create(method.Ins[kIn], "r_old.regs[" + arg + "]"));
                    kIn++;
                    outs.Add(Tuple.Create(method.Outs[kOut], "r.regs[" + arg + "]"));
                    outRegs += "[" + arg + " := " + GhostVar(method.Outs[kOut].Name) + "]";
                    kOut++;
                    break;
                case "out":
                    arg = opnName(method.Outs[kOut].Name);
                    parms.Add(arg + ":int");
                    opnReq(arg, s => s);
                    outs.Add(Tuple.Create(method.Outs[kOut], "r.regs[" + arg + "]"));
                    outRegs += "[" + arg + " := " + GhostVar(method.Outs[kOut].Name) + "]";
                    kOut++;
                    break;
                case "mem":
                    arg = opnName(method.Ins[kIn].Name);
                    parms.Add(arg + ":opn_mem");
                    ins.Add(Tuple.Create(method.Ins[kIn], "EvalPtr(r_old, " + arg + ")"));
                    kIn++;
                    break;
                default: throw new Exception("expected 'in' or 'inout' or 'out' or 'mem' in attributes of method" + method.Name);
            }
            args.Add(arg);
        }

        if (method.Body != null)
        {
            stmtExprEnabled = true;
            instructionProcArgs = args;
            foreach (var x in method.Ins.Concat(method.Outs))
            {
                string xName = GhostVar(x.Name);
                allVars[xName] = new RtlVar(xName, x.IsGhost, AppType(x.Type));
            }
            foreach (Statement stmt in method.Body.Body)
            {
                AddStatement(stmt);
            }
            instructionProcArgs = null;
            stmtExprEnabled = false;
        }

        bool isRelational = dafnycc.relational && reqs.Concat(enss).ToList().Exists(s =>
            s is RtlApply && (((RtlApply)s).op == "public" || ((RtlApply)s).op == "relation"));
        bool modifiesIo = Attributes.Contains(method.Attributes, "modifies_io");
        string envOther = ", objLayouts:[int]ObjLayout, $S:int, $toAbs:[int]int, $absMem:[int][int]int, $commonVars:commonVars, $gcVars:gcVars, init:bool, stk:mem, statics:mem, core_state:core_state, ptMem:mem, mems:mems, $stacksFrames:[int]Frames";
        string nucArgs = "objLayouts, $S, $toAbs, $absMem, $commonVars, $gcVars, me, init, stk, statics, core_state, ptMem, mems, $stacksFrames";
        string envIn = modifiesIo ? ", linear io_old:IOState" + envOther : "";
        string envOut = modifiesIo ? ", linear io:IOState" : "";
        string pIns = String.Concat(method.Ins.Select(f => ", " + GhostVar(f.Name) + ":" + TypeString(f.Type)));
        string pOuts = String.Concat(method.Outs.Select(f => ", " + GhostVar(f.Name) + ":" + TypeString(f.Type)));
        envIn += pIns;
        envOut += pOuts;

        Util.Assert(!isPrinting);
        isPrinting = true;
        string operandList = String.Concat(parms.Select(p => ", " + p));
        iwriter.WriteLine("atomic procedure " + name + "(my r_old:regs" + envIn + operandList + ") returns(my r:regs" + envOut + ");");
        Func<string,RtlExp,string> lets_e = (lets, e) =>
            !(e is RtlApply) ? lets + e :
            ((RtlApply)e).op == "public" ? "public(" + lets + ((RtlApply)e).args[0] + ")" :
            ((RtlApply)e).op == "relation" ? "relation(" + lets + ((RtlApply)e).args[0] + ")" :
            lets + e;
        if (strictOperands) { opnReqs.ForEach(e => iwriter.WriteLine("    requires " + e + ";")); }
        ins.ForEach(p => iwriter.WriteLine("    requires " + GhostVar(p.Item1.Name) + " == " + p.Item2 + ";"));
        reqs.ForEach(e => iwriter.WriteLine("    requires " + e + ";"));
        if (modifiesIo) { WriteDefaultRelationalRequires(isRelational); }
        if (modifiesIo) { iwriter.WriteLine("    requires NucleusInv(" + nucArgs + ", io_old);"); }
        GetStaticFieldMods().ForEach(x => iwriter.WriteLine("    modifies " + x + ";"));
        enss.ForEach(e => iwriter.WriteLine("    ensures  " + e + ";"));
        iwriter.WriteLine("    ensures  r.regs == r_old.regs" + outRegs + ";");
        if (modifiesIo) { WriteDefaultRelationalEnsures(isRelational); }
        if (modifiesIo) { iwriter.WriteLine("    ensures  NucleusInv(" + nucArgs + ", io);"); }
        if (method.Body != null)
        {
            writer.WriteLine("implementation " + name + "(my r_old:regs" + envIn + operandList + ") returns(my r:regs" + envOut + ")");
            writer.WriteLine("{");
            WriteAllVars();
            writer.WriteLine("r := r_old;");
            if (modifiesIo) { writer.WriteLine("io := io_old;"); }
            dafnySpec.WriteLemmas(writer, this, visibleModules, method.Attributes);
            foreach (RtlStmt s in stmts)
            {
                writer.WriteLine(s);
            }

            writer.WriteLine("}");
        }
        isPrinting = false;
    }

    public override void Compile()
    {
        Util.Assert(!isPrinting);
        
        isGhost = method is Lemma || method.IsGhost;
        procName = ProcName(isGhost, SimpleName(typeApply.AppName()));
        bool isAxiom = Attributes.Contains(method.Attributes, "axiom");
        bool isPublic = Attributes.Contains(method.Attributes, "public");
        bool isImported = Attributes.Contains(method.Attributes, "imported");
        bool isInstruction = Attributes.Contains(method.Attributes, "instruction");
        bool isHeapUnmodified = Attributes.Contains(method.Attributes, "dafnycc_heap_unmodified");
        if (isImported && method.Body == null)
        {
            return;
        }
        if (method.Body == null && method.Name.StartsWith("reveal_")) 
        {
            return;
        }
        if (isGhost)
        {
            if (!minVerify)
            {
                CompileGhost();
            }
            return;
        }
        if (isInstruction)
        {
            CompileInstruction();
            return;
        }

        List<string> inVars = method.Ins.Where(x => !x.IsGhost).ToList().Select(x => GhostVar(x.Name)).ToList();
        List<string> outVars = method.Outs.Where(x => !x.IsGhost).ToList().Select(x => GhostVar(x.Name)).ToList();
        List<Formal> inInts = method.Ins.Where(x => !x.IsGhost && !IsPtrType(AppType(x.Type))).ToList();
        List<Formal> outInts = method.Outs.Where(x => !x.IsGhost && !IsPtrType(AppType(x.Type))).ToList();
        List<Formal> inPtrs = method.Ins.Where(x => !x.IsGhost && IsPtrType(AppType(x.Type))).ToList();
        List<Formal> outPtrs = method.Outs.Where(x => !x.IsGhost && IsPtrType(AppType(x.Type))).ToList();

        foreach (var x in method.Ins.Concat(method.Outs))
        {
            string name = GhostVar(x.Name);
            allVars[name] = new RtlVar(name, x.IsGhost, AppType(x.Type));
        }

        BlockStmt body = method.Body;
        if (body != null)
        {
            bool lastReturn = false;
            stmtExprEnabled = true;
            foreach (Statement stmt in body.Body)
            {
                lastReturn = (stmt is ReturnStmt);
                AddStatement(stmt);
            }
            if (!lastReturn && !isGhost)
            {
                AddReturn(null);
            }
            stmtExprEnabled = false;
            
            stmts = new Optimize(inVars, outVars, stmts).Run();
        }
        alloc = new RegAlloc(dafnySpec, this, inVars, outVars, inInts, outInts, inPtrs, outPtrs, allVars, stmts);
        if (body != null)
        {
            stmts = alloc.Alloc();
        }
        else if (isAxiom)
        {
            stmts = new List<RtlStmt> { new RtlComment("dummy method body for axiom"), new RtlReturn(new RtlVar[0]) };
        }
        List<RtlExp> reqs = minVerify ? new List<RtlExp>()
            : method.Req.ConvertAll(a => GhostExpression(a.E, false, true, a.Attributes));
        List<RtlExp> enss = minVerify ? new List<RtlExp>()
            : method.Ens.ConvertAll(a => GhostExpression(a.E, false, false, a.Attributes));
        AddTypeWellFormed(reqs, method.Ins);
        AddTypeWellFormed(enss, method.Outs);
        bool isRelational = dafnycc.relational && reqs.Concat(enss).ToList().Exists(s =>
            s is RtlApply && (((RtlApply)s).op == "public" || ((RtlApply)s).op == "relation"));
        
        







        Util.DebugWriteLine();
        Func<string, string> regold = s => "r_old.regs[" + s + "]";
        Func<string, string> reg = s => "r.regs[" + s + "]";
        string sMemOld = "stk_old";
        string sMem = "stk";
        string parms = String.Join(", ", method.Ins.Select(x => GhostVar(x.Name) + ":" + TypeString(AppType(x.Type))));
        string rets = String.Join(", ", method.Outs.Select(x => GhostVar(x.Name) + ":" + TypeString(AppType(x.Type))));
        string memVarsOld = "me,init,stk_old,statics_old,core_state,ptMem,mems_old";
        string memVars = "me,init,stk,statics,core_state,ptMem,mems";
        int frameCount = alloc.FrameCount() + dafnycc.framePointerCount;
        int frameSize = frameCount * 4;
        int inOutSize = 4 * alloc.InsOutsCount();
        Func<List<Formal>, string> f = l => (l.Count != 0) ? ", " : "";

        List<Tuple<string,string>> preserveExps = new List<Tuple<string,string>>();
        for (int i = 0; i < method.Mod.Expressions.Count; i++)
        {
            Expression modExp = method.Mod.Expressions[i].E;
            if (!(modExp is ThisExpr))
            {
                RtlExp e = GhostExpression(modExp, false, true);
                preserveExps.Add(Tuple.Create("mod" + i, "(" + e + ").arrAbs"));
            }
        }
        string absExtend = isHeapUnmodified
            ? "$toAbs == $toAbs_old && objLayouts == objLayouts_old"
            : "AbsExtend($toAbs, $toAbs_old, objLayouts, objLayouts_old)";
        string preserveHeap = isHeapUnmodified
            ? "heap == heap_old && $absMem == $absMem_old"
            : DafnyCC.PreserveHeap(minVerify, preserveExps.ConvertAll(p => p.Item2));

        Util.Assert(!isPrinting);
        isPrinting = true;

        string stackPrefix = "stack_size__DafnyCC__";
        //- calculate the statck size
        Func<string, string> g = s => (calledMethods.Count == 0) ? "0" : s;
        if (!isPublic)
        {
            iwriter.WriteLine("const " + stackPrefix + procName + ":int := " + frameSize + " + "
                + g("max(" + String.Join(", max(", calledMethods.Select(s => stackPrefix + s + " + " + IPSize))
                + ", 0)" + String.Join(")", calledMethods.Select(s => ""))) + ";");
            iwriter.WriteLine("procedure " + procName
                + "(my r_old:regs, const my core_state:core_state, linear stk_old:mem, linear statics_old:mem, linear io_old:IOState, linear mems_old:mems"
                + ", $commonVars_old:commonVars, $gcVars_old:gcVars"
                + ", $toAbs_old:[int]int, $absMem_old:[int][int]int, $stacksFrames_old:[int]Frames, objLayouts_old:[int]ObjLayout, heap_old:Heap"
                + f(method.Ins) + parms
                + ") returns(my r:regs, linear stk:mem, linear statics:mem, linear io:IOState, linear mems:mems"
                + ", $commonVars:commonVars, $gcVars:gcVars"
                + ", $toAbs:[int]int, $absMem:[int][int]int, $stacksFrames:[int]Frames, objLayouts:[int]ObjLayout, heap:Heap"
                + f(method.Outs) + rets + ");");
            iwriter.WriteLine("    requires MemInv(" + memVarsOld + ");");
            iwriter.WriteLine("    requires NucleusInv(objLayouts_old,$S,$toAbs_old,$absMem_old,$commonVars_old,$gcVars_old,me,init,stk_old,statics_old,core_state,ptMem,mems_old,$stacksFrames_old,io_old);");
            iwriter.WriteLine("    requires SMemRequireGcRA(" + stackPrefix + procName + ", "
                + inOutSize + ", " + sMemOld + ", " + regold("ESP") + ", RET);");
            iwriter.WriteLine("    requires HeapInv($absMem_old, objLayouts_old, heap_old);");
            WriteDefaultRelationalRequires(isRelational);





            foreach (var p in alloc.inInts)
            {
                int offset = alloc.InIntsOffset() - alloc.OutsOffset() + IPSize + p.Value;
                string val = sMemOld + ".map[" + regold("ESP") + " + " + offset + "]";
                iwriter.WriteLine("    requires " + IntEqTyped(allVars[p.Key].type, p.Key, val) + ";");
            }
            for (int i = 0; i < inPtrs.Count; i++)
            {
                Formal x = inPtrs[i];
                int offset = alloc.InPtrsOffset() - alloc.OutsOffset() + IPSize + alloc.inPtrs[GhostVar(x.Name)];
                string loc = regold("ESP") + " + " + offset + " + stackGcOffset";
                iwriter.WriteLine("    requires StackAbsSlot(heap_old, $stacksFrames_old, "
                    + loc + ") == Abs_"
                    + TypeString(AppType(x.Type)) + "(" + GhostVar(x.Name) + ");");
                if (DafnySpec.IsArrayType(AppType(x.Type)))
                {
                    iwriter.WriteLine("    requires frameGet($stacksFrames_old, " + loc + ") == " + GhostVar(x.Name) + ".arrAbs;");
                }
            }
            reqs.ForEach(e => iwriter.WriteLine("    requires " + e + ";"));
            iwriter.WriteLine("    modifies $Time;");
            GetStaticFieldMods().ForEach(x => iwriter.WriteLine("    modifies " + x + ";"));
            
            iwriter.WriteLine("    ensures  " + reg("ESP") + " == old(" + regold("ESP") + ") + " + IPSize + ";");
            
            iwriter.WriteLine("    ensures  MemInv(" + memVars + ");");
            iwriter.WriteLine("    ensures  NucleusInv(objLayouts,$S,$toAbs,$absMem,$commonVars,$gcVars,me,init,stk,statics,core_state,ptMem,mems,$stacksFrames,io);");
            iwriter.WriteLine("    ensures  SMemEnsureGcF(" + inOutSize + ", " + sMem + ", old(" + sMemOld + "), " + reg("ESP") + ", old(" + regold("ESP") + "), $stacksFrames, $stacksFrames_old);");
            iwriter.WriteLine("    ensures  HeapInv($absMem, objLayouts, heap);");
            iwriter.WriteLine("    ensures  " + absExtend + ";");
            iwriter.WriteLine("    ensures  " + preserveHeap + ";");
            WriteDefaultRelationalEnsures(isRelational);

            enss.ForEach(e => iwriter.WriteLine("    ensures  " + e + ";"));
            /*
            foreach (var p in retMap)
            {
                writer.WriteLine("    ensures  " + reg(p.Value) + " == " + p.Key + ";");
            }
            */
            foreach (var p in alloc.outInts)
            {
                int offset = IPSize + p.Value;
                string val = sMem + ".map[" + regold("ESP") + " + " + offset + "]";
                iwriter.WriteLine("    ensures  " + IntEqTyped(allVars[p.Key].type, p.Key, val) + ";");
            }
            for (int i = 0; i < outPtrs.Count; i++)
            {
                Formal x = outPtrs[i];
                int offset = IPSize + alloc.outPtrs[GhostVar(x.Name)];
                string loc = regold("ESP") + " + " + offset + " + stackGcOffset";
                iwriter.WriteLine("    ensures  StackAbsSlot(heap, $stacksFrames, "
                    + loc + ") == Abs_"
                    + TypeString(AppType(x.Type)) + "(" + GhostVar(x.Name) + ");");
                if (DafnySpec.IsArrayType(AppType(x.Type)))
                {
                    iwriter.WriteLine("    ensures  frameGet($stacksFrames, " + loc + ") == " + GhostVar(x.Name) + ".arrAbs;");
                }
            }
        }
        if (body != null || isAxiom)
        {
            writer.WriteLine("implementation " + procName
                + "(my r_old:regs, const my core_state:core_state, linear stk_old:mem, linear statics_old:mem, linear io_old:IOState, linear mems_old:mems"
                + ", $commonVars_old:commonVars, $gcVars_old:gcVars"
                + ", $toAbs_old:[int]int, $absMem_old:[int][int]int, $stacksFrames_old:[int]Frames, objLayouts_old:[int]ObjLayout, heap_old:Heap"
                + f(method.Ins) + parms
                + ") returns(my r:regs, linear stk:mem, linear statics:mem, linear io:IOState, linear mems:mems"
                + ", $commonVars:commonVars, $gcVars:gcVars"
                + ", $toAbs:[int]int, $absMem:[int][int]int, $stacksFrames:[int]Frames, objLayouts:[int]ObjLayout, heap:Heap"
                + f(method.Outs) + rets + ")");
            writer.WriteLine("{");
            writer.WriteLine("    var $absMem_tmp:[int][int]int;");
            writer.WriteLine("    var objLayouts_tmp:[int]ObjLayout;");
            writer.WriteLine("    var heap_tmp:Heap;");
            writer.WriteLine("    var obj_tmp:int;");
            writer.WriteLine("    var val_tmp:int;");
            preserveExps.ForEach(p => writer.WriteLine("    var " + p.Item1 + ":int;"));
            WriteAllVars();
            dafnySpec.WriteLemmas(writer, this, visibleModules, method.Attributes);
            writer.WriteLine("    r := r_old;");
            writer.WriteLine("    stk := stk_old;");
            writer.WriteLine("    statics := statics_old;");
            writer.WriteLine("    io := io_old;");
            writer.WriteLine("    mems := mems_old;");
            writer.WriteLine("    $commonVars := $commonVars_old;");
            writer.WriteLine("    $gcVars := $gcVars_old;");
            writer.WriteLine("    $toAbs := $toAbs_old;");
            writer.WriteLine("    $absMem := $absMem_old;");
            writer.WriteLine("    $stacksFrames := $stacksFrames_old;");
            writer.WriteLine("    objLayouts := objLayouts_old;");
            writer.WriteLine("    heap := heap_old;");
            for (int i = 0; i < inPtrs.Count; i++)
            {
                Formal x = inPtrs[i];
                int offset = alloc.InPtrsOffset() - alloc.OutsOffset() + IPSize + alloc.inPtrs[GhostVar(x.Name)];
                writer.WriteLine("    " + GhostVar(x.Name) + "__abs := frameGet($stacksFrames, "
                    + regold("ESP") + " + " + offset + " + stackGcOffset);");
            }
            preserveExps.ForEach(p => writer.WriteLine("    " + p.Item1 + " := " + p.Item2 + ";"));
            writer.WriteLine("    assert TV(" + reg("ESP") + ");");
            for (int i = 0; i < frameCount; i++)
            {
                writer.WriteLine("    assert TO(0 - " + (i + 1) + ");");
                writer.WriteLine("    assert TO(" + RegAlloc.stackGcOffset / 4 + " - " + (i + 1) + ");");
            }
            for (int i = frameCount; i < alloc.FrameVisibleCount(); i++)
            {
                writer.WriteLine("    assert TO(" + (i - frameCount) + ");");
                writer.WriteLine("    assert TO(" + (RegAlloc.stackGcOffset / 4 + i - frameCount) + ");");
            }
            if (frameSize != 0)
            {
                writer.WriteLine("    call r := logical_Sub(r, ESP, OConst(" + frameSize + "));");
                if (dafnycc.useFramePointer)
                {
                    writer.WriteLine("    call stk := logical_Store(r, core_state, stk, OMem(MReg(ESP, " + (frameSize - 4) + ")), OReg(EBP));");
                    writer.WriteLine("    call r := instr_LeaUnchecked(r, EBP, OMem(MReg(ESP, " + (frameSize - 4) + ")));");
                }
            }
            bool wasComment= false;
            string indent = "    ";
            foreach (RtlStmt s in stmts)
            {
                RtlIndent rtlIndent = s as RtlIndent;
                RtlLabel label = s as RtlLabel;
                RtlCall call = s as RtlCall;
                if (rtlIndent != null)
                {
                    indent = rtlIndent.Positive ? indent + "    " : indent.Substring(4);
                    continue;
                }
                if (s is RtlReturn && frameSize != 0)
                {
                    if (dafnycc.useFramePointer)
                    {
                        writer.WriteLine("    call r := logical_Load(r, core_state, stk, EBP, OMem(MReg(ESP, " + (frameSize - 4) + ")));");
                    }
                    writer.WriteLine(indent + "call r := logical_Add(r, ESP, OConst(" + frameSize + "));");
                }
                /*
                if (call != null && call.op == "Proc_sample")
                {
                    writer.WriteLine(indent + GhostVar(samplemap) + " := F();");
                }
                 */
                if (s.comment != null)
                {
                    if (!wasComment)
                    {
                        writer.WriteLine();
                    }
                    writer.WriteLine(indent + "// " + s.comment().Replace(Environment.NewLine, Environment.NewLine + indent));
                }
                wasComment = true;
                if (s.ToString() != "")
                {
                    writer.WriteLine(indent + s.ToString().Replace(Environment.NewLine, Environment.NewLine + indent));
                    wasComment = false;
                }
                if (call != null)
                {
                    
                    writer.WriteLine(indent + "assert SMemInvGcF(" + (inOutSize + 4) + ", " + sMem + ", old(" + sMemOld + "), " + reg("ESP") + " + " + frameSize + ", old(" + regold("ESP") + "), $stacksFrames, $stacksFrames_old);");
                    if (dafnycc.useFramePointer) {
                      writer.WriteLine(indent + "call r := instr_LeaUnchecked(r, EBP, OMem(MReg(ESP, " + (frameSize - 4) + ")));");
                    }
                }
                if (label != null && label.loop)
                {
                    writer.WriteLine(indent + "invariant MemInv(" + memVars + ");");
                    writer.WriteLine(indent + "invariant NucleusInv(objLayouts,$S,$toAbs,$absMem,$commonVars,$gcVars,me,init,stk,statics,core_state,ptMem,mems,$stacksFrames,io);");
                    writer.WriteLine(indent + "invariant SMemInvGcF(" + (inOutSize + 4) + ", " + sMem + ", old(" + sMemOld + "), " + reg("ESP") + " + " + frameSize + ", old(" + regold("ESP") + "), $stacksFrames, $stacksFrames_old);");
                    writer.WriteLine(indent + "invariant HeapInv($absMem, objLayouts, heap);");
                    writer.WriteLine(indent + "invariant " + absExtend + ";");
                    writer.WriteLine(indent + "invariant " + preserveHeap + ";");
                    if (isRelational)
                    {
                        writer.WriteLine("    invariant public(io._inCtr);");
                        writer.WriteLine("    invariant public(io._outCtr);");
                    }
                    else if (dafnycc.relational)
                    {
                        writer.WriteLine("    invariant io._inCtr == io_old._inCtr && io._outCtr == io_old._outCtr;");
                    }

                }
                if (s is RtlLoopStart)
                {
                    
                    dafnySpec.WriteLemmas(writer, this, visibleModules, method.Attributes, true);
                }
            }
            writer.WriteLine("}");
        }
        isPrinting = false;
    }
}
