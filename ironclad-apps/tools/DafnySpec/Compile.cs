using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using Type = Microsoft.Dafny.Type;
using System.Numerics;

public class TypeApply
{
    public readonly DafnySpec dafnySpec;
    public readonly string name;
    public readonly List<TypeParameter> typeParams;
    public readonly Dictionary<TypeParameter,Type> typeArgs;
    public readonly Dictionary<string,Type> typeSubsts;
    readonly string appName;
    readonly string appFullName;

    public TypeApply(DafnySpec dafnySpec, string name, List<TypeParameter> typeParams, Dictionary<TypeParameter,Type> typeArgs)
    {
        
        
        this.dafnySpec = dafnySpec;
        this.name = name;
        this.typeParams = typeParams;
        this.typeArgs = new Dictionary<TypeParameter,Type>();
        typeArgs.ToList().ForEach(a => this.typeArgs.Add(a.Key, ToType(a.Value)));
        this.typeSubsts = new Dictionary<string,Type>();
        typeArgs.ToList().ForEach(a => this.typeSubsts.Add(a.Key.Name, ToType(a.Value)));
        
        string suffix = String.Concat(typeParams.Select(p => "___" + dafnySpec.TypeString(typeArgs[p])));
        appName = name + suffix;
        appFullName = name + "__FULL" + suffix;
        int i = appFullName.Contains('.') ? appFullName.LastIndexOf('.') + 1 : 0;
        appFullName = appFullName.Insert(i, DafnySpec.CleanName("#"));
    }

    static Type ToType(Type t)
    {
        return DafnySpec.ToType(t);
    }

    public Type AppType(Type t)
    {
        Util.Assert(t != null);
        
        
        return Resolver.SubstType(t, typeArgs);
    }

    public string AppName()
    {
        return appName;
    }

    public string AppFullName()
    {
        
        return appFullName;
    }

    public override bool Equals(object obj)
    {
        TypeApply that = obj as TypeApply;
        if (that != null && that.name == this.name && that.typeArgs.Count == this.typeArgs.Count)
        {
            Dictionary<string,Type> thisArgs = this.typeArgs.ToDictionary(p => p.Key.ToString(), p => p.Value);
            Dictionary<string,Type> thatArgs = that.typeArgs.ToDictionary(p => p.Key.ToString(), p => p.Value);
            return thatArgs.Keys.ToList().TrueForAll(x => thisArgs.ContainsKey(x) && thatArgs[x].Equals(thisArgs[x]));
        }
        return false;
    }

    public override int GetHashCode()
    {
        return name.GetHashCode() + typeArgs.Values.Sum(t => ("" + t.ToString()).GetHashCode());
    }
}

public class SeqTree
{
    public readonly SeqTree left;
    public readonly SeqTree right;
    public readonly int buildCount; 
    public SeqTree(SeqTree left, SeqTree right, int buildCount) { this.left = left; this.right = right; this.buildCount = buildCount; }

    public static string TreeName(SeqTree s)
    {
        return (s == null) ? "e" : (s.buildCount >= 0) ? s.buildCount.ToString() :
            "a_" + TreeName(s.left) + "_" + TreeName(s.right);
    }
}

public class CompileBase
{
    public DafnySpec dafnySpec;
    public TypeApply typeApply;
    public bool isRecursive;
    public string procName;
    public string recFunName;
    public bool minVerify;
    public bool stmtExprEnabled;
    public int ignoreStmtExpr;
    public List<RtlStmt> stmts = new List<RtlStmt>();
    public List<List<RtlExp>> recCalls = new List<List<RtlExp>>();
    public Dictionary<string,RtlVar> allVars = new Dictionary<string,RtlVar>();
    public List<Dictionary<string,RtlVar>> forallVars = new List<Dictionary<string,RtlVar>>();
    public Dictionary<string,string> renamer = new Dictionary<string,string>();
    public int nextRename;
    public static bool isPrinting = false;
    public TextWriter writer;
    public TextWriter iwriter;
    public string moduleName;
    public List<string> imports;
    public List<string> visibleModules;
    public Type visibleElementType; 
    public int tempCount = 0;

    public CompileBase(DafnySpec dafnySpec, TypeApply typeApply,
        TextWriter writer, TextWriter iwriter, string moduleName, List<string> imports)
    {
        this.dafnySpec = dafnySpec;
        this.typeApply = typeApply;
        this.writer = writer;
        this.iwriter = iwriter;
        this.moduleName = moduleName;
        this.imports = imports;
        this.visibleModules = imports.Concat(new List<string> { moduleName, "private##" + moduleName }).ToList();
    }

    public static string GhostProcName(string x) { return DafnySpec.GhostProcName(x); }
    public static string FunName(string x) { return DafnySpec.FunName(x); }
    public static string SimpleName(string x) { return DafnySpec.SimpleName(x); }
    public Type AppType(Type t) { return typeApply.AppType(t); }
    public string TypeString(Type t) { return dafnySpec.TypeString(t); }

    public string GhostVar(string x, bool allowRename = true)
    {
        return (x == "INTERNAL_absMem") ? "$absMem"
            : "$ghost_" + (allowRename && renamer.ContainsKey(x) ? renamer[x] : "") + DafnySpec.CleanName(x);
    }

    public string TempName()
    {
        return "temp__" + (tempCount++);
    }

    public void AddRename(string x)
    {
        renamer[x] = "_" + (nextRename++) + "_";
    }

    public Dictionary<string,string> PushRename()
    {
        return new Dictionary<string,string>(renamer);
    }

    public Dictionary<string,string> PushRename(string x)
    {
        var oldRenamer = PushRename();
        AddRename(x);
        return oldRenamer;
    }

    public Dictionary<string,string> PushRename(IEnumerable<string> xs)
    {
        var oldRenamer = PushRename();
        xs.ToList().ForEach(AddRename);
        return oldRenamer;
    }

    public void PopRename(Dictionary<string,string> oldRenamer)
    {
        renamer = oldRenamer;
    }

    public RtlStmt PushForall()
    {
        var dict = new Dictionary<string,RtlVar>();
        forallVars.Add(dict);
        return new RtlGhostStmtComputed(s => String.Concat(dict.Values.Select(
            x => "var " + x.x + ":" + TypeString(x.type) + ";")),
            new RtlExp[0]);
    }

    public void PopForall()
    {
        forallVars.RemoveAt(forallVars.Count - 1);
    }

    public void Indent()
    {
        stmts.Add(new RtlIndent(true));
    }

    public void Unindent()
    {
        stmts.Add(new RtlIndent(false));
    }

    public static bool IsConstant(Expression e)
    {
        UnaryOpExpr unary = e as UnaryOpExpr;
        BinaryExpr binary = e as BinaryExpr;
        if (unary!= null)
        {
            return IsConstant(unary.E);
        }
        if (binary != null)
        {
            return IsConstant(binary.E0) && IsConstant(binary.E1);
        }
        return e is LiteralExpr;
    }

    public static string IntToTyped(Type t, string e)
    {
        return
            (t is BoolType) ? "((" + e + ") != 0)" :
            (t is RealType) ? "(real(" + e + "))" :
            e;
    }

    //- Assert that et is a well-formed value of type t, represented by integer ei
    public static RtlExp IntEqTyped(Type t, RtlExp et, RtlExp ei)
    {
        return
            (t is BoolType) ?
                new RtlBinary("||",
                    new RtlBinary("&&", et, new RtlBinary("==", ei, new RtlInt(1))),
                    new RtlBinary("&&", new RtlApply("!", new RtlExp[] { et }), new RtlBinary("==", ei, new RtlInt(0)))) :
            (t is RealType) ? new RtlBinary("==", et, new RtlApply("real", new RtlExp[] { ei })) :
            new RtlBinary("==", et, ei);
    }

    public static string IntEqTyped(Type t, string et, string ei)
    {
        return "(" + IntEqTyped(t, new RtlLiteral(et), new RtlLiteral(ei)) + ")";
    }

    public Expression GetExp(Expression e)
    {
        Expression r = e.WasResolved() ? e.Resolved : e;
        ParensExpression p = e as ParensExpression;
        return (r != null) ? r : (p != null) ? GetExp(p.E) : e;
    }

    public RtlVar TempVar(Type t, bool declare = true)
    {
        string name = "$ghost__" + TempName();
        RtlVar ret = new RtlVar(name, false, AppType(t));
        if (declare)
        {
            allVars.Add(name, ret);
        }
        return ret;
    }

    public RtlVar AsVar(Expression exp)
    {
        exp = GetExp(exp);
        IdentifierExpr id = exp as IdentifierExpr;
        if (id != null)
        {
            //- We're assuming this is a local variable for the moment; otherwise we shouldn't call AppType
            string name = GhostVar(id.Name);
            RtlVar ret = new RtlVar(name, id.Var.IsGhost, AppType(id.Type));
            
            return ret;
        }
        else
        {
            return null;
        }
    }

    public RtlVar AsVar(BoundVar x)
    {
        string name = GhostVar(x.Name);
        return new RtlVar(name, x.IsGhost, AppType(x.Type));
    }

    public string Triggers(Attributes attrs, Func<Expression,RtlExp> f)
    {
        List<List<RtlExp>> triggers = new List<List<RtlExp>>();
        for (; attrs != null; attrs = attrs.Prev)
        {
            if (attrs.Name == "trigger")
            {
                triggers.Add(attrs.Args.ConvertAll(a => f(a)));
            }
        }
        return String.Concat(triggers.Select(es => "{" + String.Join(", ", es) + "}"));
    }

    public RtlExp GhostIfThenElse(RtlExp eTest, Func<RtlExp> feThen, Func<RtlExp> feElse)
    {
        if (stmtExprEnabled && ignoreStmtExpr == 0)
        {
            stmts.Add(new RtlGhostStmtComputed(s => "if (" + eTest + ") {", new RtlExp[0]));
            Indent();
        }
        var eThen = feThen();
        if (stmtExprEnabled && ignoreStmtExpr == 0)
        {
            Unindent();
            stmts.Add(new RtlGhostStmtComputed(s => "}", new RtlExp[0]));
            stmts.Add(new RtlGhostStmtComputed(s => "if (!(" + eTest + ")) {", new RtlExp[0]));
            Indent();
        }
        var eElse = feElse();
        if (stmtExprEnabled && ignoreStmtExpr == 0)
        {
            Unindent();
            stmts.Add(new RtlGhostStmtComputed(s => "}", new RtlExp[0]));
        }
        return new RtlLiteral("(if (" + eTest + ") then ("
            + eThen + ") else (" + eElse + "))");
    }

    public RtlExp GhostLet(Microsoft.Boogie.IToken tok, List<BoundVar> lhss, List<RtlExp> rhss,
        Func<RtlExp> body)
    {
        if (stmtExprEnabled && ignoreStmtExpr == 0)
        {
            var oldRenamer1 = PushRename();
            for (int i = 0; i < lhss.Count; i++)
            {
                var lhs = lhss[i];
                var rhs = rhss[i];
                AddGhostVarDecl(lhs.Name, lhs.Type, true);
                MoveGhost(new RtlVar(GhostVar(lhs.Name), true, AppType(lhs.Type)), rhs);
            }
            body();
            PopRename(oldRenamer1);
        }
        var oldRenamer2 = PushRename();
        lhss.ForEach(e => AddRename(e.Name));
        ignoreStmtExpr++; 
        RtlExp rExp = new RtlLiteral("("
            + String.Concat(lhss.Zip(rhss, (lhs, rhs) =>
                "let " + GhostVar(lhs.Name) + ":" + TypeString(AppType(lhs.Type))
                + " := (" + rhs + ") in "))
            + " (" + body() + "))");
        ignoreStmtExpr--;
        PopRename(oldRenamer2);
        return rExp;
    }

    public RtlExp GhostExpressionRec(Expression exp, bool inRecSpec = false, bool inRequiresOrOld = false)
    {
        Util.Assert(!isPrinting);
        exp = GetExp(exp);
        StmtExpr stmtExpr = exp as StmtExpr;
        IdentifierExpr idExp = exp as IdentifierExpr;
        LiteralExpr literal = exp as LiteralExpr;
        BinaryExpr binary = exp as BinaryExpr;
        UnaryExpr unary = exp as UnaryExpr;
        ITEExpr ite = exp as ITEExpr;
        ExistsExpr existsExp = exp as ExistsExpr;
        ForallExpr forallExp = exp as ForallExpr;
        LetExpr letExp = exp as LetExpr;
        MatchExpr matchExp = exp as MatchExpr;
        OldExpr oldExp = exp as OldExpr;
        FunctionCallExpr funCall = exp as FunctionCallExpr;
        DatatypeValue dataVal = exp as DatatypeValue;
        MemberSelectExpr memberSelect = exp as MemberSelectExpr;
        SeqSelectExpr seqSelect = exp as SeqSelectExpr;
        SeqUpdateExpr seqUpdate = exp as SeqUpdateExpr;
        SeqDisplayExpr seqDisplay = exp as SeqDisplayExpr;

        Func<Expression,RtlExp> G = e => GhostExpression(e, inRecSpec, inRequiresOrOld);

        if (stmtExpr != null)
        {
            if (stmtExprEnabled)
            {
                if (ignoreStmtExpr == 0)
                {
                    AddGhostStatement(stmtExpr.S, null);
                }
                return G(stmtExpr.E);
            }
            else
            {
                throw new Exception("not implemented: cannot handle statement expression here");
            }
        }
        else if (idExp != null)
        {
            return AsVar(idExp);
        }
        else if (literal != null && literal.Value is BigInteger)
        {
            return new RtlInt((BigInteger)(literal.Value));
        }
        else if (literal != null && literal.Value is bool)
        {
            return new RtlLiteral((bool)(literal.Value) ? "true" : "false");
        }
        else if (literal != null && literal.Value == null)
        {
            return new RtlLiteral("ArrayOfInt(0 - 1, NO_ABS)");
        }
        else if (literal != null && literal.Value is Microsoft.Basetypes.BigDec)
        {
            return new RtlLiteral(((Microsoft.Basetypes.BigDec)literal.Value).ToDecimalString());
        }
        else if (binary != null)
        {
            string op = null;
            string internalOp = null;
            CompileFunction compileFunction = this as CompileFunction;
            string thisFuncName = (compileFunction == null) ? null : compileFunction.function.Name;
            switch (binary.ResolvedOp)
            {
                case BinaryExpr.ResolvedOpcode.SeqEq:
                    return new RtlApply(dafnySpec.GetSeqOperationName(AppType(binary.E0.Type), "Seq_Equal"),
                        new RtlExp[] { G(binary.E0), G(binary.E1) });
                case BinaryExpr.ResolvedOpcode.SeqNeq:
                    return new RtlLiteral("(!" +
                        new RtlApply(dafnySpec.GetSeqOperationName(AppType(binary.E0.Type), "Seq_Equal"),
                            new RtlExp[] { G(binary.E0), G(binary.E1) }) + ")");
                case BinaryExpr.ResolvedOpcode.Concat:
                    return new RtlApply(dafnySpec.GetSeqOperationName(AppType(binary.Type), "Seq_Append"),
                        new RtlExp[] { G(binary.E0), G(binary.E1) });
            }
            if (binary.Op == BinaryExpr.Opcode.Exp)
            {
                binary = new BinaryExpr(binary.tok, BinaryExpr.Opcode.Imp, binary.E0, binary.E1);
            }
            switch (binary.Op)
            {
                case BinaryExpr.Opcode.Disjoint:
                case BinaryExpr.Opcode.In:
                case BinaryExpr.Opcode.NotIn:
                    throw new Exception("not implemented: binary operator '" + BinaryExpr.OpcodeString(binary.Op) + "'");
            }
            if (AppType(binary.E0.Type) is IntType && AppType(binary.E1.Type) is IntType)
            {
                switch (binary.Op)
                {
                    case BinaryExpr.Opcode.Le: internalOp = "INTERNAL_le_boogie"; break;
                    case BinaryExpr.Opcode.Lt: internalOp = "INTERNAL_lt_boogie"; break;
                    case BinaryExpr.Opcode.Ge: internalOp = "INTERNAL_ge_boogie"; break;
                    case BinaryExpr.Opcode.Gt: internalOp = "INTERNAL_gt_boogie"; break;
                    case BinaryExpr.Opcode.Add: internalOp = "INTERNAL_add_boogie"; break;
                    case BinaryExpr.Opcode.Sub: internalOp = "INTERNAL_sub_boogie"; break;
                    case BinaryExpr.Opcode.Mul:
                        op = "*";
                        if (thisFuncName != "INTERNAL_mul")
                        {
                            internalOp = FunName("INTERNAL__mul");
                        }
                        break;
                    case BinaryExpr.Opcode.Div:
                        op = "div";
                        if (thisFuncName != "INTERNAL_div")
                        {
                            internalOp = FunName("INTERNAL__div");
                        }
                        break;
                    case BinaryExpr.Opcode.Mod:
                        op = "mod";
                        if (thisFuncName != "INTERNAL_mod")
                        {
                            internalOp = FunName("INTERNAL__mod");
                        }
                        break;
                    default:
                        op = BinaryExpr.OpcodeString(binary.Op);
                        break;
                }
            }
            else
            {
                op = BinaryExpr.OpcodeString(binary.Op);
            }
            if (internalOp == null)
            {
                return new RtlBinary(op, G(binary.E0), G(binary.E1));
            }
            else
            {
                return new RtlApply(internalOp, new RtlExp[]
                    { G(binary.E0), G(binary.E1) });
            }
        } else if (unary != null) {
          if (unary is UnaryOpExpr) {
            UnaryOpExpr unaryOp = (UnaryOpExpr)unary;
            if (unaryOp.Op == UnaryOpExpr.Opcode.Not) {
              return new RtlLiteral("(!(" + G(unaryOp.E) + "))");
            } else if (unaryOp.Op == UnaryOpExpr.Opcode.Cardinality) {
              return new RtlApply(dafnySpec.GetSeqOperationName(AppType(unaryOp.E.Type), "Seq_Length"),
                new RtlExp[] { G(unaryOp.E) });
            } else if (unaryOp.Op == UnaryOpExpr.Opcode.Fresh) {
              Util.Assert(DafnySpec.IsArrayType(unaryOp.E.Type));
              string abs = G(unaryOp.E) + ".arrAbs";
              return new RtlLiteral("(heap_old.absData[" + abs + "] is AbsNone)");
            } else {
              throw new Exception("not implemented: " + exp);
            }
          } else if (unary is ConversionExpr) {
             var e = (ConversionExpr)unary;
             var fromInt = e.E.Type.IsNumericBased(Type.NumericPersuation.Int);
             var toInt = e.ToType.IsNumericBased(Type.NumericPersuation.Int);
             if (fromInt && !toInt) {
                return new RtlApply("real", new RtlExp[] { G(e.E) });
              } else if (!fromInt && toInt) {
                return new RtlApply("int", new RtlExp[] { G(e.E) });
              } else {
                Util.Assert(fromInt == toInt);
                return GhostExpressionRec(e.E, inRecSpec, inRequiresOrOld);
              }
          } else {
            throw new Exception("not implemented: " + exp);
          }
        }
        else if (ite != null)
        {
            return GhostIfThenElse(G(ite.Test), () => G(ite.Thn), () => G(ite.Els));
        }
        else if (funCall != null)
        {
            switch (funCall.Function.Name)
            {
                case "left":
                case "right":
                case "relation":
                case "public":
                    Util.Assert(funCall.Args.Count == 1);
                    return new RtlApply(funCall.Function.Name, new RtlExp[] { G(funCall.Args[0]) });
                case "sizeof":
                    Util.Assert(funCall.Args.Count == 1);
                    return new RtlApply(funCall.Function.Name + "##" + TypeString(AppType(funCall.Args[0].Type)),
                        new RtlExp[] { G(funCall.Args[0]) });
                case "INTERNAL_add_raw":
                    Util.Assert(funCall.Args.Count == 2);
                    return new RtlBinary("+", G(funCall.Args[0]), G(funCall.Args[1]));
                case "INTERNAL_sub_raw":
                    Util.Assert(funCall.Args.Count == 2);
                    return new RtlBinary("-", G(funCall.Args[0]), G(funCall.Args[1]));                
            }
            TypeApply app = dafnySpec.Compile_Function(funCall.Function,
                funCall.TypeArgumentSubstitutions.ToDictionary(p => p.Key, p => AppType(p.Value)));
            string name = FunName(SimpleName(app.AppName()));
            string fullName = FunName(SimpleName(app.AppFullName()));
            List<RtlExp> rtlArgs = funCall.Args.Select(G).ToList();
            List<RtlExp> rtlReads = funCall.Function.Reads.Where(e => e.Field != null).ToList()
                .ConvertAll(e => (RtlExp)new RtlVar(
                    GhostVar(e.FieldName), e.Field.IsGhost, AppType(e.Field.Type)));
            rtlArgs = rtlReads.Concat(rtlArgs).ToList();
            if (name.EndsWith("__INTERNAL__HEAP"))
            {
                name = name.Substring(0, name.Length - "__INTERNAL__HEAP".Length);
            }
            else if (DafnySpec.IsHeapFunction(funCall.Function))
            {
                rtlArgs.Insert(0, new RtlLiteral(inRequiresOrOld ? "$absMem_old" : "$absMem"));
            }
            if (Attributes.Contains(funCall.Function.Attributes, "opaque")
                && funCall.Function.Formals.Count + rtlReads.Count == 0)
            {
                rtlArgs.Insert(0, new RtlLiteral("true"));
            }
            if (fullName == recFunName)
            {
                name = fullName;
            }
            if (name == recFunName)
            {
                recCalls.Add(new List<RtlExp>(rtlArgs));
                rtlArgs.Insert(0, new RtlApply("decreases_" + name, new List<RtlExp>(rtlArgs)));
                rtlArgs.Insert(1, new RtlLiteral(inRecSpec ? "__unroll" : "__unroll + 1"));
                name = "rec_" + name;
            }
            return new RtlApply(name, rtlArgs);
        }
        else if (dataVal != null)
        {
            bool isSeq = dataVal.Type.TypeName(null).StartsWith("Seq<");
            return new RtlApply((isSeq ? "_" : "") + dafnySpec.Compile_Constructor(
                dataVal.Type, dataVal.Ctor.Name, dataVal.InferredTypeArgs, typeApply.typeArgs).AppName(),
                dataVal.Arguments.Select(G));
        }
        else if (existsExp != null || forallExp != null)
        {
            QuantifierExpr qExp = (QuantifierExpr)exp;
            bool isForall = forallExp != null;
            var varTuples = qExp.BoundVars.Select(v => Tuple.Create(GhostVar(v.Name), v.IsGhost, v.Type));
            var oldRenamer = PushRename(qExp.BoundVars.Select(v => v.Name));
            var oldStmtExprEnabled = stmtExprEnabled;
            stmtExprEnabled = false; 
            RtlExp rExp = new RtlLiteral((isForall ? "(forall " : "(exists ")
                + string.Join(", ", qExp.BoundVars.Select(v => GhostVar(v.Name) + ":" + TypeString(AppType(v.Type))))
                + " :: " + Triggers(qExp.Attributes, G) + " "
                + GetTypeWellFormedExp(varTuples.ToList(), isForall ? "==>" : "&&", G(qExp.Term)) + ")");
            stmtExprEnabled = oldStmtExprEnabled;
            PopRename(oldRenamer);
            return rExp;
        }
        else if (letExp != null)
        {
            List<RtlExp> rhss;
            if (letExp.Exact)
            {
                rhss = letExp.RHSs.ConvertAll(e => G(e));
            }
            else if (letExp.LHSs.Count == 1 && LiteralExpr.IsTrue(letExp.RHSs[0]) && AppType(letExp.LHSs[0].Var.Type) is IntType)
            {
                rhss = new List<RtlExp> { new RtlLiteral("0") };
            }
            else
            {
                throw new Exception("not implemented: LetExpr: " + letExp);
            }
            return GhostLet(exp.tok, letExp.LHSs.ConvertAll(lhs => lhs.Var), rhss, () => G(letExp.Body));
        }
        else if (matchExp != null)
        {
            if (matchExp.MissingCases.Count != 0)
            {
                throw new Exception("not implemented: MatchExpr with missing cases: " + matchExp);
            }
            //- match src case c1(ps1) => e1 ... cn(psn) => en
            //-   -->
            //- let x := src in
            //-   if x is c1 then let ps1 := ...x.f1... in e1 else
            //-   if x is c2 then let ps2 := ...x.f2... in e2 else
            //-                   let ps3 := ...x.f3... in e3
            var src = G(matchExp.Source);
            var cases = matchExp.Cases;
            string x = TempName();
            Func<RtlExp> body = null;
            for (int i = cases.Count; i > 0; )
            {
                i--;
                MatchCaseExpr c = cases[i];
                Func<List<RtlExp>> cRhss = () => c.Ctor.Formals.ConvertAll(f => (RtlExp)new RtlLiteral("("
                    + f.Name + "#" + c.Ctor.Name + "(" + GhostVar(x) + "))"));
                Func<RtlExp> ec = () => GhostLet(exp.tok, c.Arguments, cRhss(), () => G(c.Body));
                if (body == null)
                {
                    body = ec;
                }
                else
                {
                    var prevBody = body;
                    body = () => GhostIfThenElse(new RtlLiteral("(" + GhostVar(x) + " is " + c.Ctor.Name + ")"),
                        ec, prevBody);
                }
            }
            return GhostLet(exp.tok, new List<BoundVar> { new BoundVar(exp.tok, x, matchExp.Source.Type) },
                new List<RtlExp> { src }, body);
        }
        else if (oldExp != null)
        {
            return new RtlLiteral("old(" + GhostExpression(oldExp.E, inRecSpec, true) + ")");
        }        
        else if (memberSelect != null && memberSelect.MemberName.EndsWith("?"))
        {
          string constructor = memberSelect.MemberName.Substring(0, memberSelect.MemberName.Length - 1);
            constructor = dafnySpec.Compile_Constructor(memberSelect.Obj.Type, constructor, null, typeApply.typeArgs).AppName();
            bool isSeq = memberSelect.Obj.Type.TypeName(null).StartsWith("Seq<");
            return isSeq
                ? new RtlLiteral("is_" + constructor + "(" + G(memberSelect.Obj) + ")")
                : new RtlLiteral("((" + G(memberSelect.Obj) + ") is " + constructor + ")");
        } 
        else if (memberSelect != null && memberSelect.Member is Field && !memberSelect.Member.IsStatic && AppType(memberSelect.Obj.Type) is UserDefinedType
            && memberSelect.Member is DatatypeDestructor)
        {
            DatatypeDestructor field = (DatatypeDestructor) memberSelect.Member;
            string constructor = dafnySpec.Compile_Constructor(memberSelect.Obj.Type,
                field.EnclosingCtor.Name, null, typeApply.typeArgs).AppName();
            bool isSeq = memberSelect.Obj.Type.TypeName(null).StartsWith("Seq<");
            return new RtlLiteral("(" + memberSelect.MemberName + (isSeq ? "_" : "#") + constructor
                + "(" + G(memberSelect.Obj) + "))");
        }
        else if (memberSelect != null && memberSelect.Member is Field && DafnySpec.IsArrayType(AppType(memberSelect.Obj.Type))
            && memberSelect.MemberName == "Length")
        {
            return new RtlLiteral("(Arr_Length(" + G(memberSelect.Obj) + "))");
        } 
        else if (memberSelect != null && memberSelect.Member is Field && memberSelect.Obj is ImplicitThisExpr)
        {
            //- we don't support objects yet, so interpret this as a global variable
            return new RtlVar(GhostVar(memberSelect.MemberName), true, memberSelect.Type);
        }
        else if (seqSelect != null)
        {
            if (seqSelect.SelectOne && DafnySpec.IsArrayType(AppType(seqSelect.Seq.Type)))
            {
                return new RtlExpComputed(e => "fun_INTERNAL__array__elems__index("
                    + (inRequiresOrOld ? "$absMem_old" : "$absMem") + "[" + e.args[0] + ".arrAbs], ("
                    + e.args[1] + "))", new RtlExp[] { G(seqSelect.Seq), G(seqSelect.E0) });
            }
            else if (seqSelect.SelectOne)
            {
                return new RtlApply(dafnySpec.GetSeqOperationName(AppType(seqSelect.Seq.Type), "Seq_Index"),
                    new RtlExp[] { G(seqSelect.Seq), G(seqSelect.E0) });
            }
            else
            {
                RtlExp seq = G(seqSelect.Seq);
                if (DafnySpec.IsArrayType(AppType(seqSelect.Seq.Type)))
                {
                    seq = new RtlApply(FunName("Seq__FromArray"), new RtlExp[] {
                        new RtlLiteral(inRequiresOrOld ? "$absMem_old" : "$absMem"), seq });
                }
                if (seqSelect.E1 != null)
                {
                    seq = new RtlApply(dafnySpec.GetSeqOperationName(AppType(seqSelect.Type), "Seq_Take"),
                        new RtlExp[] { seq, G(seqSelect.E1) });
                }
                if (seqSelect.E0 != null)
                {
                    seq = new RtlApply(dafnySpec.GetSeqOperationName(AppType(seqSelect.Type), "Seq_Drop"),
                        new RtlExp[] { seq, G(seqSelect.E0) });
                }
                return seq;
            }
        }
        else if (seqUpdate != null)
        {
            if (seqUpdate.ResolvedUpdateExpr != null) {
                return GhostExpressionRec(seqUpdate.ResolvedUpdateExpr, inRecSpec, inRequiresOrOld); 
            } 
            return new RtlApply(dafnySpec.GetSeqOperationName(AppType(seqUpdate.Seq.Type), "Seq_Update"),
                new RtlExp[] { G(seqUpdate.Seq), G(seqUpdate.Index), G(seqUpdate.Value) });
        }
        else if (seqDisplay != null)
        {
            RtlExp seq = new RtlApply(dafnySpec.GetSeqOperationName(AppType(seqDisplay.Type), "Seq_Empty"), new RtlExp[0]);
            foreach (Expression ei in seqDisplay.Elements)
            {
                seq = new RtlApply(dafnySpec.GetSeqOperationName(AppType(seqDisplay.Type), "Seq_Build"),
                    new RtlExp[] { seq, G(ei) });
            }
            return seq;
        }
        else
        {
            throw new Exception("not implemented: " + exp);
        }
    }

    public RtlExp GhostExpression(Expression exp, bool inRecSpec = false, bool inRequiresOrOld = false,
        Attributes attrs = null)
    {
        Type oldDefault = StartTypeArg(attrs);
        var e = GhostExpressionRec(exp, inRecSpec, inRequiresOrOld);
        DafnySpec.defaultPolyType = oldDefault;
        return e;
    }

    public string DecreasesExp(ICallable target)
    {
        Util.Assert(!isPrinting);
        Expression decrease;
        if (target.Decreases.Expressions.Count == 0 && target.Ins.Count > 0)
        {
            decrease = DafnySpec.MakeIdentifierExpr(target.Ins[0].Name, target.Ins[0].Type,
                target.Ins[0].IsGhost);
        }
        else if (target.Decreases.Expressions.Count == 1)
        {
            decrease = target.Decreases.Expressions[0];
        }
        else if (target.Decreases.Expressions.Count > 1)
        {
            
            decrease = target.Decreases.Expressions[0];
            
        }
        else
        {
            throw new Exception("recursive methods must have at least one parameter or supply a decreases clause");
        }
        Type decreaseType = AppType(decrease.Type);
        if (decreaseType.AsDatatype != null)
        {
            return "sizeof##" + TypeString(decreaseType) + "(" + GhostExpression(decrease) + ")";
        }
        else if (decreaseType is SeqType)
        {
            return new RtlApply(dafnySpec.GetSeqOperationName(decreaseType, "Seq_Length"),
                new RtlExp[] { GhostExpression(decrease) }).ToString();
        }
        else if (decreaseType.Equals(Type.Int))
        {
            return GhostExpression(decrease).ToString();
        }
        else
        {
            throw new Exception("decreases clauses must be an integer or datatype");
        }
    }

    public void AddTypeWellFormed(List<RtlExp> specs, RtlExp exp, bool isGhost, Type t, List<UserDefinedType> recs)
    {
        UserDefinedType ut = t as UserDefinedType;
        if (minVerify && !isGhost && t is IntType)
        {
            specs.Add(new RtlApply("word", new RtlExp[] { exp }));
            return;
        }
        if (t is NatType)
        {
            specs.Add(new RtlBinary(">=", exp, new RtlInt(0)));
        }
        if (ut != null && ut.AsDatatype != null
            && recs.TrueForAll(r => ut.Name != r.Name) 
            )
        {
            recs.Add(ut);
            foreach (var ctor in ut.AsDatatype.Ctors)
            {
                List<RtlExp> cspecs = new List<RtlExp>();
                foreach (var f in ctor.Formals)
                {
                    AddTypeWellFormed(cspecs, new RtlLiteral(f.Name + "#" + ctor.Name + "(" + exp + ")"),
                        isGhost, f.Type, recs);
                }
                foreach (var spec in cspecs)
                {
                    specs.Add(new RtlLiteral("((" + exp + ") is " + ctor.Name + " ==> (" + spec + "))"));
                }
            }
            recs.RemoveAt(recs.Count - 1);
        }
    }

    public void AddTypeWellFormed(List<RtlExp> specs, string name, bool isGhost, Type t)
    {
        AddTypeWellFormed(specs, new RtlVar(name, isGhost, t), isGhost, t, new List<UserDefinedType>());
    }

    public void AddTypeWellFormed(List<RtlExp> specs, List<Formal> formals)
    {
        formals.ForEach(f => AddTypeWellFormed(specs, GhostVar(f.Name), f.IsGhost, f.Type));
    }

    public List<RtlExp> GetTypeWellFormed(List<Tuple<string,bool,Type>> vars)
    {
        List<RtlExp> exps = new List<RtlExp>();
        vars.ForEach(x => AddTypeWellFormed(exps, x.Item1, x.Item2, x.Item3));
        return exps;
    }

    public RtlExp GetTypeWellFormedExp(List<Tuple<string,bool,Type>> vars, string op, RtlExp rhs)
    {
        var exps = GetTypeWellFormed(vars);
        foreach(var e in exps)
        {
            rhs = new RtlBinary(op, e, rhs);
        }
        return rhs;
    }

    public void SymdiffLinearityPoint()
    {
        stmts.Add(new RtlAssert(new RtlLiteral("!false"))); 
    }

    public void AddGhostCall(List<RtlVar> destVars, string name, List<Expression> args, bool isHeap)
    {
        List<RtlExp> rtlArgs = args.ConvertAll(e => GhostExpression(e));
        name = GhostProcName(name);
        if (isHeap)
        {
            rtlArgs.Insert(0, new RtlLiteral("$absMem"));
        }
        if (name == procName)
        {
            isRecursive = true;
            rtlArgs.Insert(0, new RtlApply("decreases_" + name, new List<RtlExp>(rtlArgs)));
            name = "rec_" + name;
        }
        stmts.Add(new RtlGhostCall(name, destVars, rtlArgs)
            .WithComment("call:: " + String.Join(",", destVars) + " := " + name
                + "(" + String.Join(", ", rtlArgs.ToList()) + ")  // isGhost = " + true));
    }

    private void AddGhostCall(List<RtlVar> destVars, List<Expression> args, TypeApply typeApply, bool isHeap)
    {
        AddGhostCall(destVars, SimpleName(typeApply.AppName()), args, isHeap);
    }

    public void AddGhostVarDecl(string varName, Type t, bool isGhost)
    {
        string name = GhostVar(varName);
        if (allVars.ContainsKey(name) || forallVars.Exists(d => d.ContainsKey(name)))
        {
            AddRename(varName);
            name = GhostVar(varName);
        }
        var dict = (forallVars.Count == 0) ? allVars : forallVars[forallVars.Count - 1];
        dict.Add(name, new RtlVar(name, isGhost, AppType(t)));
    }

    public void MoveGhost(RtlVar destVar, RtlExp rhs)
    {
        stmts.Add(new RtlGhostMove(new RtlVar[] { destVar }, new RtlExp[] { rhs }));
    }

    public virtual void AddResolvedGhostStatement(Statement stmt, Attributes attrs)
    {
        BlockStmt block = stmt as BlockStmt;
        IfStmt ifStmt = stmt as IfStmt;
        AssertStmt assertStmt = stmt as AssertStmt;
        AssignStmt assignStmt = stmt as AssignStmt;
        CallStmt callStmt = stmt as CallStmt;
        VarDeclStmt varDecl = stmt as VarDeclStmt;
        CalcStmt calcStmt = stmt as CalcStmt;
        ForallStmt forallStmt = stmt as ForallStmt;
        AssignSuchThatStmt existsStmt = stmt as AssignSuchThatStmt;

        if (block != null)
        {
            var oldRenamer = PushRename();
            block.Body.ForEach(s => AddGhostStatement(s, attrs));
            PopRename(oldRenamer);
        }
        else if (varDecl != null)
        {
            foreach (var varLocal in varDecl.Locals) { 
                AddGhostVarDecl(varLocal.Name, varLocal.Type, varLocal.IsGhost);
            }

            if (varDecl.Update != null) {                
                Util.Assert(varDecl.Update is UpdateStmt || varDecl.Update is AssignSuchThatStmt);
                AddGhostStatement((Statement)varDecl.Update, attrs);
                //Util.Assert(varDecl.Update.Lhss.Count() == 1);
                //var destVar = AsVar(varDecl.Update.Lhss[0]);
                //Util.Assert(destVar != null);
                //ExprRhs expRhs = ((UpdateStmt)varDecl.Update).Rhss[0] as ExprRhs;
                //if (expRhs != null) { 
                //    stmts.Add(new RtlGhostMove(new RtlVar[] { destVar },
                //        new RtlExp[] { GhostExpression(expRhs.Expr) }));
                //} else {
                //    throw new Exception("not implemented: " + ((UpdateStmt)varDecl.Update).Rhss[0]);
                //}
            }
        }
        else if (minVerify)
        {
            return;
        }
        else if (assignStmt != null)
        {
            ExprRhs expRhs = assignStmt.Rhs as ExprRhs;
            if (expRhs != null)
            {
              MemberSelectExpr memberSelect = assignStmt.Lhs as MemberSelectExpr;
                RtlVar destVar;
                if (memberSelect != null && memberSelect.Member is Field)
                {
                    // assume that this is a global variable; we don't support objects yet
                    destVar = new RtlVar(GhostVar(memberSelect.MemberName), true, memberSelect.Type);
                }
                else
                {
                    destVar = AsVar(assignStmt.Lhs);
                    Util.Assert(destVar != null);
                }
                stmts.Add(new RtlGhostMove(new RtlVar[] { destVar },
                    new RtlExp[] { GhostExpression(expRhs.Expr) }));
            }
            else
            {
                throw new Exception("not implemented: " + assignStmt.Rhs);
            }
        }
        else if (callStmt != null)
        {
            var extraTypeargs = GetTypeArgs(attrs);
            var extraTypeargsDict = extraTypeargs.Select((t,index) => Tuple.Create(new TypeParameter(callStmt.Tok, "Fake" + index),t)).ToDictionary(tuple => tuple.Item1, tuple => tuple.Item2);
            var subst = callStmt.MethodSelect.TypeArgumentSubstitutions().Concat(extraTypeargsDict);

            AddGhostCall(callStmt.Lhs.ConvertAll(AsVar), callStmt.Args,
                dafnySpec.Compile_Method((Method)callStmt.MethodSelect.Member,
                    subst.ToDictionary(p => p.Key, p => AppType(p.Value)),
                    extraTypeargsDict.Keys.ToList()),
                DafnySpec.IsHeapMethod((Method)callStmt.MethodSelect.Member));
            SymdiffLinearityPoint();
        }
        else if (ifStmt != null)
        {
            stmts.Add(new RtlGhostStmtComputed(s => "if (" + s.args[0] + ") {",
                new RtlExp[] { GhostExpression(ifStmt.Guard) }));
            Indent();
            AddGhostStatement(ifStmt.Thn, attrs);
            Unindent();
            stmts.Add(new RtlGhostStmtComputed(s => "}", new RtlExp[0]));
            if (ifStmt.Els != null)
            {
                stmts.Add(new RtlGhostStmtComputed(s => "if (" + s.args[0] + ") {",
                    new RtlExp[] {
                        GhostExpression(new UnaryOpExpr(Bpl.Token.NoToken, UnaryOpExpr.Opcode.Not, ifStmt.Guard)) }));
                Indent();
                AddGhostStatement(ifStmt.Els, attrs);
                Unindent();
                stmts.Add(new RtlGhostStmtComputed(s => "}", new RtlExp[0]));
            }
        }
        else if (assertStmt != null)
        {
            stmts.Add(new RtlAssert(GhostExpression(assertStmt.Expr)));
        }
        else if (forallStmt != null)
        {
            var oldRenamer = PushRename(forallStmt.BoundVars.Select(v => v.Name));
            RtlExp ens = new RtlLiteral("true");
            foreach (var e in forallStmt.Ens)
            {
                ens = new RtlBinary("&&", ens, GhostExpression(e.E));
            }
            RtlExp range = (forallStmt.Range == null) ? new RtlLiteral("true")
                : GhostExpression(forallStmt.Range);
            List<RtlExp> wellFormed = GetTypeWellFormed(forallStmt.BoundVars.
                Select(x => Tuple.Create(GhostVar(x.Name), x.IsGhost, x.Type)).ToList());
            wellFormed.ForEach(e => range = new RtlBinary("&&", e, range));
            ens = new RtlBinary("==>", range, ens);
            string vars = String.Join(", ", forallStmt.BoundVars.Select(x => GhostVar(x.Name) + ":" +
                TypeString(AppType(x.Type))));
            stmts.Add(new RtlGhostStmtComputed(s => "forall " + vars + "::(" + s.args[0] + ")",
                new List<RtlExp> { ens }));
            stmts.Add(new RtlGhostStmtComputed(s => "{", new RtlExp[0]));
            Indent();
            stmts.Add(PushForall());
            stmts.Add(new RtlGhostStmtComputed(s => "if (" + s.args[0] + ")",
                new List<RtlExp> { range }));
            stmts.Add(new RtlGhostStmtComputed(s => "{", new RtlExp[0]));
            Indent();
            AddGhostStatement(forallStmt.Body, attrs);
            foreach (var e in forallStmt.Ens)
            {
                stmts.Add(new RtlAssert(GhostExpression(e.E)));
            }
            PopForall();
            Unindent();
            stmts.Add(new RtlGhostStmtComputed(s => "}", new RtlExp[0]));
            Unindent();
            stmts.Add(new RtlGhostStmtComputed(s => "}", new RtlExp[0]));
            PopRename(oldRenamer);
        }
        else if (existsStmt != null)
        {
            List<RtlStmt> assigns = new List<RtlStmt>();
            List<RtlVar> tmps = new List<RtlVar>();
            List<Tuple<string,bool,Type>> varTuples = new List<Tuple<string,bool,Type>>();
            var oldRenamer = PushRename();
            foreach (var lhs in existsStmt.Lhss)
            {
                IdentifierExpr idExp = lhs.Resolved as IdentifierExpr;
                RtlVar origVar = AsVar(lhs);
                AddRename(idExp.Name);
                RtlVar renameVar = AsVar(lhs);
                tmps.Add(renameVar);
                varTuples.Add(Tuple.Create(renameVar.ToString(), true, idExp.Type));
                assigns.Add(new RtlGhostMove(new RtlVar[] { origVar },
                    new RtlExp[] { renameVar }));
            }
            string vars = String.Join(", ", tmps.Select(x => x.getName() + ":" + TypeString(AppType(x.type))));
            stmts.Add(new RtlGhostStmtComputed(s => "exists " + vars + "::(" + s.args[0] + ");",
                new List<RtlExp> {
                    GetTypeWellFormedExp(varTuples.ToList(), "&&", GhostExpression(existsStmt.Expr)) }));
            stmts.AddRange(assigns);
            PopRename(oldRenamer);
        }
        else if (calcStmt != null)
        {
            Util.Assert(calcStmt.Steps.Count == calcStmt.Hints.Count);
            CalcStmt.BinaryCalcOp binOp = calcStmt.Op as CalcStmt.BinaryCalcOp;
            bool isImply = binOp != null && binOp.Op == BinaryExpr.Opcode.Imp && calcStmt.Steps.Count > 0;
            if (isImply)
            {
                stmts.Add(new RtlGhostStmtComputed(s => "if (" + s.args[0] + ")",
                    new RtlExp[] { GhostExpression(CalcStmt.Lhs(calcStmt.Steps[0])) }));
                stmts.Add(new RtlGhostStmtComputed(s => "{", new RtlExp[0]));
                Indent();
            }
            var stepCount = calcStmt.Hints.Last().Body.Count == 0 ? calcStmt.Steps.Count - 1 : calcStmt.Steps.Count;
            for (int i = 0; i < stepCount; i++)
            {
                if (calcStmt.Hints[i] == null)
                {
                    stmts.Add(new RtlAssert(GhostExpression(calcStmt.Steps[i])));
                }
                else
                {
                    stmts.Add(new RtlGhostStmtComputed(s => "forall::(" + s.args[0] + ")",
                        new List<RtlExp> { GhostExpression(calcStmt.Steps[i]) }));
                    stmts.Add(new RtlGhostStmtComputed(s => "{", new RtlExp[0]));
                    Indent();
                    var dict = new Dictionary<string,RtlVar>();
                    stmts.Add(new RtlGhostStmtComputed(s => String.Concat(dict.Values.Select(
                        x => "var " + x.x + ":" + TypeString(x.type) + ";")),
                        new RtlExp[0]));
                    forallVars.Add(dict);
                    AddGhostStatement(calcStmt.Hints[i], attrs);
                    forallVars.RemoveAt(forallVars.Count - 1);
                    Unindent();
                    stmts.Add(new RtlGhostStmtComputed(s => "}", new RtlExp[0]));
                }
            }
            if (isImply)
            {
                Unindent();
                stmts.Add(new RtlGhostStmtComputed(s => "}", new RtlExp[0]));
            }
        }
        else
        {
            throw new Exception("not implemented in ghost methods: " + stmt);
        }
    }

    public List<Statement> ResolveStmt(Statement s)
    {
        /*
        ConcreteSyntaxStatement concrete = s as ConcreteSyntaxStatement;
        if (concrete != null && concrete.ResolvedStatements != null)
        {
            return concrete.ResolvedStatements;
        }
         */
        UpdateStmt update = s as UpdateStmt;
        if (update != null && update.ResolvedStatements != null)
        {
            return update.ResolvedStatements;
        }
        return null;
    }

    public List<Type> GetTypeArgs(Attributes attrs)
    { 
        var args = Attributes.FindExpressions(attrs, "typearg");
        var types = new List<Type>();
        foreach (var arg in args ?? new List<Expression>()) 
        {            
            string s = (string)(((StringLiteralExpr)arg).Value);
            switch (s)
            {
                case "int":  types.Add(Type.Int) ; break;
                case "bool": types.Add(Type.Bool); break;
                case "real": types.Add(Type.Real); break;
                default:
                    if (typeApply.typeSubsts.ContainsKey(s))
                    {
                        types.Add(typeApply.typeSubsts[s]);
                    }
                    else
                    {
                        throw new Exception("not implemented: StartTypeArg: " + s);
                    }
                    break;
            }
            
        }
        return types;
    }

    public Type StartTypeArg(Attributes attrs)
    {
        Type prev = DafnySpec.defaultPolyType;
        
        for (var a = attrs; a != null; a = a.Prev)
        {
            if (a.Name == "typearg")
            {
                string s = (string)(((StringLiteralExpr)a.Args[0]).Value);
                switch (s)
                {
                    case "int": DafnySpec.defaultPolyType = Type.Int; break;
                    case "bool": DafnySpec.defaultPolyType = Type.Bool; break;
                    case "real": DafnySpec.defaultPolyType = Type.Real; break;
                    default:
                        if (typeApply.typeSubsts.ContainsKey(s))
                        {
                            DafnySpec.defaultPolyType = typeApply.typeSubsts[s];
                        }
                        else
                        {
                            throw new Exception("not implemented: StartTypeArg: " + s);
                        }
                        break;
                }
                break;
            }
        }
        return prev;
    }

    public void AddGhostStatement(Statement stmt, Attributes attribs)
    {
        Util.Assert(!isPrinting);
        stmts.Add(new RtlComment("###LINE: " + stmt.Tok.filename + ": " + stmt.Tok.line));
        List<Statement> resolved = ResolveStmt(stmt);
        if (resolved != null)
        {
            UpdateStmt u = stmt as UpdateStmt;
            if (u != null)
            {
                Type oldDefault = StartTypeArg(u.Rhss[0].Attributes);
                resolved.ForEach(s => AddGhostStatement(s, u.Rhss[0].Attributes));
                DafnySpec.defaultPolyType = oldDefault;
            }
            else
            {
                resolved.ForEach(s => AddGhostStatement(s, attribs));
            }
        }
        else
        {
            AddResolvedGhostStatement(stmt, attribs);
        }
    }
}

