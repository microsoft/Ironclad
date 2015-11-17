using System;
using System.IO;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Boogie
{

public interface IToken
{
    string filename { get; }
    int line { get; }
}

public class Token: IToken
{
    public static Token NoToken = new Token("nofile", 0);

    string _filename;
    int _line;

    public Token(string filename, int line) { this._filename = filename; this._line = line; }

    public string filename { get { return _filename; } }
    public int line { get { return _line; } }
}

}

namespace Microsoft.Basetypes
{
    public class BigDec
    {
        string s;
        internal BigDec(string s) { this.s = s; }
        public static BigDec FromString(string s) { return new BigDec(s); }
        public override string ToString() { return s; }
        public string ToDecimalString() { return s; }
    }
}

namespace Microsoft.Dafny
{
using Token = Bpl.Token;

public class Attributes
{
    public string Name;
    public List<Expression> Args;
    public Attributes Prev;

    public Attributes(string Name, List<Expression> Args, Attributes Prev) { this.Name = Name; this.Args = Args; this.Prev = Prev; }

    public static void Resolve(Resolver resolver, Attributes attrs)
    {
        if (attrs != null)
        {
            for (int i = 0; i < attrs.Args.Count; i++) {
                attrs.Args[i] = attrs.Args[i].Resolve(resolver, null);
            }            
            Resolve(resolver, attrs.Prev);
        }
    }

    public static bool Contains(Attributes attrs, string name)
    {
        return attrs != null && (attrs.Name == name || Contains(attrs.Prev, name));
    }

    public static List<Expression> FindExpressions(Attributes attrs, string nm) 
    {
        for (; attrs != null; attrs = attrs.Prev) {
            if (attrs.Name == nm) {
                return attrs.Args;
            }
        }
        return null;
    }
}

public abstract class Type
{
    public static IntType Int = new IntType();
    public static NatType Nat = new NatType();
    public static RealType Real = new RealType();
    public static BoolType Bool = new BoolType();

    public enum NumericPersuation { Int, Real }

    public bool IsNumericBased(NumericPersuation p) {
        return (this is IntType && p == NumericPersuation.Int)
            || (this is RealType && p == NumericPersuation.Real);
    }

    public abstract string TypeName(object o);
    public virtual DatatypeDecl AsDatatype { get { return null; } }

    public override abstract bool Equals(Object o);
    public override int GetHashCode() { return 0; }
    public abstract Type Subst(Dictionary<TypeParameter,Type> map);
    public virtual void Resolve(Resolver resolver) {}
}

public class TypeParameter
{
    public string Name;

    public TypeParameter(string Name) { this.Name = Name; }
    public TypeParameter(Token tok, string Name) { this.Name = Name; }

    public override bool Equals(object other)
    {
        TypeParameter that = other as TypeParameter;
        return that != null && that.Name == this.Name;
    }

    public override int GetHashCode() { return Name.GetHashCode(); }
}

public class TypeProxy: Type
{
    public Type T;

    public TypeProxy(Type T) { this.T = T; }

    public override bool Equals(Object o) { return T.Equals(o); }
    public override int GetHashCode() { return T.GetHashCode(); }
    public override string TypeName(object o) { return T.TypeName(o); }
    public override Type Subst(Dictionary<TypeParameter,Type> map) { return new TypeProxy(T.Subst(map)); }
}

public class IntType: Type
{
    public override bool Equals(Object o) { return o is IntType && !(o is NatType); }
    public override int GetHashCode() { return 0; }
    public override string TypeName(object o) { return "int"; }
    public override Type Subst(Dictionary<TypeParameter,Type> map) { return this; }
}

public class NatType: IntType
{
    public override bool Equals(Object o) { return o is NatType; }
    public override int GetHashCode() { return 0; }
    public override string TypeName(object o) { return "nat"; }
    public override Type Subst(Dictionary<TypeParameter,Type> map) { return this; }
}

public class RealType: Type
{
    public override bool Equals(Object o) { return o is RealType; }
    public override int GetHashCode() { return 0; }
    public override string TypeName(object o) { return "real"; }
    public override Type Subst(Dictionary<TypeParameter,Type> map) { return this; }
}

public class BoolType: Type
{
    public override bool Equals(Object o) { return o is BoolType; }
    public override int GetHashCode() { return 0; }
    public override string TypeName(object o) { return "bool"; }
    public override Type Subst(Dictionary<TypeParameter,Type> map) { return this; }
}

public class SeqType: Type
{
    public Type Arg;

    public SeqType(Type Arg) { this.Arg = Arg; }

    public override bool Equals(Object o) { SeqType that = o as SeqType; return that != null && Arg.Equals(that.Arg); }
    public override int GetHashCode() { return Arg.GetHashCode(); }
    public override string TypeName(object o) { return "seq<" + Arg.TypeName(o) + ">"; }
    public override Type Subst(Dictionary<TypeParameter,Type> map) { return new SeqType(Arg.Subst(map)); }
    public override void Resolve(Resolver resolver) { Arg.Resolve(resolver); }
}

public class MapType: Type
{
    public Type Domain;
    public Type Range;

    public MapType(Type Domain, Type Range) { this.Domain = Domain; this.Range = Range; }

    public override bool Equals(Object o) { MapType that = o as MapType; return that != null && Domain.Equals(that.Domain) && Range.Equals(that.Range); }
    public override int GetHashCode() { return Range.GetHashCode(); }
    public override string TypeName(object o) { return "map<" + Domain.TypeName(o) + "," + Range.TypeName(o) + ">"; }
    public override Type Subst(Dictionary<TypeParameter,Type> map) { return new MapType(Domain.Subst(map), Range.Subst(map)); }
    public override void Resolve(Resolver resolver) { Domain.Resolve(resolver); Range.Resolve(resolver); }
}

public class UserDefinedType: Type
{
    DatatypeDecl datatype;
    public string Name;
    public Attributes Attributes;
    public List<Type> TypeArgs;
    public bool IsTypeParameter;

    public UserDefinedType(Token tok, string name, DatatypeDecl decl, List<Type> typeArgs,
        bool IsTypeParameter, Attributes Attributes)
    {
        this.datatype = decl;
        this.Name = name;
        this.Attributes = Attributes;
        this.TypeArgs = typeArgs;
        this.IsTypeParameter = IsTypeParameter;
    }

    public UserDefinedType(Token tok, string name, DatatypeDecl decl, List<Type> typeArgs)
        :this(tok, name, decl, typeArgs, false, null)
    {
    }

    internal UserDefinedType(string name)
        :this(Token.NoToken, name, null, null, true, null)
    {
    }

    public override string TypeName(object o)
    {
        if (TypeArgs == null) { return Name; }
        string[] args = new string[TypeArgs.Count];
        for (int i = 0; i < args.Length; i++) args[i] = TypeArgs[i].TypeName(o);
        return Name + "<" + String.Join(",", args) + ">";
    }

    public override DatatypeDecl AsDatatype { get { return datatype; } }

    public override bool Equals(Object o)
    {
        UserDefinedType that = o as UserDefinedType;
        if (that == null || Name != that.Name || IsTypeParameter != that.IsTypeParameter || TypeArgs.Count != that.TypeArgs.Count) { return false; }
        for (int i = 0; i < TypeArgs.Count; i++) { if (!TypeArgs[i].Equals(that.TypeArgs[i])) { return false; } }
        return true;
    }

    public override int GetHashCode() { return Name.GetHashCode(); }

    public override Type Subst(Dictionary<TypeParameter,Type> map)
    {
        if (IsTypeParameter && map.ContainsKey(new TypeParameter(Name)))
        {
            return map[new TypeParameter(Name)];
        }
        else
        {
            List<Type> typeArgs = new List<Type>();
            foreach (Type t in TypeArgs) { typeArgs.Add(t.Subst(map)); }
            return new UserDefinedType(Token.NoToken, Name, datatype, typeArgs, IsTypeParameter, Attributes);
        }
    }

    public override void Resolve(Resolver resolver)
    {
        if (resolver.typeParams.ContainsKey(Name))
        {
            IsTypeParameter = true;
        }
        else
        {
            datatype = resolver.Find(resolver.datatypes, Name);
        }
        if (TypeArgs != null)
        {
            foreach (Type arg in TypeArgs) { arg.Resolve(resolver); }
        }
    }
}

public class BoundVar
{
    public string Name;
    public Type Type;
    public bool IsGhost;

    public BoundVar(Token tok, string name, Type Type)
    {
        this.Name = name;
        this.Type = Type;
    }

    public void Resolve(Resolver resolver, Type t)
    {
        if (this.Type == null) { this.Type = t; }
        Type.Resolve(resolver);
        this.IsGhost = resolver.IsGhost();
    }
}

public class Formal
{
    public string Name;
    public Type Type;
    public bool IsGhost;

    public Formal(string name, Type type, bool IsGhost) { this.Name = name; this.Type = type; this.IsGhost = IsGhost; }

    public Formal(Token tok, string name, Type type, bool b1, bool b2)
    {
        if (b1 != b2) { throw new Exception("internal error"); }
        this.Name = name;
        this.Type = type;
        this.IsGhost = b1;
    }

    public void Resolve(Resolver resolver)
    {
        Type.Resolve(resolver);
        IsGhost = IsGhost || resolver.IsGhost();
    }
}

public class Expression
{
    public Token tok = Token.NoToken;
    public Type Type;
    public Expression Resolved;

    public bool WasResolved() { return false; }
    public virtual Expression Resolve(Resolver resolver, Type t) { Type = (Type == null) ? t : Type; return this; }
}

public class IdentifierExpr: Expression
{
    public string Name;
    public LocalVariable Var;

    public IdentifierExpr(Token tok, string name)
    {
        this.Name = name;
    }

    public override Expression Resolve(Resolver resolver, Type t)
    {
        VarDecl VarDecl = resolver.Var(Name);
                        
        if (VarDecl == null)
        {
            if (resolver.fields.ContainsKey(Name))
            {
                MemberSelectExpr ret = new MemberSelectExpr(new ImplicitThisExpr(), Name);
                ret.Member = resolver.fields[Name];
                ret.Type = resolver.fields[Name].Type;
                return ret;
            }
            else if (resolver.constructors.ContainsKey(Name))
            {
                DatatypeCtor ctor = resolver.constructors[Name];
                DatatypeValue ret = new DatatypeValue(new List<Type>(), ctor, new List<Expression>(),
                    new UserDefinedType(Token.NoToken, ctor.datatype.Name, ctor.datatype, new List<Type>()));
                return ret;
            }
            else
            {
                throw new Exception("cannot find variable/field/constructor named " + Name);
            }
        }
        else
        {
            Var = new LocalVariable(tok, tok, Name, VarDecl.Type, VarDecl.IsGhost);
            resolver.CollectVar(Name);
        }
        Type = Var.Type;
        return this;
    }
}

public class ThisExpr: Expression
{
}

public class ImplicitThisExpr: Expression
{
    public ImplicitThisExpr() { this.Type = Type.Bool; } // HACK
}

public class ParensExpression: Expression
{
    public Expression E;
    private ParensExpression() {} // never created
}

public abstract class StmtExpr: Expression
{
    public abstract Statement S { get; }
    public Expression E;
}

public class StmtExprCall: StmtExpr
{
    string Name;
    List<Expression> Args;
    CallStmt call;
    public override Statement S { get { return call; } }

    public StmtExprCall(string Name, List<Expression> Args, Expression E) { this.Name = Name; this.Args = Args; this.E = E; }

    public override Expression Resolve(Resolver resolver, Type t)
    {
        Method method = resolver.Find(resolver.methods, Name);
        for (int i = 0; i < Args.Count; i++) { Args[i] = Args[i].Resolve(resolver, method.Formals[i].Type); }
        call = new CallStmt(Args, new Dictionary<TypeParameter,Type>(), method);
        E = E.Resolve(resolver, t);
        Type = E.Type;
        return this;
    }
}

public delegate LiteralExpr MakeBigInt(string i);

public class LiteralExpr: Expression
{
    public object Value;

    public LiteralExpr(object Value) { this.Value = Value; }

    public override Expression Resolve(Resolver resolver, Type t)
    {
        Type =
            Value is bool ? (Type)Type.Bool :
            Value is Microsoft.Basetypes.BigDec ? (Type)Type.Real :
            (Type)Type.Int;
        return this;
    }

    public static bool IsTrue(Expression e)
    {
        LiteralExpr lit = e as LiteralExpr;
        return lit != null && lit.Value is bool && ((bool)lit.Value);
    }

    public static MakeBigInt MakeBigInt;
}

public class StringLiteralExpr : LiteralExpr
{
    public StringLiteralExpr(string s) : base(s) {}
}


public class UnaryExpr: Expression
{
}

public class UnaryOpExpr: UnaryExpr
{
    public enum Opcode { Not, Cardinality, Fresh }

    public Opcode Op;
    public Expression E;

    public UnaryOpExpr(Token tok, Opcode op, Expression e)
    {
        this.Op = op;
        this.E = e;
    }

    public override Expression Resolve(Resolver resolver, Type t)
    {
        switch (Op)
        {
            case Opcode.Not: E = E.Resolve(resolver, Type.Bool); Type = Type.Bool; break;
            case Opcode.Cardinality: E = E.Resolve(resolver, null); Type = Type.Int; break;
            case Opcode.Fresh: E = E.Resolve(resolver, Type.Bool); Type = Type.Bool; break;
        }

        return this;
    }
}

public class ConversionExpr : UnaryExpr
{
    public Type ToType;
    public Expression E;

    public ConversionExpr(Type ToType, Expression Input)
    {
        this.ToType = ToType;
        this.E = Input;
    }

    public override Expression Resolve(Resolver resolver, Type t)
    {
        this.Type = ToType;
        this.E = this.E.Resolve(resolver, t);
        return this;
    }
}

public class BinaryExpr: Expression
{
    public enum Opcode {
        None,
        Iff, Imp, Exp, And, Or, In, NotIn, Disjoint,
        Eq, Neq, Le, Lt, Ge, Gt,
        Add, Sub, Mul, Div, Mod,
    }
    public enum ResolvedOpcode { None, SeqEq, SeqNeq, Concat }

    public Opcode Op = Opcode.None;
    public ResolvedOpcode ResolvedOp = ResolvedOpcode.None;
    public Expression E0;
    public Expression E1;

    public BinaryExpr(Token tok, Opcode op, Expression e0, Expression e1)
    {
        this.Op = op;
        this.E0 = e0;
        this.E1 = e1;
    }

    public override Expression Resolve(Resolver resolver, Type t)
    {
        Type t0 = null;
        Type t1 = null;
        switch (Op)
        {
            case Opcode.Iff: case Opcode.Imp: case Opcode.Exp: case Opcode.And: case Opcode.Or:
                t0 = Type.Bool;
                t1 = Type.Bool;
                Type = Type.Bool;
                break;
            case Opcode.Eq: case Opcode.Neq: Type = Type.Bool; break;
            case Opcode.Le: case Opcode.Lt: case Opcode.Ge: case Opcode.Gt:
                t0 = Type.Int;
                t1 = Type.Int;
                Type = Type.Bool;
                break;
            case Opcode.Sub: case Opcode.Mul: case Opcode.Div: case Opcode.Mod:
                t0 = Type.Int;
                t1 = Type.Int;
                Type = Type.Int;
                break;
        }
        switch (Op)
        {
            case Opcode.Eq: case Opcode.Neq: case Opcode.Le: case Opcode.Lt: case Opcode.Ge: case Opcode.Gt:
                //- ((a < b) < c) < d
                //- -->
                //- ((a < b) < c) && c < d
                BinaryExpr B0 = E0 as BinaryExpr;
                if (B0 != null)
                {
                    switch (B0.Op)
                    {
                        case Opcode.Eq: case Opcode.Neq: case Opcode.Le: case Opcode.Lt: case Opcode.Ge: case Opcode.Gt:
                            Expression _e0 = B0;
                            Expression _e1 = new BinaryExpr(tok, Op, B0.E1, E1);
                            Expression _e = new BinaryExpr(tok, Opcode.And, _e0, _e1);
                            return _e.Resolve(resolver, Type.Bool);
                    }
                }
                break;
        }
        E0 = E0.Resolve(resolver, t0);
        E1 = E1.Resolve(resolver, t1);
        if (E0.Type == null) { E0 = E0.Resolve(resolver, E1.Type); } // HACK
        if (E1.Type == null) { E1 = E1.Resolve(resolver, E0.Type); } // HACK
        switch (Op)
        {
            case Opcode.Add:
                if (E0.Type is SeqType) { ResolvedOp = ResolvedOpcode.Concat; Type = E0.Type; }
                else if (E0.Type is RealType) { Type = E0.Type; }
                else { Type = Type.Int; }
                break;
            case Opcode.Sub: case Opcode.Mul: case Opcode.Div:
                if (E0.Type is RealType) { Type = E0.Type; }
                break;
            case Opcode.Eq: if (E0.Type is SeqType) { ResolvedOp = ResolvedOpcode.SeqEq; } break;
            case Opcode.Neq: if (E0.Type is SeqType) { ResolvedOp = ResolvedOpcode.SeqNeq; } break;
        }
        return this;
    }

    public static string OpcodeString(Opcode Op)
    {
        switch (Op)
        {
            case Opcode.Iff: return "<==>";
            case Opcode.Imp: return "==>";
            case Opcode.Exp: return "<==";
            case Opcode.And: return "&&";
            case Opcode.Or: return "||";
            case Opcode.In: return null;
            case Opcode.NotIn: return null;
            case Opcode.Disjoint: return null;
            case Opcode.Eq: return "==";
            case Opcode.Neq: return "!=";
            case Opcode.Le: return "<=";
            case Opcode.Lt: return "<";
            case Opcode.Ge: return ">=";
            case Opcode.Gt: return ">";
            case Opcode.Add: return "+";
            case Opcode.Sub: return "-";
            case Opcode.Mul: return "*";
            case Opcode.Div: return "/";
            case Opcode.Mod: return "%";
        }
        return null;
    }
}

public class ITEExpr: Expression
{
    public Expression Test;
    public Expression Thn;
    public Expression Els;

    public ITEExpr(Expression Test, Expression Thn, Expression Els) { this.Test = Test; this.Thn = Thn; this.Els = Els; }

    public override Expression Resolve(Resolver resolver, Type t)
    {
        Test = Test.Resolve(resolver, Type.Bool);
        Thn = Thn.Resolve(resolver, t);
        Els = Els.Resolve(resolver, t);
        if (Thn.Type == null) { Thn = Thn.Resolve(resolver, Els.Type); } // HACK
        if (Els.Type == null) { Els = Els.Resolve(resolver, Thn.Type); } // HACK
        Type = Thn.Type;
        return this;
    }
}

public abstract class QuantifierExpr: Expression
{
    public List<BoundVar> BoundVars;
    public Attributes Attributes;
    public Expression Term;

    public QuantifierExpr(List<BoundVar> BoundVars, Attributes Attributes, Expression Term)
    {
        this.BoundVars = BoundVars;
        this.Attributes = Attributes;
        this.Term = Term;
    }

    public override Expression Resolve(Resolver resolver, Type t)
    {
        foreach (BoundVar x in BoundVars)
        {
            //- "Infer" missing types as int.  If we're wrong, type checking will fail and the
            //- programmer will have to supply an explicit type.  
            // TODO: should we implement real type inference?
            Type tx = (x.Type != null) ? x.Type : Type.Int;
            x.Resolve(resolver, tx);
            resolver.PushVar(x);
        }
        Attributes.Resolve(resolver, Attributes);
        Term = Term.Resolve(resolver, Type.Bool);
        foreach (BoundVar x in BoundVars) { resolver.PopVar(x.Name); }
        Type = Type.Bool;
        return this;
    }
}

public class ExistsExpr: QuantifierExpr
{
    public ExistsExpr(List<BoundVar> BoundVars, Attributes Attributes, Expression Term): base(BoundVars, Attributes, Term) {}
}

public class ForallExpr: QuantifierExpr
{
    public ForallExpr(List<BoundVar> BoundVars, Attributes Attributes, Expression Term): base(BoundVars, Attributes, Term) {}
}

public class Lhs
{
}

public class LetExpr: Expression
{
    public bool tryToEliminate;
    public bool Exact;
    public List<ExprLhs> LHSs;
    public List<Expression> RHSs;
    public Expression Body;

    public LetExpr(bool Exact, List<ExprLhs> LHSs, List<Expression> RHSs, Expression Body)
    {
        this.Exact = Exact;
        this.LHSs = LHSs;
        this.RHSs = RHSs;
        this.Body = Body;
    }

    public override Expression Resolve(Resolver resolver, Type t)
    {
        resolver.PushVarCollect();
        for (int i = 0; i < RHSs.Count; i++)
        {
            RHSs[i] = RHSs[i].Resolve(resolver, LHSs[i].Var.Type);
            LHSs[i].Var.Resolve(resolver, RHSs[i].Type);
            resolver.PushVar(LHSs[i].Var);
        }
        Body = Body.Resolve(resolver, t);
        for (int i = 0; i < RHSs.Count; i++)
        {
            resolver.PopVar(LHSs[i].Var.Name);
        }
        Type = Body.Type;
        Dictionary<string,bool> neededVars = resolver.PopVarCollect();
        bool needed = false;
        foreach (ExprLhs lhs in LHSs)
        {
            if (neededVars.ContainsKey(lhs.Var.Name)) { needed = true; }
        }
        if (tryToEliminate && !needed) { return Body; }
        return this;
    }
}

public class MatchCaseExpr
{
    public string name;
    public DatatypeCtor Ctor;
    public List<BoundVar> Arguments;
    public Expression Body;

    public MatchCaseExpr(string name, List<BoundVar> Arguments, Expression Body) { this.name = name; this.Arguments = Arguments; this.Body = Body; }

    public void Resolve(Resolver resolver, DatatypeDecl data, Type t)
    {
        foreach (DatatypeCtor ctor in data.Ctors)
        {
            if (ctor.Name == name)
            {
                Ctor = ctor;
                for (int i = 0; i < Arguments.Count; i++)
                {
                    Arguments[i].Resolve(resolver, ctor.Formals[i].Type);
                    resolver.PushVar(Arguments[i]);
                }
                Body = Body.Resolve(resolver, t);
                for (int i = 0; i < Arguments.Count; i++) { resolver.PopVar(Arguments[i].Name); }
            }
        }
    }
}

public class MatchExpr: Expression
{
    public Expression Source;
    public List<MatchCaseExpr> Cases;
    public List<object> MissingCases;

    public MatchExpr(Expression Source, List<MatchCaseExpr> Cases) { this.Source = Source; this.Cases = Cases; this.MissingCases = new List<object>(); }

    public override Expression Resolve(Resolver resolver, Type t)
    {
        Type = t;
        Source = Source.Resolve(resolver, null);
        DatatypeDecl data = resolver.Find(resolver.datatypes, Source.Type.AsDatatype.Name);
        foreach (MatchCaseExpr c in Cases) { c.Resolve(resolver, data, t); t = c.Body.Type; Type = t; }
        return this;
    }
}

public class OldExpr: Expression
{
    public Expression E;

    public OldExpr(Expression E) { this.E = E; }
    public override Expression Resolve(Resolver resolver, Type t) { E = E.Resolve(resolver, t); Type = E.Type; return this; }
}

public class FunctionCallExpr: Expression
{
    public string name;
    public List<Type> typeArgs;
    public Function Function;
    public Dictionary<TypeParameter,Type> TypeArgumentSubstitutions;
    public List<Expression> Args;

    public FunctionCallExpr(string name, List<Type> typeArgs, List<Expression> Args)
    {
        this.name = name;
        this.typeArgs = typeArgs;
        this.Args = Args;
    }

    public override Expression Resolve(Resolver resolver, Type t)
    {
        List<TypeParameter> typeParams = null;
        List<Formal> formals = null;
        Expression ret = this;
        List<TypeParameter> parentParams =
            (resolver.currentFunction != null) ? resolver.currentFunction.TypeArgs :
            (resolver.currentMethod != null) ? resolver.currentMethod.TypeArgs :
            null;
        if (parentParams != null)
        {
            typeArgs = new List<Type>();
            foreach (TypeParameter p in parentParams) { typeArgs.Add(new UserDefinedType(p.Name)); } // HACK
        }
        if (resolver.functions.ContainsKey(name))
        {
            Function = resolver.functions[name];
            if (Function == resolver.currentFunction) { Function.IsRecursive = true; } // TODO: mutual recursion
            typeParams = Function.TypeArgs;
            formals = Function.Formals;
            Type = Function.ResultType;
        }
        else if (resolver.constructors.ContainsKey(name))
        {
            DatatypeCtor ctor = resolver.constructors[name];
            DatatypeDecl data = ctor.datatype;
            typeParams = data.TypeArgs;
            formals = ctor.Formals;
            Type = new UserDefinedType(Token.NoToken, data.Name, data, typeArgs);
            ret = new DatatypeValue(typeArgs, ctor, Args, Type);
        }
        else if (name == "IntToReal")
        {
            Function = new Function(name);
            formals = new List<Formal>(new Formal[] { new Formal("x", Type.Int, true) });
            Type = Type.Real;
        }
        else if (name == "RealToInt")
        {
            Function = new Function(name);
            formals = new List<Formal>(new Formal[] { new Formal("x", Type.Real, true) });
            Type = Type.Int;
        }
        else
        {
            throw new Exception("function not found: " + name);
        }
        // HACK: since Dafny has no syntax for explicit function type arguments, and we have no type inference, use heuristic for typeArgs:
        TypeArgumentSubstitutions = new Dictionary<TypeParameter,Type>();
        for (int i = 0; i < typeArgs.Count; i++)
        {
            TypeArgumentSubstitutions.Add(typeParams[i], typeArgs[i]);
            typeArgs[i].Resolve(resolver);
        }
        //foreach (Formal f in formals) { f.Resolve(resolver); }
        for (int i = 0; i < Args.Count; i++)
        {
            Args[i] = Args[i].Resolve(resolver, formals[i].Type);
        }
        return ret;
    }
}

public class DatatypeValue: Expression
{
    public List<Type> InferredTypeArgs;
    public DatatypeCtor Ctor;
    public List<Expression> Arguments;

    public DatatypeValue(List<Type> InferredTypeArgs, DatatypeCtor Ctor, List<Expression> Arguments, Type t)
    {
        this.InferredTypeArgs = InferredTypeArgs;
        this.Ctor = Ctor;
        this.Arguments = Arguments;
        this.Type = t;
    }

    public override Expression Resolve(Resolver resolver, Type t)
    {
        for (int i = 0; i < Arguments.Count; i++) { Arguments[i] = Arguments[i].Resolve(resolver, Ctor.Formals[i].Type); }
        return this;
    }
}

public class LocalVariable {
    public String Name;
    public Type Type;
    public bool IsGhost;
  
    public LocalVariable(Token Tok, Token EndTok, String Name, Type Type, bool IsGhost) {
        this.Name = Name;
        this.Type = Type;
        this.IsGhost = IsGhost;
    }

}

public class MemberSelectExpr: Expression
{
    public Expression Obj;
    public string MemberName;
    public MemberDecl Member;
    internal Dictionary<TypeParameter,Type> TypeArgumentSubst;

    public MemberSelectExpr(Expression Obj, string FieldName) { this.Obj = Obj; this.MemberName = FieldName; }
    
    public MemberSelectExpr(Method Method, Dictionary<TypeParameter,Type> TypeArgumentSubstitutions) { this.Member = Method; this.TypeArgumentSubst = TypeArgumentSubstitutions; }

    public Dictionary<TypeParameter,Type> TypeArgumentSubstitutions() 
    {
      return TypeArgumentSubst;
    }

    public override Expression Resolve(Resolver resolver, Type t)
    {
        Obj = Obj.Resolve(resolver, null);
        DatatypeDecl data = Obj.Type.AsDatatype;
        if (MemberName.EndsWith("?"))
        {
            Type = Type.Bool;
        }
        else if (data != null)
        {
            foreach (DatatypeCtor ctor in data.Ctors)
            {
                foreach (Formal f in ctor.Formals)
                {
                    if (f.Name == MemberName)
                    {
                        Member = new DatatypeDestructor(ctor, Obj.tok, null, f.Name, f.IsGhost, f.Type);
                        Type = f.Type;
                    }
                }
            }
        }
        return this;
    }
}

public class SeqSelectExpr: Expression
{
    public bool SelectOne;
    public Expression Seq;
    public Expression E0;
    public Expression E1;

    public SeqSelectExpr(bool SelectOne, Expression Seq, Expression E0, Expression E1) { this.SelectOne = SelectOne; this.Seq = Seq; this.E0 = E0; this.E1 = E1; }

    public override Expression Resolve(Resolver resolver, Type t)
    {
        Seq = Seq.Resolve(resolver, null);
        if (E0 != null) { E0 = E0.Resolve(resolver, Type.Int); }
        if (E1 != null) { E1 = E1.Resolve(resolver, Type.Int); }
        Type = SelectOne ? ((SeqType)Seq.Type).Arg : Seq.Type;
        return this;
    }
}

public class SeqUpdateExpr: Expression
{
    public Expression Seq;
    public Expression Index;
    public Expression Value;
    public Expression ResolvedUpdateExpr = null;

    public SeqUpdateExpr(Expression Seq, Expression Index, Expression Value) { this.Seq = Seq; this.Index = Index; this.Value = Value; }

    static int xCount = 0;

    public override Expression Resolve(Resolver resolver, Type t)
    {
        Seq = Seq.Resolve(resolver, null);
        if (Seq.Type is SeqType)
        {
            Index = Index.Resolve(resolver, Type.Int);
            Value = Value.Resolve(resolver, ((SeqType)Seq.Type).Arg);
            Type = Seq.Type;
            return this;
        }
        else
        {
            UserDefinedType ut = (UserDefinedType)(Seq.Type);
            string name = ((IdentifierExpr)Index).Name;
            foreach (DatatypeCtor ctor in ut.AsDatatype.Ctors)
            {
                foreach (Formal formal in ctor.Formals)
                {
                    if (formal.Name == name)
                    {
                        //- Seq[name := Value]
                        //-    -->
                        //- let x := Seq in ctor(x.f1, ..., Value, ..., x.fn)
                        IdentifierExpr x = new IdentifierExpr(tok, "#UPDATE##" + (xCount++));
                        List<Expression> args = new List<Expression>(); // args = (x.f1, ..., Value, ..., x.fn)
                        foreach (Formal f in ctor.Formals)
                        {
                            Expression arg = (f.Name == name) ? Value : new MemberSelectExpr(x, f.Name);
                            args.Add(arg);
                        }
                        Expression body = new DatatypeValue(ut.TypeArgs, ctor, args, ut);
                        Expression ret = new LetExpr(true,
                            new List<ExprLhs>(new ExprLhs[] { new ExprLhs(new BoundVar(tok, x.Name, Seq.Type)) }),
                            new List<Expression>(new Expression[] { Seq }),
                            body);
                        return ret.Resolve(resolver, Seq.Type);
                    }
                }
            }
            throw new Exception("field update selector not found: " + name);
        }
    }
}

public class SeqDisplayExpr: Expression
{
    public List<Expression> Elements;

    public SeqDisplayExpr(List<Expression> Elements) { this.Elements = Elements; }

    public override Expression Resolve(Resolver resolver, Type t)
    {
        SeqType tSeq = t as SeqType;
        for (int i = 0; i < Elements.Count; i++) { Elements[i] = Elements[i].Resolve(resolver, tSeq == null ? null : tSeq.Arg); }
        Type = (Elements.Count == 0) ? t : new SeqType(Elements[0].Type);
        return this;
    }
}

public class ExprLhs
{
    public BoundVar Var;
    public ExprLhs(BoundVar Var) { this.Var = Var; }
}

public class ExprRhs
{
    public Expression Expr;
    public ExprRhs(Expression Expr) { this.Expr = Expr; }
}

public class SpecExpression
{
    public Attributes Attributes;
    public Expression E;

    public SpecExpression(Attributes Attributes, Expression E) { this.Attributes = Attributes; this.E = E; }
    public void Resolve(Resolver resolver)
    {
        Attributes.Resolve(resolver, Attributes);
        E = E.Resolve(resolver, Type.Bool);
    }
}

public class FrameExpression
{
    public Token tok;
    public Expression E = new ThisExpr();
    public string FieldName;
    public Field Field;

    public FrameExpression(string FieldName) { this.FieldName = FieldName; }
    public void Resolve(Resolver resolver) { Field = resolver.Find(resolver.fields, FieldName); }
}

public class Statement
{
    public Token Tok = Token.NoToken;
}

public class BlockStmt: Statement
{
    public List<Statement> Body;

    public BlockStmt() { Body = new List<Statement>(); }
}

public class VarDeclStmt: Statement
{
    public List<LocalVariable> Locals;
    public object Update;
    public bool IsGhost;

    //public VarDeclStmt(string name, Type type, bool isGhost) { this.Name = name; this.Type = type; this.IsGhost = isGhost; }
    //public VarDeclStmt(Token tok1, Token tok2, string name, Type type, bool isGhost): this(name, type, isGhost) {}
}

internal class VarDecl
{
    public string Name;
    public Type Type;
    public bool IsGhost;

    public VarDecl(string name, Type type, bool isGhost) { this.Name = name; this.Type = type; this.IsGhost = isGhost; }
    public VarDecl(Token tok1, Token tok2, string name, Type type, bool isGhost): this(name, type, isGhost) {}
}

public class IfStmt: Statement
{
    public Expression Guard;
    public Statement Thn;
    public Statement Els;
}

public class AssertStmt: Statement
{
    public Expression Expr;
}

public class AssignStmt: Statement
{
    public Expression Lhs;
    public ExprRhs Rhs;
}

public class CallStmt: Statement
{
    public List<BoundVar> Lhs;
    public List<Expression> Args;
    public MemberSelectExpr MethodSelect;

    internal CallStmt(List<Expression> Args, Dictionary<TypeParameter,Type> TypeArgumentSubstitutions, Method Method)
    {
        this.Lhs = new List<BoundVar>();
        this.Args = Args;
        this.MethodSelect = new MemberSelectExpr(Method, TypeArgumentSubstitutions);
    }
}

public class CalcStmt: Statement
{
    public class BinaryCalcOp
    {
        public BinaryExpr.Opcode Op;
    }

    public List<Expression> Steps;
    public List<BlockStmt> Hints;
    public BinaryCalcOp Op;

    public static Expression Lhs(Expression e) { return null; }
}

public class ForallStmt: Statement
{
    public List<BoundVar> BoundVars;
    public List<SpecExpression> Ens;
    public Expression Range;
    public Statement Body;
}

public class AssignSuchThatStmt: Statement
{
    public List<Expression> Lhss;
    public Expression Expr;
}

public class UpdateStmtRhs
{
    public Attributes Attributes;
}

public class ConcreteSyntaxStatement: Statement
{
    public List<Statement> ResolvedStatements;
}

public class UpdateStmt: Statement
{
    public List<UpdateStmtRhs> Rhss;
    public List<Statement> ResolvedStatements;
}

public class Mod
{
    public List<FrameExpression> Expressions;
    public Mod(List<FrameExpression> Expressions) { this.Expressions = Expressions; }
}

public class Decreases
{
    public List<Expression> Expressions;
    public Decreases(List<Expression> Expressions) { this.Expressions = Expressions; }
    public void Resolve(Resolver resolver)
    {
        for (int i = 0; i < Expressions.Count; i++)
        {
            Expressions[i] = Expressions[i].Resolve(resolver, Type.Int);
            if (Expressions[i].Type is NatType) { Expressions[i].Type = Type.Int; } // HACK
        }
    }
}

public interface ICallable
{
    Decreases Decreases { get; }
    List<Formal> Ins { get; }
}

public class MemberDecl
{
    public Token tok;
    public Attributes Attributes;
    public string Name;
    public bool IsGhost;
    public bool IsStatic = false;

    public MemberDecl(Token tok, Attributes Attributes, string Name, bool IsGhost)
    {
        this.tok = tok;
        this.Attributes = Attributes;
        this.Name = Name;
        this.IsGhost = IsGhost;
    }

}

public class Field: MemberDecl
{
    public Type Type;

    public Field(Token tok, Attributes Attributes, string Name, bool IsGhost, Type Type)
        :base(tok, Attributes, Name, IsGhost)
    {
        this.Type = Type;
    }

    //internal VarDeclStmt AsVarDecl() { return new VarDeclStmt(Name, Type, IsGhost); }
}

public class Function: MemberDecl, ICallable
{
    public ClassDecl EnclosingClass;
    public List<TypeParameter> TypeArgs;
    public List<Formal> Formals;
    public Type ResultType;
    public List<Expression> Req;
    public List<Expression> Ens;
    Decreases decreases;
    public Expression Body;

    public List<FrameExpression> Reads = new List<FrameExpression>(); // TODO
    public bool IsRecursive;

    internal Function(string Name): base(Token.NoToken, null, Name, true) {}

    public Function(Token tok, Attributes Attributes, string Name, bool IsGhost,
        List<TypeParameter> TypeArgs, List<Formal> Formals, Type ResultType,
        List<Expression> Req, List<Expression> Ens, Decreases decreases, Expression Body)
        :base(tok, Attributes, Name, IsGhost)
    {
        this.EnclosingClass = ClassDecl.TheClass;
        this.TypeArgs = TypeArgs;
        this.Formals = new List<Formal>();
        foreach (Formal f in Formals) { this.Formals.Add(new Formal(f.Name, f.Type, f.IsGhost || IsGhost)); }
        this.ResultType = ResultType;
        this.Req = Req;
        this.Ens = Ens;
        this.decreases = decreases;
        this.Body = Body;
    }

    public Decreases Decreases { get { return decreases; } }
    public List<Formal> Ins { get { return Formals; } }
}

public class Method: MemberDecl, ICallable
{
    Decreases decreases;

    public List<TypeParameter> TypeArgs;
    public List<Formal> Formals;
    public List<Formal> Outs;
    public List<SpecExpression> Req;
    public List<SpecExpression> Ens;
    public Mod Mod;
    public BlockStmt Body;

    public Method(Token tok, Attributes Attributes, string Name, bool IsGhost,
        List<TypeParameter> TypeArgs, List<Formal> Formals, List<Formal> Outs,
        List<SpecExpression> Req, List<SpecExpression> Ens, Mod Mod, Decreases decreases, BlockStmt Body)
        :base(tok, Attributes, Name, IsGhost)
    {
        this.TypeArgs = TypeArgs;
        this.Formals = new List<Formal>();
        foreach (Formal f in Formals) { this.Formals.Add(new Formal(f.Name, f.Type, f.IsGhost || IsGhost)); }
        this.Outs = new List<Formal>();
        foreach (Formal f in Outs) { this.Outs.Add(new Formal(f.Name, f.Type, f.IsGhost || IsGhost)); }
        this.Req = Req;
        this.Ens = Ens;
        this.Mod = Mod;
        this.decreases = decreases;
        this.Body = Body;
    }

    public Decreases Decreases { get { return decreases; } }
    public List<Formal> Ins { get { return Formals; } }
}

abstract public class Lemma: Method
{
    public Lemma(Token tok, Attributes Attributes, string Name, bool IsGhost,
        List<TypeParameter> TypeArgs, List<Formal> Formals, List<Formal> Outs,
        List<SpecExpression> Req, List<SpecExpression> Ens, Mod Mod, Decreases decreases, BlockStmt Body)
        :base(tok, Attributes, Name, IsGhost, TypeArgs, Formals, Outs, Req, Ens, Mod, decreases, Body)
    {
    }
}

public class TopLevelDecl
{
    public Token tok;
    public Attributes Attributes;
    public string Name;
}

public class DatatypeCtor
{
    public DatatypeDecl datatype;
    public string Name;
    public List<Formal> Formals;
    public DatatypeCtor(string Name, List<Formal> Formals) { this.Name = Name; this.Formals = Formals; }
}

public class DatatypeDestructor : Field
{    
    public DatatypeCtor EnclosingCtor;

    public DatatypeDestructor(DatatypeCtor EnclosingCtor, Token tok, Attributes Attributes, string Name, bool IsGhost, Type Type)
      : base(tok, Attributes, Name, IsGhost, Type) { this.EnclosingCtor = EnclosingCtor; }
}

public class DatatypeDecl: TopLevelDecl
{
    public List<TypeParameter> TypeArgs;
    public List<DatatypeCtor> Ctors;

    public DatatypeDecl(Token tok, string name, Attributes attrs, List<TypeParameter> TypeArgs, List<DatatypeCtor> Ctors)
    {
        this.tok = tok;
        this.Name = name;
        this.Attributes = attrs;
        this.TypeArgs = TypeArgs;
        this.Ctors = Ctors;
    }
}

public class ClassDecl: TopLevelDecl
{
    public static ClassDecl TheClass = new ClassDecl();

    public List<MemberDecl> Members = new List<MemberDecl>();
}

public class ModuleDefinition
{
    public string Name;
    public List<TopLevelDecl> TopLevelDecls;
    public ModuleDefinition(string Name, List<TopLevelDecl> TopLevelDecls) { this.Name = Name; this.TopLevelDecls = TopLevelDecls; }
}

public class Program
{
    public List<ModuleDefinition> Modules;
    public Program(List<ModuleDefinition> Modules) { this.Modules = Modules; }

    public static List<A> MakeList<A>(IEnumerable<A> e) { return new List<A>(e); }
}

public class Resolver
{
    public A Find<A>(Dictionary<string,A> dict, string key)
    {
        if (!dict.ContainsKey(key)) { throw new Exception("could not find: " + key); }
        else return dict[key];
    }
    public Dictionary<string,DatatypeDecl> datatypes = new Dictionary<string,DatatypeDecl>();
    public Dictionary<string,DatatypeCtor> constructors = new Dictionary<string,DatatypeCtor>();
    public Dictionary<string,Field> fields = new Dictionary<string,Field>();
    public Dictionary<string,Function> functions = new Dictionary<string,Function>();
    public Dictionary<string,Method> methods = new Dictionary<string,Method>();
    public Function currentFunction;
    public Method currentMethod;

    public Dictionary<string,TypeParameter> typeParams = new Dictionary<string,TypeParameter>();
    Dictionary<string,List<VarDecl>> vars = new Dictionary<string,List<VarDecl>>();
    int ghost;
    List<Dictionary<string,bool>> collectVars = new List<Dictionary<string,bool>>();

    public Resolver(Program program)
    {
        foreach (ModuleDefinition module in program.Modules)
        {
            foreach (TopLevelDecl decl in module.TopLevelDecls)
            {
                DatatypeDecl data = decl as DatatypeDecl;
                if (data != null)
                {
                    datatypes.Add(data.Name, data);
                    foreach (DatatypeCtor ctor in data.Ctors)
                    {
                        constructors.Add(ctor.Name, ctor);
                        ctor.datatype = data;
                    }
                }
            }
        }
        foreach (MemberDecl member in ClassDecl.TheClass.Members)
        {
            Field field = member as Field;
            Function fun = member as Function;
            Method method = member as Method;
            if (field != null) { fields.Add(field.Name, field); }
            if (fun != null) { functions.Add(fun.Name, fun); }
            if (method != null) { methods.Add(method.Name, method); }
        }
    }

    List<VarDecl> varList(string x)
    {
        if (!vars.ContainsKey(x)) { vars.Add(x, new List<VarDecl>()); }
        return vars[x];
    }

    public void PushTypeParam(TypeParameter p) { typeParams.Add(p.Name, p); }
    public void PopTypeParam(TypeParameter p) { typeParams.Remove(p.Name); }

    public void PushVar(string x, Type t, bool isGhost) { varList(x).Add(new VarDecl(x, t, isGhost)); }
    public void PushVar(BoundVar x) { PushVar(x.Name, x.Type, x.IsGhost); }
    public void PopVar(string x) { vars[x].RemoveAt(vars[x].Count - 1); }
    internal VarDecl Var(string x) { return vars.ContainsKey(x) && vars[x].Count > 0 ? vars[x][vars[x].Count - 1] : null; }

    public void PushGhost() { ghost++; }
    public void PopGhost() { ghost--; }
    public bool IsGhost() { return ghost != 0; }

    public void PushVarCollect() { collectVars.Add(new Dictionary<string,bool>()); }
    public Dictionary<string,bool> PopVarCollect() { Dictionary<string,bool> r = collectVars[collectVars.Count - 1]; collectVars.RemoveAt(collectVars.Count - 1); return r; }
    public void CollectVar(string x) { foreach (Dictionary<string,bool> d in collectVars) { d[x] = true; } }

    public static Type SubstType(Type t, Dictionary<TypeParameter,Type> map)
    {
        return t.Subst(map);
    }
}

}

