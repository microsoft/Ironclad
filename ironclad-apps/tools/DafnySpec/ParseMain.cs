using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Numerics;
using Microsoft.Boogie;
using Microsoft.Dafny;

namespace Microsoft.Boogie
{

public class CommandLineOptionEngine
{
    public class CommandLineParseState
    {
        public List<string> args;
        public int i;
        public bool ConfirmArgumentCount(int n)
        {
            return (i++) + n <= args.Count;
        }
    }
}

public class CommandLineOptions
{
    public static CommandLineOptions Clo = new CommandLineOptions();

    public bool RunningBoogieFromCommandLine;
    public List<string> Files = new List<string>();

    protected virtual bool ParseOption(string name, CommandLineOptionEngine.CommandLineParseState ps)
    {
        return false;
    }

    public bool Parse(string[] args)
    {
        CommandLineOptionEngine.CommandLineParseState ps = new CommandLineOptionEngine.CommandLineParseState();
        Func<string,int,char,string> replaceAt = (s, i, c) => s.Substring(0, i) + c + s.Substring(i + 1);
        ps.args = new List<string>(args)
            .ConvertAll(s => s.StartsWith("/") && s.Contains(":") ? replaceAt(s, s.IndexOf(':'), '*') : s)
            .SelectMany(s => s.Split(new char[] {'*'})).ToList();
        ps.i = 0;
        for (ps.i = 0; ps.i < ps.args.Count; ps.i++)
        {
            string name = ps.args[ps.i];
            if (name.StartsWith("-") || name.StartsWith("/"))
            {
                if (!Clo.ParseOption(name.Substring(1), ps))
                {
                    throw new Exception("unknown command-line switch: " + name);
                }
            }
            else
            {
                Files.Add(new FileInfo(ps.args[ps.i]).FullName);
            }
        }
        return true;
    }
}

}

namespace Microsoft.Dafny
{

public class DafnyOptions: CommandLineOptions
{
    public static void Install(DafnyOptions options)
    {
        Clo = options;
    }
}

class AutoReq
{
    Resolver resolver;
    Dictionary<string,string> doneFunctions = new Dictionary<string,string>();
    Dictionary<string,string> doneMethods = new Dictionary<string,string>();

    internal AutoReq(Resolver resolver)
    {
        this.resolver = resolver;
    }

    internal void ReqFunction(Function fun)
    {
        if (!doneFunctions.ContainsKey(fun.Name))
        {
            doneFunctions.Add(fun.Name, "");
            if (Attributes.Contains(fun.Attributes, "autoReq"))
            {
                if (Attributes.Contains(fun.Attributes, "opaque") && !fun.Name.EndsWith("_FULL"))
                {
                    var new_reqs = new List<Expression>();
                    Function full = (Function)ClassDecl.TheClass.Members.Find(
                        m => m.Name == "#" + fun.Name + "_FULL");
                    ReqFunction(full);
                    fun.Req.Clear();
                    fun.Req.AddRange(full.Req);
                }
                else
                {
                    List<Expression> auto_reqs = new List<Expression>();
                    foreach (Expression req in fun.Req)
                    {
                        auto_reqs.AddRange(GenerateAutoReqs(req, fun));
                    }
                    fun.Req.InsertRange(0, auto_reqs);
                    if (fun.Body != null)
                    {
                        auto_reqs = GenerateAutoReqs(fun.Body, fun);
                        fun.Req.AddRange(auto_reqs);
                    }
                }
            }
        }
    }

    internal void ReqMethod(Method method)
    {
        if (!doneMethods.ContainsKey(method.Name))
        {
            doneMethods.Add(method.Name, "");
            if (Attributes.Contains(method.Attributes, "autoReq"))
            {
                List<SpecExpression> auto_reqs = new List<SpecExpression>();
                foreach (SpecExpression req in method.Req)
                {
                    List<Expression> local_auto_reqs = GenerateAutoReqs(req.E, null);
                    foreach (Expression local_auto_req in local_auto_reqs)
                    {
                        auto_reqs.Add(new SpecExpression(null, local_auto_req));
                    }
                }
                method.Req.InsertRange(0, auto_reqs);
            }
        }
    }

    Expression Andify(List<Expression> exprs)
    {
        Expression ret = null;
        foreach (var expr in exprs)
        {
            ret = (ret == null) ? expr : new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, ret, expr);
            ret.Type = Type.Bool;
        }
        return ret != null ? ret : new LiteralExpr(true);
    }

    List<Expression> GatherReqs(Function fun, List<Expression> args)
    {
        List<Expression> translated_f_reqs = new List<Expression>();
        if (fun.Req.Count > 0)
        {
            List<Tuple<BoundVar,Expression>> substs = fun.Formals.Zip(args, (f, arg) =>
                Tuple.Create(new BoundVar(Token.NoToken, f.Name, f.Type), arg)).ToList();
            substs = substs.Where(p => !(p.Item2 is IdentifierExpr) || ((IdentifierExpr)p.Item2).Name != p.Item1.Name).ToList();
            List<ExprLhs> lhss = substs.ConvertAll(p => new ExprLhs(p.Item1));
            foreach (var req in fun.Req)
            {
                var letExpr = new LetExpr(true, lhss, substs.ConvertAll(p => p.Item2), req);
                letExpr.tryToEliminate = true;
                translated_f_reqs.Add(letExpr);
            }
        }
        return translated_f_reqs;
    }

    List<Expression> GenerateAutoReqs(Expression expr, Function parent)
    {
        List<Expression> reqs = new List<Expression>();
        Func<Expression,List<Expression>> generateAutoReqs = e => GenerateAutoReqs(e, parent);
        if (expr is LiteralExpr)
        {
        }
        else if (expr is ThisExpr)
        {
        }
        else if (expr is IdentifierExpr)
        {
        }
        else if (expr is SeqDisplayExpr)
        {
            SeqDisplayExpr e = (SeqDisplayExpr)expr;
            foreach (var elt in e.Elements)
            {
                reqs.AddRange(generateAutoReqs(elt));
            }
        }
        else if (expr is MemberSelectExpr && ((MemberSelectExpr)expr).Member is Field)
        {
            MemberSelectExpr e = (MemberSelectExpr)expr;
            reqs.AddRange(generateAutoReqs(e.Obj));
        }
        else if (expr is SeqSelectExpr)
        {
            SeqSelectExpr e = (SeqSelectExpr)expr;
            reqs.AddRange(generateAutoReqs(e.Seq));
            if (e.E0 != null)
            {
                reqs.AddRange(generateAutoReqs(e.E0));
            }
            if (e.E1 != null)
            {
                reqs.AddRange(generateAutoReqs(e.E1));
            }
        }
        else if (expr is SeqUpdateExpr)
        {
            SeqUpdateExpr e = (SeqUpdateExpr)expr;
            reqs.AddRange(generateAutoReqs(e.Seq));
            reqs.AddRange(generateAutoReqs(e.Index));
            reqs.AddRange(generateAutoReqs(e.Value));
        }
        else if (expr is FunctionCallExpr)
        {
            FunctionCallExpr e = (FunctionCallExpr)expr;
            foreach (var arg in e.Args)
            {
                reqs.AddRange(generateAutoReqs(arg));
            }
            if (parent == null || parent.Name != e.name)
            {
                ReqFunction(e.Function);
                reqs.AddRange(GatherReqs(e.Function, e.Args));
            }
        }
        else if (expr is DatatypeValue)
        {         
            DatatypeValue dtv = (DatatypeValue)expr;
            for (int i = 0; i < dtv.Arguments.Count; i++)
            {
                Expression arg = dtv.Arguments[i];
                reqs.AddRange(generateAutoReqs(arg));
            }
        }
        else if (expr is OldExpr)
        {
        }
        else if (expr is MatchExpr)
        {
            MatchExpr e = (MatchExpr)expr;
            reqs.AddRange(generateAutoReqs(e.Source));
            List<MatchCaseExpr> newMatches = new List<MatchCaseExpr>();
            foreach (MatchCaseExpr caseExpr in e.Cases)
            {
                MatchCaseExpr c = new MatchCaseExpr(caseExpr.name, caseExpr.Arguments, Andify(generateAutoReqs(caseExpr.Body)));
                newMatches.Add(c);
            }
            reqs.Add(new MatchExpr(e.Source, newMatches));
        }
        else if (expr is UnaryOpExpr)
        {
            UnaryOpExpr e = (UnaryOpExpr)expr;
            Expression arg = e.E;            
            reqs.AddRange(generateAutoReqs(arg));
        }
        else if (expr is BinaryExpr)
        {
            BinaryExpr e = (BinaryExpr)expr;
            switch (e.Op)
            {
                case BinaryExpr.Opcode.Imp:
                case BinaryExpr.Opcode.And:
                    reqs.AddRange(generateAutoReqs(e.E0));
                    foreach (var req in generateAutoReqs(e.E1))
                    {
                        reqs.Add(new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Imp, e.E0, req));
                    }
                    break;
                case BinaryExpr.Opcode.Or:
                    reqs.AddRange(generateAutoReqs(e.E0));
                    foreach (var req in generateAutoReqs(e.E1))
                    {
                        reqs.Add(new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Imp,
                            new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Not, e.E0), req));
                    }
                    break;
                default:
                    reqs.AddRange(generateAutoReqs(e.E0));
                    reqs.AddRange(generateAutoReqs(e.E1));
                    break;
            }
        }
        else if (expr is LetExpr)
        {
            var e = (LetExpr)expr;
            if (e.Exact)
            {
                foreach (var rhs in e.RHSs)
                {
                    reqs.AddRange(generateAutoReqs(rhs));
                }
                var new_reqs = generateAutoReqs(e.Body);
                if (new_reqs.Count > 0)
                {
                    reqs.Add(new LetExpr(e.Exact, e.LHSs, e.RHSs, Andify(new_reqs)));
                }
            }
        }
        else if (expr is QuantifierExpr)
        {
            QuantifierExpr e = (QuantifierExpr)expr;
            var auto_reqs = generateAutoReqs(e.Term);
            if (auto_reqs.Count > 0)
            {
                Expression allReqsSatisfied = Andify(auto_reqs);
                Expression allReqsSatisfiedAndTerm = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, allReqsSatisfied, e.Term);
                e.Term = allReqsSatisfiedAndTerm;
            }
        }
        else if (expr is StmtExpr)
        {
            var e = (StmtExpr)expr;
            reqs.AddRange(generateAutoReqs(e.E));
        }
        else if (expr is ITEExpr)
        {
            ITEExpr e = (ITEExpr)expr;
            reqs.AddRange(generateAutoReqs(e.Test));
            reqs.Add(new ITEExpr(e.Test, Andify(generateAutoReqs(e.Thn)), Andify(generateAutoReqs(e.Els))));
        }
        return reqs;
    }
}

public class Main
{
    public static void Resolve(Resolver resolver, Program program)
    {
        try
        {
            foreach (ModuleDefinition module in program.Modules)
            {
                foreach (TopLevelDecl decl in module.TopLevelDecls)
                {
                    DatatypeDecl data = decl as DatatypeDecl;
                    if (data != null)
                    {
                        foreach (var ctor in data.Ctors)
                        {
                            resolver.PushGhost();
                            data.TypeArgs.ForEach(p => resolver.PushTypeParam(p));
                            ctor.Formals.ForEach(f => f.Resolve(resolver));
                            data.TypeArgs.ForEach(p => resolver.PopTypeParam(p));
                            resolver.PopGhost();
                        }
                    }
                }
            }
            foreach (MemberDecl member in ClassDecl.TheClass.Members)
            {
                Field field = member as Field;
                Function fun = member as Function;
                Method method = member as Method;
                if (field != null)
                {
                    if (field.IsGhost) { resolver.PushGhost(); }
                    field.Type.Resolve(resolver);
                    if (field.IsGhost) { resolver.PopGhost(); }
                }
                if (fun != null)
                {
                    resolver.currentFunction = fun;
                    resolver.PushGhost();
                    fun.TypeArgs.ForEach(p => resolver.PushTypeParam(p));
                    fun.Formals.ForEach(x => { x.Resolve(resolver); });
                    fun.ResultType.Resolve(resolver);
                    fun.TypeArgs.ForEach(p => resolver.PopTypeParam(p));
                    resolver.PopGhost();
                    resolver.currentFunction = null;
                }
                if (method != null)
                {
                    resolver.currentMethod = method;
                    if (method.IsGhost) { resolver.PushGhost(); }
                    method.TypeArgs.ForEach(p => resolver.PushTypeParam(p));
                    method.Formals.ForEach(x => { x.Resolve(resolver); });
                    method.Outs.ForEach(x => { x.Resolve(resolver); });
                    method.TypeArgs.ForEach(p => resolver.PopTypeParam(p));
                    if (method.IsGhost) { resolver.PopGhost(); }
                    resolver.currentMethod = null;
                }
            }
            foreach (MemberDecl member in ClassDecl.TheClass.Members)
            {
                Function fun = member as Function;
                Method method = member as Method;
                if (fun != null)
                {
                    resolver.currentFunction = fun;
                    resolver.PushGhost();
                    fun.TypeArgs.ForEach(p => resolver.PushTypeParam(p));
                    fun.Formals.ForEach(x => { resolver.PushVar(x.Name, x.Type, true); });
                    fun.ResultType.Resolve(resolver);
                    fun.Req = fun.Req.ConvertAll(e => e.Resolve(resolver, Type.Bool));
                    fun.Ens = fun.Ens.ConvertAll(e => e.Resolve(resolver, Type.Bool));
                    fun.Decreases.Resolve(resolver);
                    if (fun.Body != null) { fun.Body = fun.Body.Resolve(resolver, fun.ResultType); }
                    if (fun.IsRecursive && fun.Decreases.Expressions.Count == 0)
                    {
                        fun.Decreases.Expressions.Add(new IdentifierExpr(Token.NoToken, fun.Formals[0].Name));
                        fun.Decreases.Resolve(resolver);
                    }
                    fun.Formals.ForEach(x => resolver.PopVar(x.Name));
                    fun.TypeArgs.ForEach(p => resolver.PopTypeParam(p));
                    resolver.PopGhost();
                    resolver.currentFunction = null;
                }
                if (method != null)
                {
                    resolver.currentMethod = method;
                    if (method.IsGhost) { resolver.PushGhost(); }
                    method.TypeArgs.ForEach(p => resolver.PushTypeParam(p));
                    method.Formals.ForEach(x => { resolver.PushVar(x.Name, x.Type, true); });
                    method.Req.ForEach(e => e.Resolve(resolver));
                    method.Outs.ForEach(x => { resolver.PushVar(x.Name, x.Type, true); });
                    method.Ens.ForEach(e => e.Resolve(resolver));
                    method.Decreases.Resolve(resolver);
                    method.Outs.ForEach(x => resolver.PopVar(x.Name));
                    method.Formals.ForEach(x => resolver.PopVar(x.Name));
                    method.TypeArgs.ForEach(p => resolver.PopTypeParam(p));
                    if (method.IsGhost) { resolver.PopGhost(); }
                    resolver.currentMethod = null;
                }
            }
        }
        catch (Exception e)
        {
            string ctxt =
                (resolver.currentMethod != null) ? "in method " + resolver.currentMethod.Name + ": ":
                (resolver.currentFunction != null) ? "in function " + resolver.currentFunction.Name + ": ":
                "";
            throw new Exception(ctxt, e);
        }
    }

    public static string ParseCheck(List<string> modules, string name, out Program program)
    {
        LiteralExpr.MakeBigInt = new MakeBigInt(s => new LiteralExpr(BigInteger.Parse(s)));
        program = new Program(modules.ConvertAll(m => new ModuleDefinition(m, Parser.parse(m))));

        Resolver resolver = new Resolver(program);
        Resolve(resolver, program);

        List<MemberDecl> fullFunctions = new List<MemberDecl>();
        foreach (MemberDecl member in ClassDecl.TheClass.Members)
        {
            Function fun = member as Function;
            if (fun != null && Attributes.Contains(fun.Attributes, "opaque"))
            {
                Function full = new Function(fun.tok, fun.Attributes, "#" + fun.Name + "_FULL",
                    fun.IsGhost, fun.TypeArgs, fun.Formals, fun.ResultType, fun.Req, fun.Ens,
                    fun.Decreases, fun.Body);
                full.IsRecursive = fun.IsRecursive;
                fun.Body = null;
                fullFunctions.Add(full);
            }
        }
        ClassDecl.TheClass.Members.AddRange(fullFunctions);

        AutoReq autoReq = new AutoReq(resolver);
        foreach (MemberDecl member in ClassDecl.TheClass.Members)
        {
            Function fun = member as Function;
            Method method = member as Method;
            if (fun != null) { autoReq.ReqFunction(fun); }
            if (method != null) { autoReq.ReqMethod(method);}
        }

        Resolve(resolver, program);

        return null;
    }
}

}

