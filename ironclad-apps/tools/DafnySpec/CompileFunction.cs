using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using Type = Microsoft.Dafny.Type;
using System.Numerics;

public class CompileFunction: CompileBase
{
    public Function function;

    public CompileFunction(DafnySpec dafnySpec, Function function, TypeApply typeApply,
        TextWriter writer, TextWriter iwriter, string moduleName, List<string> imports):
        base(dafnySpec, typeApply, writer, iwriter, moduleName, imports)
    {
        this.function = function;
    }

    public void Compile()
    {
        Util.Assert(!isPrinting);
        string name = FunName(DafnySpec.SimpleName(typeApply.AppName()));
        string fullName = FunName(DafnySpec.SimpleName(typeApply.AppFullName()));
        bool isAxiom = Attributes.Contains(function.Attributes, "axiom");
        bool isPrivate = Attributes.Contains(function.Attributes, "private");
        bool hidden = Attributes.Contains(function.Attributes, "opaque");
        bool isHeap = DafnySpec.IsHeapFunction(function);
        List<string> heapParams = isHeap ? new List<string> { "$absMem:[int][int]int" } : new List<string>();
        List<string> heapArgs = isHeap ? new List<string> { "$absMem" } : new List<string>();
        var formals = function.Formals;
        var reads = function.Reads.Where(e => e.Field != null).ToList().ConvertAll(e =>
            new Formal(e.tok, e.FieldName, e.Field.Type, true, e.Field.IsGhost));
        formals = reads.Concat(formals).ToList();
        if (hidden && formals.Count == 0)
        {
            formals = new List<Formal> { new Formal(function.tok, "___dummy", Type.Bool, true, true) };
        }
        if (hidden && !function.Name.EndsWith("_FULL"))
        {
            ClassDecl cls = (ClassDecl)function.EnclosingClass;
            Function full = (Function)cls.Members.Find(m => m.Name == "#" + function.Name + "_FULL");
            dafnySpec.Compile_Function(full, typeApply.typeArgs);
        }
        bool isFull = hidden && function.Name.EndsWith("_FULL");
        string unfullName = isFull ? name.Substring(0, name.Length - "__FULL".Length)
            .Replace("#", "").Replace("____HASH", "") : null;
        
        string argsNoRec = String.Join(", ", heapArgs.Concat(formals.Select(f => GhostVar(f.Name))));
        List<RtlExp> reqsNoRec = minVerify ? new List<RtlExp>() : function.Req.ConvertAll(e => GhostExpression(e, true));
        List<RtlExp> enssNoRec = minVerify ? new List<RtlExp>() : function.Ens.ConvertAll(e => GhostExpression(e, true));
        AddTypeWellFormed(reqsNoRec, formals);
        AddTypeWellFormed(enssNoRec, name + "(" + argsNoRec + ")", function.IsGhost, function.ResultType);
        if (function.Body != null && !minVerify)
        {
            
            recFunName = name;
            stmtExprEnabled = true;
            GhostExpression(function.Body);
            function.IsRecursive = recCalls.Count != 0;
            stmtExprEnabled = false;
            stmts = new List<RtlStmt>();
            recCalls = new List<List<RtlExp>>();
            recFunName = null;
            
        }
        if (function.IsRecursive)
        {
            recFunName = name;
        }
        stmts = new List<RtlStmt>();
        stmtExprEnabled = true;
        var bodyDecls = PushForall();
        RtlExp body = (function.Body == null || minVerify) ? null : GhostExpression(function.Body);
        List<RtlStmt> bodyStmts = stmts;
        PopForall();
        stmtExprEnabled = false;
        stmts = new List<RtlStmt>();
        string parms = String.Join(", ", heapParams.Concat(
            formals.Select(f => GhostVar(f.Name) + ":" + TypeString(AppType(f.Type)))));
        string args = String.Join(", ", heapArgs.Concat(
            formals.Select(f => GhostVar(f.Name))));
        string sep = (heapArgs.Count + formals.Count != 0) ? ", " : "";
        string ret = TypeString(AppType(function.ResultType));
        string recName = "rec_" + name;
        string decreases = null;
        List<RtlExp> reqs = minVerify ? new List<RtlExp>() : function.Req.ConvertAll(e => GhostExpression(e, true));
        List<RtlExp> enss = minVerify ? new List<RtlExp>() : function.Ens.ConvertAll(e => GhostExpression(e, true));
        AddTypeWellFormed(reqs, formals);
        AddTypeWellFormed(enss, name + "(" + args + ")", function.IsGhost, function.ResultType);
        string reqConjunct = "(true" + String.Concat(reqs.Select(e => " && (" + e + ")")) + ")";
        string ensConjunct = "(true" + String.Concat(enss.Select(e => " && (" + e + ")")) + ")";
        Util.Assert(!isPrinting);
        if (function.IsRecursive && function.Body != null && !minVerify)
        {
            decreases = DecreasesExp(function);
        }
        List<RtlExp> enssRec = null;
        if (function.IsRecursive && (!hidden || isFull) && body != null && !minVerify)
        {
            enssRec = function.Ens.ConvertAll(e => GhostExpression(e, true));
        }
        isPrinting = true;
        var fiWriter = isPrivate ? writer : iwriter;
        if (function.IsRecursive && function.Body != null && !minVerify)
        {
            iwriter.WriteLine("function decreases0_" + name + "(" + parms + "):int { " + decreases + " }");
            iwriter.WriteLine("function decreases_" + name + "(" + parms + "):int { if decreases0_"
                + name + "(" + args + ") < 0 then 0 else 1 + decreases0_" + name + "(" + args + ") }");
            iwriter.WriteLine("function " + recName + "(__decreases:int, __unroll:int" + sep + parms
                + "):" + ret + ";");
            fiWriter.WriteLine("function implementation{" + FunName("unroll") + "(__unroll), "
                + recName + "(__decreases, __unroll" + sep + args + ")} "
                + recName + "(__decreases:int, __unroll:int" + sep + parms + "):" + ret);
            fiWriter.WriteLine("{");
            fiWriter.WriteLine("    " + body.ToString());
            fiWriter.WriteLine("}");
        }
        iwriter.WriteLine("function " + name + "(" + parms + "):" + ret + ";");
        if (hidden && !isFull && !minVerify)
        {
            iwriter.WriteLine("function unhide_" + name + "(" + parms + "):bool { true }");
            fiWriter.WriteLine("function implementation{unhide_" + name + "(" + args + ")} "
                + name + "(" + parms + "):" + ret);
            fiWriter.WriteLine("{");
            fiWriter.WriteLine("    " + fullName + "(" + args + ")");
            fiWriter.WriteLine("}");
            iwriter.WriteLine("atomic ghost procedure "
                + GhostProcName("reveal__" + DafnySpec.SimpleName(typeApply.AppName())) + "();");
            string forall = "forall " + parms + "::" + name + "(" + args + ") == "
                + fullName + "(" + args +")";
            iwriter.WriteLine("    ensures (" + forall + ");");
            writer.WriteLine("implementation "
                + GhostProcName("reveal__" + DafnySpec.SimpleName(typeApply.AppName())) + "()");
            writer.WriteLine("{");
            writer.WriteLine("    " + forall);
            writer.WriteLine("    {");
            writer.WriteLine("        assert unhide_" + name + "(" + args + ");");
            writer.WriteLine("    }");
            writer.WriteLine("}");
        }
        if (body != null && (!hidden || isFull))
        {
            fiWriter.WriteLine("function implementation{" + name + "(" + args + ")" + "} " + name
                + "(" + parms + "):" + ret);
            fiWriter.WriteLine("{");
            if (function.IsRecursive)
            {
                fiWriter.WriteLine("    " + recName + "(decreases_" + name + "(" + args + "), 0" + sep + args + ")");
            }
            else
            {
                fiWriter.WriteLine("    " + body.ToString());
            }
            fiWriter.WriteLine("}");
        }
        if (function.IsRecursive && (!hidden || isFull) && body != null && !minVerify)
        {
            AddTypeWellFormed(enssRec, recName + "(__decreases, __unroll" + sep + args + ")",
                function.IsGhost, function.ResultType);
            string ensRecConjunct = "(true" + String.Concat(enssRec.Select(e => " && (" + e + ")")) + ")";
            iwriter.WriteLine("atomic ghost procedure lemma_unroll2_" + recName
                + "(__decreases:int, __unroll:int, __unroll2:int" + sep + parms + ");");
            iwriter.WriteLine("    requires __decreases == decreases_" + name + "(" + args + ");");
            iwriter.WriteLine("    ensures  " + reqConjunct + " ==> " + ensRecConjunct + " && "
                + recName + "(__decreases, __unroll" + sep + args + ") == "
                + recName + "(__decreases, __unroll2" + sep + args + ");");
            
            writer.WriteLine("implementation lemma_unroll2_" + recName
                + "(__decreases:int, __unroll:int, __unroll2:int" + sep + parms + ")");
            writer.WriteLine("{");
            writer.WriteLine("    " + bodyDecls);
            writer.WriteLine("    assert fun_unroll(__unroll) && fun_unroll(__unroll2);");
            dafnySpec.WriteLemmas(writer, this, visibleModules, function.Attributes);
            writer.WriteLine("    if (" + reqConjunct + ")");
            writer.WriteLine("    {");
            bodyStmts.ForEach(s => writer.WriteLine("    " + s));
            writer.WriteLine("    }");
            foreach (List<RtlExp> recArgs in recCalls)
            {
                string rec_args = String.Join(", ", recArgs);
                string rec_decrease = "decreases_" + name + "(" + rec_args + ")";
                writer.WriteLine("    if (0 <= " + rec_decrease + " && " + rec_decrease + " < __decreases)");
                writer.WriteLine("    {");
                writer.WriteLine("        call lemma_unroll2_" + recName + "(" + rec_decrease
                    + ", __unroll + 1, __unroll2 + 1" + sep + rec_args + ");");
                writer.WriteLine("    }");
            }
            writer.WriteLine("}");
            string unroll_args = "decreases_" + name + "(" + args + "), __unroll";
            string unroll_args0 = "decreases_" + name + "(" + args + "), 0";
            string unroll = recName + "(" + unroll_args + sep + args + ")";
            string unroll0 = recName + "(" + unroll_args0 + sep + args + ")";

            
            var lwriter = isPrivate ? writer : iwriter;
            string recForall = "forall __unroll:int" + sep + parms + "::"
                + "{fun_unroll(__unroll), " + unroll + "} "
                + reqConjunct + " ==> fun_unroll(__unroll) ==> " + unroll + " == " + body;
            lwriter.WriteLine("atomic ghost procedure lemma_unroll_" + recName + "();");
            lwriter.WriteLine("    ensures  (" + recForall + ");");
            writer.WriteLine("implementation lemma_unroll_" + recName + "()");
            writer.WriteLine("{");
            dafnySpec.WriteLemmas(writer, this, visibleModules, function.Attributes);
            writer.WriteLine("    " + recForall);
            writer.WriteLine("    {");
            writer.WriteLine("    " + bodyDecls);
            writer.WriteLine("    if (" + reqConjunct + ")");
            writer.WriteLine("    {");
            bodyStmts.ForEach(s => writer.WriteLine("    " + s));
            writer.WriteLine("    }");
            writer.WriteLine("    }");
            writer.WriteLine("}");
            dafnySpec.AddLemma(new LemmaCall((isPrivate ? "private##" : "") + moduleName,
                visibleElementType,
                "call lemma_unroll_" + recName + "();",
                false));

            Func<string,string> forall = s => "forall __unroll:int" + sep + parms + "::"
                + "{" + s + unroll + "} "
                + "{fun_unroll__all(__unroll), " + unroll + "} "
                + reqConjunct + " ==> " + unroll + " == " + name + "(" + args + ") && " + ensConjunct;
            iwriter.WriteLine("atomic ghost procedure lemma_unroll_" + name + "();");
            iwriter.WriteLine("    ensures  (" + forall(unroll0 + ", ") + ");");
            writer.WriteLine("implementation lemma_unroll_" + name + "()");
            writer.WriteLine("{");
            dafnySpec.WriteLemmas(writer, this, visibleModules, function.Attributes);
            writer.WriteLine("    " + forall(""));
            writer.WriteLine("    {");
            writer.WriteLine("        call lemma_unroll2_" + recName + "("
                + unroll_args + ", 0" + sep + args + ");");
            writer.WriteLine("        if (" + reqConjunct + ")");
            writer.WriteLine("        {");
            enss.ForEach(e => writer.WriteLine("            assert " + e + ";"));
            writer.WriteLine("        }");
            writer.WriteLine("    }");
            writer.WriteLine("}");
            dafnySpec.AddLemma(new LemmaCall(moduleName, visibleElementType,
                "call lemma_unroll_" + name + "();", false));
        }
        else if (enssNoRec.Count > 0 && !minVerify)
        {
            string reqConjunctNoRec = "(true" + String.Concat(reqsNoRec.Select(e => " && (" + e + ")")) + ")";
            string ensConjunctNoRec = "(true" + String.Concat(enssNoRec.Select(e => " && (" + e + ")")) + ")";
            iwriter.WriteLine("function trigger_" + name + "(" + parms + "):bool { true }");
            iwriter.WriteLine("atomic ghost procedure lemma_fun_ensures_" + name + "();");
            string forallNoRec = "forall " + parms
                + "::{" + name + "(" + argsNoRec + ")}"
                + (isFull ? ("{" + unfullName + "(" + argsNoRec + ")}") : "")
                + "{trigger_" + name + "(" + argsNoRec + ")}"
                + "trigger_" + name + "(" + argsNoRec + ") ==> "
                + reqConjunctNoRec + " ==> " + ensConjunctNoRec;
            iwriter.WriteLine("    ensures (" + forallNoRec + ");");
            if (body != null || hidden || isAxiom)
            {
                writer.WriteLine("implementation lemma_fun_ensures_" + name + "()");
                writer.WriteLine("{");
                dafnySpec.WriteLemmas(writer, this, visibleModules, function.Attributes);
                writer.WriteLine("    " + forallNoRec);
                writer.WriteLine("    {");
                writer.WriteLine("        " + bodyDecls);
                writer.WriteLine("        if (" + reqConjunct + ")");
                writer.WriteLine("        {");
                if (isAxiom)
                {
                    writer.WriteLine("        // dummy lemma body for axiom");
                }
                else
                {
                    bodyStmts.ForEach(s => writer.WriteLine("            " + s));
                }
                writer.WriteLine("        }");
                if (hidden && !isFull)
                {
                    writer.WriteLine("        assert unhide_" + name + "(" + argsNoRec + ");");
                }
                if (hidden && isFull)
                {
                    writer.WriteLine("        assert unhide_" + unfullName + "(" + argsNoRec + ");");
                }
                writer.WriteLine("        if (" + reqConjunct + ")");
                writer.WriteLine("        {");
                enssNoRec.ForEach(e => writer.WriteLine("            assert " + e + ";"));
                writer.WriteLine("        }");
                writer.WriteLine("    }");
                writer.WriteLine("}");
            }
            dafnySpec.AddLemma(new LemmaCall(moduleName, visibleElementType,
                "call lemma_fun_ensures_" + name + "();", false));
        }
        isPrinting = false;
    }
}
