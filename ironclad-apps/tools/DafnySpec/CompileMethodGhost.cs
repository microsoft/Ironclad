using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using Type = Microsoft.Dafny.Type;
using System.Numerics;

public class CompileMethodGhost: CompileBase
{
    protected Method method;
    protected bool isGhost;
    protected List<string> calledMethods = new List<string>();

    public CompileMethodGhost(DafnySpec dafnySpec, Method method, TypeApply typeApply,
        TextWriter writer, TextWriter iwriter, string moduleName, List<string> imports):
        base(dafnySpec, typeApply, writer, iwriter, moduleName, imports)
    {
        this.method = method;
    }

    public List<string> GetStaticFieldMods()
    {
        return (method.Mod.Expressions.Exists(e => e.E is ThisExpr && e.FieldName == null))
            ? dafnySpec.allStaticFields.ConvertAll(x => GhostVar(x))
            : method.Mod.Expressions.Where(e => e.E is ThisExpr).Select(e => GhostVar(e.FieldName)).ToList();
    }

    public void CompileGhost(string name, string parms, string rets, string req, Action printBody)
    {
        List<RtlExp> reqs = method.Req.ConvertAll(a => GhostExpression(a.E, false, false, a.Attributes)); 
        List<RtlExp> enss = method.Ens.ConvertAll(a => GhostExpression(a.E, false, false, a.Attributes));
        AddTypeWellFormed(reqs, method.Ins);
        AddTypeWellFormed(enss, method.Outs);
        Util.Assert(!isPrinting);
        isPrinting = true;
        iwriter.WriteLine("atomic ghost procedure " + name + "(" + parms + ") returns(" + rets + ");");
        if (req != null)
        {
            iwriter.WriteLine("    requires " + req + ";");
        }
        reqs.ForEach(e => iwriter.WriteLine("    requires " + e + ";"));
        enss.ForEach(e => iwriter.WriteLine("    ensures  " + e + ";"));
        GetStaticFieldMods().ForEach(x => iwriter.WriteLine("    modifies " + x + ";"));
        if (printBody != null)
        {
            writer.WriteLine("implementation " + name + "(" + parms + ") returns(" + rets + ")");
            writer.WriteLine("{");
            allVars.Keys
                .Where(x => !method.Ins.Select(y => GhostVar(y.Name)).ToList().Contains(x)
                    && !method.Outs.Select(y => GhostVar(y.Name)).ToList().Contains(x)).ToList()
                .ForEach(x => writer.WriteLine("    var " + x + ":" + TypeString(allVars[x].type) + ";"));
            dafnySpec.WriteLemmas(writer, this, visibleModules, method.Attributes);
            printBody();
            writer.WriteLine("}");
        }
        isPrinting = false;
    }

    public void CompileGhost()
    {
        bool isAxiom = Attributes.Contains(method.Attributes, "axiom");
        bool isHeap = DafnySpec.IsHeapMethod(method);
        BlockStmt body = method.Body;
        List<string> heapParams = isHeap ? new List<string> { "$absMem:[int][int]int" } : new List<string>();
        List<string> heapArgs = isHeap ? new List<string> { "$absMem" } : new List<string>();
        string parms = String.Join(", ", heapParams.Concat(
            method.Ins.Select(x => GhostVar(x.Name) + ":" + TypeString(AppType(x.Type)))));
        string rets = String.Join(", ", method.Outs.Select(x => GhostVar(x.Name) + ":" + TypeString(AppType(x.Type))));
        if (body != null)
        {
            foreach (Statement stmt in body.Body)
            {
                AddGhostStatement(stmt, null);
            }
            Action printStmts = () =>
            {
                string indent = "    ";
                foreach (RtlStmt s in stmts)
                {
                    RtlIndent rtlIndent = s as RtlIndent;
                    if (rtlIndent != null)
                    {
                        indent = rtlIndent.Positive ? indent + "    " : indent.Substring(4);
                        continue;
                    }
                    if (s.comment != null)
                    {
                        writer.WriteLine(indent + "// " + s.comment().Replace(Environment.NewLine, Environment.NewLine + indent));
                    }
                    if (s.ToString() != "")
                    {
                        writer.WriteLine(indent + s.ToString().Replace(Environment.NewLine, Environment.NewLine + indent));
                    }
                }
            };
            if (isRecursive)
            {
                Util.Assert(!isPrinting);
                string decreases = DecreasesExp(method);
                isPrinting = true;
                iwriter.WriteLine("function decreases_" + procName + "(" + parms + "):int { " + decreases + " }");
                isPrinting = false;
                string applyDecrease = "decreases_" + procName + "("
                    + String.Join(", ", heapArgs.Concat(method.Ins.Select(x => GhostVar(x.Name)))) + ")";
                string sep = (method.Ins.Count + heapArgs.Count == 0) ? "" : ", ";
                CompileGhost("rec_" + procName, "__decreases:int" + sep + parms, rets,
                    "__decreases == " + applyDecrease, printStmts);
                CompileGhost(procName, parms, rets, null, () =>
                    {
                        writer.WriteLine("    call " + String.Join(", ", method.Outs.Select(x => GhostVar(x.Name)))
                            + (method.Outs.Count == 0 ? "" : " := ") + "rec_" + procName + "(" + applyDecrease
                            + String.Concat(heapArgs.Concat(method.Ins.Select(x => GhostVar(x.Name)))
                                .Select(x => ", " + x)) + ");");
                    });
            }
            else
            {
                CompileGhost(procName, parms, rets, null, printStmts);
            }
        }
        else if (isAxiom)
        {
            CompileGhost(procName, parms, rets, null, () => writer.WriteLine("    // dummy method body for axiom"));
        }
        else
        {
            CompileGhost(procName, parms, rets, null, null);
        }
    }

    public virtual void Compile()
    {
        Util.Assert(!isPrinting);
        
        isGhost = method is Lemma || method.IsGhost;
        bool isImported = Attributes.Contains(method.Attributes, "imported");
        bool isAxiom = Attributes.Contains(method.Attributes, "axiom");
        if (isImported && method.Body == null)
        {
            return;
        }
        if (!isGhost)
        {
            throw new Exception("only ghost methods can appear in specifications");
        }
        procName = GhostProcName(SimpleName(typeApply.AppName()));
        if (method.Body == null && method.Name.StartsWith("reveal_")) 
        {
            return;
        }
        CompileGhost();
    }
}
