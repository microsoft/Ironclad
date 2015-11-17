using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using Type = Microsoft.Dafny.Type;
using System.Numerics;

public class DafnySpec_Options: DafnyOptions
{
    public string outDir;
    public bool minVerify = false;

    protected override bool ParseOption(string name, Bpl.CommandLineOptionEngine.CommandLineParseState ps)
    {
        switch (name) {
            case "outdir":
                if (ps.ConfirmArgumentCount(1))
                {
                    outDir = ps.args[ps.i];
                }
                return true;
            case "minVerify":
                minVerify = true;
                return true;
            default:
                break;
        }
        return base.ParseOption(name, ps);
    }
}

public class LemmaCall
{
    public readonly string module;
    public readonly Type type;
    public readonly string stmt;
    public readonly bool loopLemma;

    public LemmaCall(string module, Type type, string stmt, bool loopLemma)
    {
        this.module = module;
        this.type = type;
        this.stmt = stmt;
        this.loopLemma = loopLemma;
    }
}

public class NonglobalVariable 
{
    public static string CompilerizeName(string s) 
    {
        return s.Replace("_", "__");
    }

}

public class DafnySpec
{
    public const string ImpBasmExtn = ".imp.basm";
    public const string IfcBasmExtn = ".ifc.basm";

    protected TextWriter trustedWriter = null;
    protected TextWriter trustedIWriter = null;
    protected string outDir = null;
    protected TextWriter outListWriter = null;
    public bool minVerify = false;
    protected Dictionary<string,Dictionary<string,string>> fileImports = new Dictionary<string,Dictionary<string,string>>();
    protected Dictionary<TypeApply,TypeApply> compileMethods = new Dictionary<TypeApply,TypeApply>();
    protected Dictionary<TypeApply,TypeApply> compileFunctions = new Dictionary<TypeApply,TypeApply>();
    protected Dictionary<TypeApply,UserDefinedType> compileDatatypes = new Dictionary<TypeApply,UserDefinedType>();
    protected List<TypeApply> compileDatatypeList = new List<TypeApply>();
    protected Dictionary<string,Method> allMethods = new Dictionary<string,Method>();
    protected Dictionary<string,Function> allFunctions = new Dictionary<string,Function>();
    protected Dictionary<string,DatatypeDecl> allDatatypes = new Dictionary<string,DatatypeDecl>();
    public List<string> allStaticFields = new List<string>();
    public static Type defaultDefaultPolyType = Type.Int;
    public static Type defaultPolyType = defaultDefaultPolyType; // HACK
    protected Dictionary<string,Tuple<TextWriter,TextWriter,string,List<string>>> outDirWriters =
        new Dictionary<string, Tuple<TextWriter, TextWriter, string, List<string>>>(StringComparer.CurrentCultureIgnoreCase);

    public static void Main(string[] args)
    {
        try
        {
            Util.DebugWriteLine("hello");
            DafnySpec_Options options = new DafnySpec_Options();
            DafnyOptions.Install(options);
            Bpl.CommandLineOptions.Clo.RunningBoogieFromCommandLine = true;
            if (!Bpl.CommandLineOptions.Clo.Parse(args))
            {
                throw new Exception("argument parse error");
            }
            IList<string> files = Bpl.CommandLineOptions.Clo.Files;
            if (files.Count == 0)
            {
                throw new Exception("*** Error: No input files were specified.");
            }
            new DafnySpec().CompileSpec(options, files);
        }
        catch (Exception e)
        {
            Console.OpenStandardOutput().Flush();
            Console.WriteLine(e);
            Console.Error.WriteLine(e);
            Environment.Exit(-1);
        }
    }

    public static string CleanName(string x)
    {
        return x.Replace("'", "___PRIME_").Replace("#", "___HASH_");
    }

    public static string GhostProcName(string x) { return "proc_" + CleanName(x); }
    public static string FunName(string x) { return "fun_" + CleanName(x); }
    public static string SimpleName(string x) { return x.Contains('.') ? x.Substring(x.LastIndexOf('.') + 1) : x; }

    public static string SanitizedName(MemberDecl m) 
    {
        return /* m.EnclosingClass.FullSanitizedName + "." + */ NonglobalVariable.CompilerizeName(m.Name.Replace("#", "&")).Replace("&", "#");
    }

    public static string SimpleSanitizedName(MemberDecl m) { return SimpleName(SanitizedName(m)); }

    public static bool IsArrayType(Type t)
    {
        return t is UserDefinedType && ((UserDefinedType)t).Name == "array";
    }

    public static bool IsHeapFunction(Function f)
    {
        // TODO: use f.Reads?
        return Attributes.Contains(f.Attributes, "heap")
            || f.Formals.Exists(p => IsArrayType(p.Type)) || IsArrayType(f.ResultType);
    }

    public static bool IsHeapMethod(Method m)
    {
        return Attributes.Contains(m.Attributes, "heap")
            || !m.IsGhost
            || m.Ins.Exists(p => IsArrayType(p.Type))
            || m.Outs.Exists(p => IsArrayType(p.Type));
    }

    public static bool IsPtrType(Type t)
    {
        return !(t is BoolType) && !(t is IntType) && !(t is NatType) && !(t is RealType);
    }

    public static IdentifierExpr MakeIdentifierExpr(string name, Type type, bool isGhost)
    {
        Util.Assert(type != null);
        IdentifierExpr id = new IdentifierExpr(Bpl.Token.NoToken, name);
        id.Type = type;
        id.Var = new LocalVariable(Bpl.Token.NoToken, Bpl.Token.NoToken, name, type, isGhost);
        return id;
    }

    public static BinaryExpr MakeBinaryExpr(BinaryExpr.Opcode op,
        BinaryExpr.ResolvedOpcode rop, Type t, Expression e0, Expression e1)
    {
        Util.Assert(t != null && e0.Type != null && e1.Type != null);
        BinaryExpr e = new BinaryExpr(e0.tok, op, e0, e1);
        e.ResolvedOp = rop;
        e.Type = t;
        return e;
    }

    public static Type ToType(Type t)
    {
        TypeProxy proxy = t as TypeProxy;
        if (proxy != null && proxy.T == null)
        {
            Util.Assert(false);     // Dafny appears to be doing sane type resolution now
            return defaultPolyType; //- pick arbitrary type
        }
        if (proxy != null)
        {
            return ToType(proxy.T);
        }
        return t;
    }

    public string TypeString(Type t)
    {
        t = ToType(t);
        MapType mt = t as MapType;
        UserDefinedType ut = t as UserDefinedType;
        SeqType seq = t as SeqType;

        if (t is BoolType)
        {
            return "bool";
        }
        else if (t is IntType)
        {
            return "int";
        }
        else if (t is RealType)
        {
            return "real";
        }
        else if (mt != null)
        {   
            return "[" + TypeString(mt.Domain) + "]" + TypeString(mt.Range);
        }
        else if (ut != null && ut.AsDatatype != null)
        {
            return Compile_Datatype(ut).AppName();
        }
        else if (ut != null && ut.Name == "array")
        {
            if (!(ToType(ut.TypeArgs[0]) is IntType) || ToType(ut.TypeArgs[0]) is NatType)
            {
                throw new Exception("not implemented: arrays of non-int types: " + ToType(ut.TypeArgs[0]));
            }
            return "ArrayOfInt";
        }
        else if (ut != null && ut.Name == "INTERNAL_AbsMem")
        {
            return "[int][int]int";
        }
        else if (ut != null && ut.Name == "INTERNAL_ArrayElems")
        {
            return "[int]int";
        }
        else if (ut != null && !ut.IsTypeParameter)
        {
            return ut.Name;
        }
        else if (seq != null)
        {
            return Compile_SeqType(seq).AppName();
        }
        else
        {
            throw new Exception("not implemented: " + t + ": " + t.GetType());
        }
    }

    public Method FindMethod(string name)
    {
        if (allMethods.ContainsKey(name))
        {
            return allMethods[name];
        }
        else
        {
            throw new Exception("could not find method " + name);
        }
    }

    public Function FindFunction(string name)
    {
        if (allFunctions.ContainsKey(name))
        {
            return allFunctions[name];
        }
        else
        {
            throw new Exception("could not find function " + name);
        }
    }

    public DatatypeDecl FindDatatype(string name)
    {
        if (allDatatypes.ContainsKey(name))
        {
            return allDatatypes[name];
        }
        else
        {
            throw new Exception("could not find datatype " + name);
        }
    }

    public virtual void AddLemma(LemmaCall lemma)
    {
    }

    public virtual void AddMethodAsLemma(Method method)
    {
    }

    public virtual void WriteLemmas(TextWriter writer, CompileBase context, List<string> visibleModules, Attributes attrs,
        bool loopLemmasOnly = false)
    {
    }

    // This emits way overkill, as it doesn't exploit import inheritance.
    // But it's autogenerated code, so we don't care, I guess. --jonh
    public void WriteInterfaceImports(TextWriter writer, IEnumerable<string> importList)
    {
        foreach (string module in importList)
        {
			string importWord = "//private-import";
            writer.WriteLine("    "+importWord+" "+module+";");
        }
    }

    public IEnumerable<string> GatherAllImports(List<string> imports)
    {
        IEnumerable<string> stockImports = new string[] {
        "BaseSpec", "MemorySpec", "IoTypesSpec", "MachineStateSpec", "AssemblySpec", "InterruptsSpec", "IoSpec", "Overflow",
        "Core", "LogicalAddressing", "Util", "Stacks", "Partition", "Instructions", "Separation",
        "IntLemmasGc", "SimpleGcMemory", "SimpleCommon", "SimpleCollector",
        "IntLemmasMain", "IntLemmasBase", "IoMain"
        };
        return stockImports.Concat(imports);
    }

    public void WriteImplementationHeader(TextWriter writer, string name, List<string> imports)
    {
        writer.WriteLine("module implementation " + name);
        WriteInterfaceImports(writer, GatherAllImports(imports));
        writer.WriteLine("{");
    }

    // TODO: this should be based on attributes, not based on the name
    public bool IsSeqFile(string filename, bool spec)
    {
        return filename.EndsWith(spec ? @"\Seq.s.dfy" : @"\Seq.dfy");
    }

    // TODO: this should be based on attributes, not based on the name
    public bool IsSpecFile(string filename)
    {
        return filename.EndsWith(@".s.dfy");
    }

    public string ModuleNameFromFilename(string filename)
    {
        string suffix = Path.GetFileNameWithoutExtension(filename).Replace("-", "_").Replace(".", "_");
        return "dafny_" + suffix;
    }

    public void AddImports(Dictionary<string,string> imports, string filename)
    {
        Dictionary<string,string> myImports;
        if (!fileImports.ContainsKey(filename))
        {
            myImports = new Dictionary<string,string>(StringComparer.CurrentCultureIgnoreCase);
            StreamReader reader = new StreamReader(filename);
            while (true)
            {
                string line = reader.ReadLine();
                if (line == null)
                {
                    reader.Close();
                    break;
                }
                string[] tokens = line.Trim().Split(' ');
                if (tokens.Length >= 2 && tokens[0] == "include" && tokens[1].StartsWith("\"")
                    && tokens[1].EndsWith("\""))
                {
                    string imp = tokens[1].Substring(1, tokens[1].Length - 2).Replace('/', '\\');
                    if (filename.EndsWith(".s.dfy") && imp.EndsWith(".i.dfy"))
                    {
                        throw new Exception("specification " + filename + " includes implementation " + imp);
                    }
                    if (!Path.IsPathRooted(imp))
                    {
                        imp = Path.Combine(Path.GetDirectoryName(filename), imp);
                    }
                    imp = new FileInfo(imp).FullName;
                    AddImports(myImports, imp);
                    string moduleName = ModuleNameFromFilename(imp);
                    if (!myImports.ContainsKey(moduleName))
                    {
                        myImports.Add(moduleName, imp);
                    }
                }
            }
            fileImports.Add(filename, myImports);
        }
        myImports = fileImports[filename];
        foreach (var p in myImports)
        {
            if (!imports.ContainsKey(p.Key))
            {
                imports.Add(p.Key, p.Value);
            }
        }
    }

    public virtual Tuple<TextWriter,TextWriter,string,List<string>> ChooseOutDirWriter(string filename)
    {
        if (!outDirWriters.ContainsKey(filename))
        {
            string moduleName = ModuleNameFromFilename(filename);
            string baseName = Path.Combine(outDir, moduleName);
            TextWriter implWriter = new StreamWriter(baseName + ImpBasmExtn);
            TextWriter intfWriter = new StreamWriter(baseName + IfcBasmExtn);
            Dictionary<string,string> imports = new Dictionary<string,string>(StringComparer.CurrentCultureIgnoreCase);
            imports.Add("Trusted", "");
            if (moduleName != "dafny_DafnyPrelude")
            {
                imports.Add("dafny_DafnyPrelude", "");
				if (moduleName.EndsWith("_i"))
				{
					imports.Add("DafnyAssembly", "");
				}
            }
            AddImports(imports, filename);
            List<string> importModules = imports.Keys.ToList();
            if (outListWriter != null && moduleName != "dafny_DafnyPrelude")
            {
                outListWriter.WriteLine(moduleName + String.Concat(
                    imports.Where(x => x.Value != "").Select(x => " " + x.Key)));
            }
            WriteImplementationHeader(implWriter, moduleName, importModules);
			WriteInterfaceImports(intfWriter, GatherAllImports(importModules));
            intfWriter.WriteLine("module interface " + moduleName);
            intfWriter.WriteLine("{");
            outDirWriters.Add(filename, Tuple.Create(implWriter, intfWriter, moduleName, importModules));
            //- make sure each import gets a file:
            imports.Values.Where(x => x != "").ToList().ForEach(x => {ChooseOutDirWriter(x);});
        }
        return outDirWriters[filename];
    }

    public bool TrustedType(Type t)
    {
        SeqType seq = t as SeqType;
        UserDefinedType ut = t as UserDefinedType;
        if (seq != null)
        {
            return TrustedType(seq.Arg);
        }
        else if (ut != null)
        {
            return IsSpecFile(ut.AsDatatype.tok.filename) && TrustedType(ut.TypeArgs);
        }
        else
        {
            return true;
        }
    }

    public bool TrustedType(IEnumerable<Type> ts)
    {
        return ts.ToList().TrueForAll(t => TrustedType(t));
    }

    public virtual Tuple<TextWriter,TextWriter,string,List<string>> ChooseWriter(
        Bpl.IToken tok, string name, TypeApply app = null)
    {
        string filename = Path.GetFullPath(tok.filename);
        if (app != null && !TrustedType(app.typeArgs.Values))
        {
            throw new Exception("specification cannot refer to untrusted type: " + name);
        }
        if (IsSeqFile(filename, true))
        {
            return Tuple.Create(trustedWriter,
                (name.StartsWith("lemma_Seq") ? trustedWriter : trustedIWriter),
                "Trusted",
                new List<string>());
        }
        else
        {
            return ChooseOutDirWriter(filename);
        }
    }

    public void CompileDatatype1Ghost(Type t, TypeApply app, TextWriter writer, TextWriter iwriter)
    {
        // type List = Nil() | Cons(hd:int, tl:List);
        string dataName = app.AppName(); // List
        List<DatatypeCtor> ctors = compileDatatypes[app].AsDatatype.Ctors;
        bool isSeq = dataName.StartsWith("Seq_");
        if (isSeq)
        {
            iwriter.WriteLine("type " + dataName + ";");
        }
        (isSeq ? writer : iwriter).WriteLine(
            "type " + (isSeq ? "implementation" : "") + "{:overload} " + dataName + " = "
            + String.Join(" | ", ctors.Select(c => Compile_Constructor(t, c.Name, app.typeArgs).AppName() + "("
                + String.Join(", ", c.Formals.Select(f => f.Name + ":" + TypeString(app.AppType(f.Type))))
                + ")")) + ";");

        if (isSeq)
        {
            foreach (var c in ctors)
            {
                string cName = Compile_Constructor(t, c.Name, app.typeArgs).AppName();
                string args = String.Join(", ", c.Formals.Select(f => f.Name));
                string parms = String.Join(", ", c.Formals.Select(f => f.Name + ":" 
                    + TypeString(app.AppType(f.Type))));
                iwriter.WriteLine("function _" + cName + "(" + parms + "):" + dataName + ";");
                writer.WriteLine("function implementation _" + cName + "(" + parms + "):"
                    + dataName + " { " + cName + "(" + args + ") }");
                foreach (var f in c.Formals)
                {
                    string tName = TypeString(app.AppType(f.Type));
                    iwriter.WriteLine("function " + f.Name + "_" + cName + "(x:" + dataName
                        + "):" + tName + ";");
                    writer.WriteLine("function implementation " + f.Name + "_" + cName + "(x:" + dataName
                        + "):" + tName + " { " + f.Name + "#" + cName + "(x) }");
                }
                iwriter.WriteLine("function is_" + cName + "(x:" + dataName + "):bool;");
                writer.WriteLine("function implementation is_" + cName + "(x:" + dataName
                    + "):bool { x is " + cName + " }");
            }
        }
    }

    const string baseDecls = @"
        function fun_unroll(i:int):bool { true }
        function fun_unroll__all(i:int):bool { true }
        function fun_word__32(i:int):bool { word(i) }

        function INTERNAL_add_boogie(x:int, y:int) : int { x + y }
        function INTERNAL_sub_boogie(x:int, y:int) : int { x - y }
        function{:never_pattern true} INTERNAL_lt_boogie(x:int, y:int) : bool { x < y }
        function{:never_pattern true} INTERNAL_le_boogie(x:int, y:int) : bool { x <= y }
        function{:never_pattern true} INTERNAL_gt_boogie(x:int, y:int) : bool { x > y }
        function{:never_pattern true} INTERNAL_ge_boogie(x:int, y:int) : bool { x >= y }
    ";

    void CompileDatatypesGhost()
    {
        for (int i = 0; i < compileDatatypeList.Count; i++)
        {
            // note that compileDatatypes may get extended during loop
            var app = compileDatatypeList[i];
            CompileDatatype1Ghost(compileDatatypes[app], app, trustedWriter, trustedIWriter);
        }
    }

    public virtual CompileMethodGhost NewCompileMethod(DafnySpec dafnySpec, Method method,
        TypeApply typeApply, TextWriter writer, TextWriter iwriter, string moduleName, List<string> imports)
    {
        return new CompileMethodGhost(dafnySpec, method, typeApply, writer, iwriter, moduleName, imports);
    }

    public TypeApply Compile_Method(Method method, Dictionary<TypeParameter,Type> typeArgs, List<TypeParameter> extraTypeParams = null)
    {
        Dictionary<string,TypeParameter> substArgs = new Dictionary<string,TypeParameter>();
        var fullTypeArgs = method.TypeArgs.Concat(extraTypeParams ?? new List<TypeParameter>()).ToList();
        fullTypeArgs.ForEach(t => substArgs.Add(t.Name, t));
        typeArgs = typeArgs.ToDictionary(p => substArgs[p.Key.Name], p => p.Value);
        TypeApply apply = new TypeApply(this, DafnySpec.SanitizedName(method), fullTypeArgs, typeArgs);
        //Console.Error.WriteLine("Compile_Method: " + method + " :: " + method.GetType() + " " + String.Join(",", typeArgs));
        if (!compileMethods.ContainsKey(apply))
        {
            //Console.Error.WriteLine("Compile_Method# " + method + " :: " + method.GetType() + " " + String.Join(",", typeArgs));
            compileMethods.Add(apply, apply);
            var tok = method.tok;
            var writers = ChooseWriter(tok, method.Name, apply);
            CompileMethodGhost compile = NewCompileMethod(this, method, apply,
                writers.Item1, writers.Item2, writers.Item3, writers.Item4);
            if (writers.Item3 == "Seq" && typeArgs.Count == 1)
            {
                compile.visibleElementType = new List<Type>(apply.typeArgs.Values)[0];
            }
            compile.minVerify = minVerify;
            try
            {
                compile.Compile();
            }
            catch(Exception e)
            {
                throw new Exception("while compiling method " + method.Name, e);
            }
        }
        return apply;
    }

    public virtual void Compile_FunctionAsMethod(Function function, Dictionary<TypeParameter,Type> typeArgs,
        Dictionary<string,TypeParameter> substArgs)
    {
    }

    public TypeApply Compile_Function(Function function, Dictionary<TypeParameter,Type> typeArgs)
    {
        Dictionary<string,TypeParameter> substArgs = new Dictionary<string,TypeParameter>();
        function.TypeArgs.ForEach(t => substArgs.Add(t.Name, t));
        typeArgs = typeArgs.ToDictionary(p => substArgs[p.Key.Name], p => p.Value);
        TypeApply apply = new TypeApply(this, DafnySpec.SanitizedName(function), function.TypeArgs, typeArgs);
        if (!compileFunctions.ContainsKey(apply))
        {
            compileFunctions.Add(apply, apply);
            var tok = function.tok;
            //Console.Error.WriteLine("function: " + function + " :: " + function.GetType());
            //Console.Error.WriteLine("    " + function.Body);
            //Console.Error.WriteLine("    " + function.IsRecursive + " " + function.IsGhost);
            var writers = ChooseWriter(tok, function.Name, apply);
            if (!Attributes.Contains(function.Attributes, "imported"))
            {
                try
                {
                    var compile = new CompileFunction(this, function, apply, writers.Item1, writers.Item2,
                        writers.Item3, writers.Item4);
                    if (writers.Item3 == "Seq" && typeArgs.Count == 1)
                    {
                        compile.visibleElementType = new List<Type>(apply.typeArgs.Values)[0];
                    }
                    compile.minVerify = minVerify;
                    compile.Compile();
                }
                catch(Exception e)
                {
                    throw new Exception("while compiling function " + function.Name, e);
                }
            }
            else
            {
                // imported
                if (function.Ens.Count > 0)
                {
                    string name = FunName(SimpleName(apply.AppName()));
                    AddLemma(new LemmaCall(writers.Item3, (Type)null,
                        "call lemma_fun_ensures_" + name + "();", false));
                }
            }
            bool hidden = Attributes.Contains(function.Attributes, "opaque");
            bool isFull = function.Name.Contains("#") && function.Name.EndsWith("_FULL");
            if (!function.IsGhost && !isFull && !IsSpecFile(function.tok.filename))
            {
                Compile_FunctionAsMethod(function, typeArgs, substArgs);
            }
        }
        return apply;
    }

    public virtual void AddDatatypeLemmas(UserDefinedType t, TypeApply apply)
    {
    }

    public TypeApply Compile_Datatype(UserDefinedType t)
    {
        Dictionary<TypeParameter,Type> subst = new Dictionary<TypeParameter,Type>();
        for (int i = 0; i < t.TypeArgs.Count; i++)
        {
            subst.Add(t.AsDatatype.TypeArgs[i], t.TypeArgs[i]);
        }
        TypeApply apply = new TypeApply(this, t.Name, t.AsDatatype.TypeArgs, subst);
        if (   !compileDatatypes.ContainsKey(apply)
            && !Attributes.Contains(t.AsDatatype.Attributes, "imported"))
        {
            compileDatatypes.Add(apply, t);
            compileDatatypeList.Add(apply);
            AddDatatypeLemmas(t, apply);
        }
        return apply;
    }

    public TypeApply Compile_Constructor(Type t, string constructor, List<Type> dataTypeArgs,
        Dictionary<TypeParameter,Type> typeArgs)
    {
        UserDefinedType ut = (UserDefinedType) t;
        if (dataTypeArgs == null)
        {
            dataTypeArgs = ut.TypeArgs;
        }
        Util.Assert(ut.AsDatatype.TypeArgs.Count == dataTypeArgs.Count);
        Dictionary<TypeParameter,Type> typeMap = new Dictionary<TypeParameter,Type>();
        for (int i = 0; i < dataTypeArgs.Count; i++)
        {
            typeMap.Add(ut.AsDatatype.TypeArgs[i],
                Resolver.SubstType(dataTypeArgs[i], typeArgs));
        }
        return new TypeApply(this, constructor, ut.AsDatatype.TypeArgs, typeMap);
    }

    // REVIEW: is this receiving the correct typeArgs?
    public TypeApply Compile_Constructor(Type t, string constructor, Dictionary<TypeParameter,Type> typeArgs)
    {
        UserDefinedType ut = (UserDefinedType) t;
        Dictionary<string,TypeParameter> substArgs = new Dictionary<string,TypeParameter>();
        ut.AsDatatype.TypeArgs.ForEach(tt => substArgs.Add(tt.Name, tt));
        typeArgs = typeArgs.ToDictionary(p => substArgs[p.Key.Name], p => p.Value);
        return new TypeApply(this, constructor, ut.AsDatatype.TypeArgs, typeArgs);
    }

    public TypeApply Compile_SeqType(SeqType t)
    {
        Dictionary<TypeParameter,Type> typeArgs = new Dictionary<TypeParameter,Type>();
        DatatypeDecl decl = FindDatatype("Seq");
        return Compile_Datatype(new UserDefinedType(Bpl.Token.NoToken, "Seq", decl, new List<Type> { t.Arg }));
    }

    public Tuple<Function,TypeApply> GetSeqOperation(Type t, string op)
    {
        Function f = FindFunction(op);
        TypeApply tApp = Compile_SeqType((SeqType)t);
        return Tuple.Create(f, Compile_Function(f, tApp.typeArgs));
    }

    public string GetSeqOperationName(Type t, string op)
    {
        TypeApply tApp = Compile_SeqType((SeqType)t);
        TypeApply fApp = Compile_Function(FindFunction(op), tApp.typeArgs);
        return FunName(SimpleName(GetSeqOperation(t, op).Item2.AppName()));
    }

    public Tuple<Method,TypeApply> GetSeqMethod(Type t, string op)
    {
        Method m = FindMethod(op);
        TypeApply tApp = Compile_SeqType((SeqType)t);
        return Tuple.Create(m, Compile_Method(m, tApp.typeArgs));
    }

    public Dictionary<string,string> CompileSpecStart(DafnySpec_Options options, IList<string> files)
    {
        minVerify = options.minVerify;
        outDir = options.outDir;
        outListWriter = new StreamWriter(Path.Combine(outDir, "dafny_modules.txt"));

        trustedWriter = new StreamWriter(Path.Combine(outDir, "Trusted"+ImpBasmExtn));
        trustedIWriter = new StreamWriter(Path.Combine(outDir, "Trusted"+IfcBasmExtn));
        WriteInterfaceImports(trustedIWriter, GatherAllImports(new List<string>()));
        trustedIWriter.WriteLine("module interface Trusted");
        trustedIWriter.WriteLine("{");
        trustedIWriter.WriteLine(baseDecls);
        WriteImplementationHeader(trustedWriter, "Trusted", new List<string>());

        Dictionary<string, string> allModules = new Dictionary<string, string>(StringComparer.CurrentCultureIgnoreCase);
        foreach (string file in files)
        {
            string filename = new FileInfo(file).FullName;
            string moduleName = ModuleNameFromFilename(filename);
            if (!allModules.ContainsKey(moduleName))
            {
                AddImports(allModules, filename);
                allModules.Add(moduleName, filename);
            }
        }
        return allModules;
    }

    public void CompileSpecEnd()
    {
        trustedIWriter.WriteLine("}");
        trustedWriter.WriteLine("}");
        trustedIWriter.Close();
        trustedWriter.Close();

        foreach (var writers in outDirWriters.Values)
        {
            writers.Item1.WriteLine("}");
            writers.Item1.Close();
            writers.Item2.WriteLine("}");
            writers.Item2.Close();
        }
        if (outListWriter != null)
        {
            outListWriter.Close();
        }
    }

    public void DeclareProgram(Program program)
    {
        foreach (ModuleDefinition mod in program.Modules)
        {
            foreach (TopLevelDecl top in mod.TopLevelDecls)
            {
                ClassDecl cls = top as ClassDecl;
                DatatypeDecl dataDecl = top as DatatypeDecl;
                if (cls != null)
                {
                    foreach (MemberDecl member in cls.Members)
                    {
                        Method method = member as Method;
                        Function function = member as Function;
                        if (method != null && !allMethods.ContainsKey(method.Name))
                        {
                            allMethods[method.Name] = method;
                        }
                        if (function != null && !allFunctions.ContainsKey(function.Name))
                        {
                            allFunctions[function.Name] = function;
                        }
                    }
                }
                if (dataDecl != null && !allDatatypes.ContainsKey(dataDecl.Name))
                {
                    allDatatypes[dataDecl.Name] = dataDecl;
                }
            }
        }
    }

    public void CompileProgram(Program program)
    {
        foreach (ModuleDefinition mod in program.Modules)
        {
            Util.DebugWriteLine("module: " + mod.Name + " " + mod.GetType());
            
            //Console.WriteLine("type Tri = Triple(Pwd:int, Salt:int, Key:int);");
            //Console.WriteLine("type Map = MapCons(Domain:[Tri]bool, Range:[Tri]int);");
            //Console.WriteLine("var $ghost_Hashed:Map;");

            foreach (TopLevelDecl top in mod.TopLevelDecls)
            {
                Util.DebugWriteLine("top-decl: " + top.Name + " " + top.GetType());
                ClassDecl cls = top as ClassDecl;
                
                if (cls != null)
                {
                    foreach (MemberDecl member in cls.Members)
                    {
                        //Console.Error.WriteLine("declaration: " + member + " :: " + member.GetType());
                        Util.DebugWriteLine("member-decl: " + member.Name + " " + member.GetType());
                        Field field = member as Field;
                        Method method = member as Method;
                        Function function = member as Function;
                        if (field != null && !allStaticFields.Contains(field.Name))
                        {
                            allStaticFields.Add(field.Name);
                            if (!field.IsGhost)
                            {
                                throw new Exception("not implemented: non-ghost fields: " + field.Name);
                            }
                            var writers = ChooseWriter(field.tok, field.Name);
                            new CompileField(this, field, writers.Item2).Compile();
                        }
                        if (method != null && method.TypeArgs.Count == 0)
                        {
                            if (method.Body == null)
                            {
                                //Console.Error.WriteLine("declaration: " + member + " :: " + member.GetType());
                            }
                            Compile_Method(method, new Dictionary<TypeParameter,Type>());
                            AddMethodAsLemma(method);
                        }
                        else if (function != null && function.TypeArgs.Count == 0)
                        {
                            Compile_Function(function, new Dictionary<TypeParameter,Type>());
                        }
                        else
                        {
                            //Console.Error.WriteLine("skipping declaration: " + member + " :: " + member.GetType());
                        }
                    }
                }
            }
        }
    }

    public void CompileSequenceSpecs()
    {
        Compile_Function(FindFunction("dummy_seqs"), new Dictionary<TypeParameter,Type>());
        List<Function> seqFunctions = allFunctions.Values.Where(f => IsSeqFile(f.tok.filename, true)).ToList();
        List<Method> seqMethods = allMethods.Values.Where(m => IsSeqFile(m.tok.filename, true)).ToList();

        for (int i = 0; i < compileDatatypeList.Count; i++)
        {
            //- note that compileDatatypes may get extended during loop
            var app = compileDatatypeList[i];
            string dataName = app.AppName(); // List
            List<DatatypeCtor> ctors = compileDatatypes[app].AsDatatype.Ctors;
            bool isSeq = dataName.StartsWith("Seq_");
            if (isSeq)
            {
                seqFunctions.ForEach(f => Compile_Function(f, app.typeArgs));
                seqMethods.ForEach(m => Compile_Method(m, app.typeArgs));
            }
        }
    }

    public void CompileSpec(DafnySpec_Options options, IList<string> files)
    {
        Dictionary<string,string> allModules = CompileSpecStart(options, files);

        Program program;
        string errors = Microsoft.Dafny.Main.ParseCheck(
            allModules.Values.ToList(),
            "DAFNYCC_PROGRAM",
            out program);
        if (errors != null)
        {
            throw new Exception(errors);
        }
        Util.DebugWriteLine(program);
        DeclareProgram(program);
        CompileProgram(program);
        CompileDatatypesGhost();
        CompileSequenceSpecs();
        files.ToList().ForEach(f => ChooseOutDirWriter(f)); //- make sure even empty modules get written

        CompileSpecEnd();
    }
}

