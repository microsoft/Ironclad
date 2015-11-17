using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using Type = Microsoft.Dafny.Type;
using System.Numerics;

public class DafnyCC_Options: DafnySpec_Options
{
    public bool relational;
    public bool x64 = false; 
    public bool useFramePointer = false;

    protected override bool ParseOption(string name, Bpl.CommandLineOptionEngine.CommandLineParseState ps)
    {
        switch (name) {
            case "relational":
                relational = true;
                return true;
            case "x64":
                x64 = true;
                return true;
            case "useFramePointer":
                useFramePointer = true;
                return true;
            default:
                break;
        }
        return base.ParseOption(name, ps);
    }
}

public class DafnyCC: DafnySpec
{
    TextWriter heapWriter = null;
    TextWriter heapIWriter = null;
    TextWriter checkedWriter = null;
    TextWriter checkedIWriter = null;
    TextWriter seqWriter = null;
    TextWriter seqIWriter = null;
    TextWriter mainWriter = Console.Out;
    public bool relational = false;

    public bool x64 = false;
    public bool useFramePointer = false;
    public int IPSize;
    public int framePointerCount = 0;

    public List<LemmaCall> lemmas = new List<LemmaCall>
        {
            new LemmaCall("Heap", (Type)null, "assert fun_unroll(0);", false),
            new LemmaCall("Heap", (Type)null, "assert fun_unroll(1);", false),
        };

    public List<string> lazyLemmas = new List<string>
        {
            "Seq_FromArray_Length",
            "Seq_FromArray_Index",
            "Seq_FromArray_Update",
        };

    public List<string> seqLemmas = new List<string>
        {
            "Seq_Empty_ToZero",
            "Seq_Empty_FromZero",
            "Seq_Singleton_Length",
            "Seq_Build_Length",
            "Seq_Build_Index",
            "Seq_Append_Length",
            "Seq_Index_Singleton",
            "Seq_Append_Index",
            "Seq_Update_Length",
            "Seq_Index_Update",
            "Seq_Equal_Equiv",
            "Seq_Take_Length",
            "Seq_Take_Index",
            "Seq_Drop_Length",
            "Seq_Drop_Index",
            "Seq_Append_TakeDrop",
            "Seq_Append_TakeDrop_Restricted",
            "Seq_Update_CommuteTake1",
            "Seq_Update_CommuteTake2",
            "Seq_Update_CommuteDrop1",
            "Seq_Update_CommuteDrop2",
            "Seq_Build_CommuteDrop",
            "Seq_Take_Empty",
            "Seq_Drop_Empty",
        };

    public static new void Main(string[] args)
    {
        try
        {
            Util.DebugWriteLine("hello");
            DafnyCC_Options options = new DafnyCC_Options();            
            DafnyOptions.Install(options);
            DafnyOptions.O.AllowGlobals = true;
            DafnyOptions.O.Dafnycc = true;
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
            if (options.useFramePointer && options.x64)
            {
                throw new Exception("64-bit frame pointer not yet implemented");
            }
            new DafnyCC().CompileCode(options, files);
        }
        catch (Exception e)
        {
            Console.OpenStandardOutput().Flush();
            Console.WriteLine(e);
            Console.Error.WriteLine(e);
            Environment.Exit(-1);
        }
    }

    public static string ProcName(bool isGhost, string x) { return (isGhost ? "proc_" : "Proc_") + CleanName(x); }

    public static string PreserveHeap(bool minVerify, List<string> mods, string absMem = "$absMem",
        string absMemOld = "$absMem_old", string heap = "heap", string heap_old = "heap_old")
    {
        return "(forall i:int::{" + absMem + "[i]}{" + heap + ".absData[i]} " + heap_old + ".absData[i] is AbsNone"
            + " || (" + heap + ".absData[i] == " + heap_old + ".absData[i]"
                + " && (" + absMem + "[i] == " + absMemOld + "[i]"
                    + (minVerify
                        ? " || " + heap_old + ".absData[i] is Abs_ArrayOfInt"
                        : String.Concat(mods.Select(s => " || i == (" + s +")"))) + ")))";
    }

    public static string PreserveHeap(bool minVerify)
    {
        return PreserveHeap(minVerify, new List<string>());
    }

    public override void AddLemma(LemmaCall lemma)
    {
        lemmas.Add(lemma);
    }

    public override void AddMethodAsLemma(Method method)
    {
        if (lazyLemmas.Contains(method.Name))
        {
            lazyLemmas.Remove(method.Name);
            lemmas.Add(new LemmaCall("Seq", (Type)null,
                "call " + ProcName(true, DafnySpec.SimpleSanitizedName(method)) + "();",
                Attributes.Contains(method.Attributes, "loop_lemma")));
        }
    }

    public override void WriteLemmas(TextWriter writer, CompileBase context, List<string> visibleModules, Attributes attrs,
        bool loopLemmasOnly = false)
    {
        if (minVerify)
        {
            return;
        }
        if (!Attributes.Contains(attrs, "dafnycc_no_lemmas"))
        {
            foreach (var x in lemmas.Where(x => visibleModules.Contains(x.module)))
            {
                if (x.type != null && context.visibleElementType != null
                    && x.type.ToString() != context.visibleElementType.ToString())
                {
                    continue;
                }
                if (loopLemmasOnly && !x.loopLemma) {
                    continue;
                }
                string line = x.stmt;
                if (line.Contains("Seq__Append__TakeDrop"))
                {
                    bool isRestricted = line.Contains("Seq__Append__TakeDrop__Restricted");
                    bool isConservative = Attributes.Contains(attrs, "dafnycc_conservative_seq_triggers");
                    if (isConservative != isRestricted)
                    {
                        continue;
                    }
                }
                writer.WriteLine("    " + line);
            }
        }
    }

/* TODO: reduce number of imports for specs
    public void WriteImplementationHeader(TextWriter writer, string name, List<string> imports)
    {
        writer.WriteLine("module implementation " + name);
        writer.WriteLine("    import BaseSpec, MemorySpec, IoTypesSpec, MachineStateSpec, AssemblySpec, InterruptsSpec, IoSpec, OverflowSpec;");
        writer.WriteLine("    import Core, LogicalAddressing, Util, Stacks, Partition, Separation;");
        writer.WriteLine("    import IntLemmasGc, GcMemory, Common, GcCollector;");
        writer.WriteLine("    import IntLemmasMain, IntLemmasBase, IoMain" + String.Join("", imports.Select(s => ", " + s)) + ";");
        writer.WriteLine("{");
    }
*/

    private void WriteAxiomAnnotations(TextWriter writer, IEnumerable<string> axioms)
    {
		foreach (string axiom in axioms)
		{
			writer.WriteLine("//<NuBuild AddBoogieAxiom "+axiom+"_axioms />");
		}
    }

    
    public override Tuple<TextWriter,TextWriter,string,List<string>> ChooseOutDirWriter(string filename)
    {
        if (outDir == null)
        {
            throw new Exception("It would be nice to specify outDir");
        }
        if (!outDirWriters.ContainsKey(filename))
        {
            string moduleName = ModuleNameFromFilename(filename);
            string baseName = Path.Combine(outDir, moduleName);
            TextWriter implWriter = new StreamWriter(baseName + ImpBasmExtn);
            TextWriter intfWriter = new StreamWriter(baseName + IfcBasmExtn);
            Dictionary<string,string> imports = new Dictionary<string,string>(StringComparer.CurrentCultureIgnoreCase);
            imports.Add("Trusted", "");
            imports.Add("Checked", "");
            imports.Add("Heap", "");
            imports.Add("Seq", "");
            if (moduleName != "dafny_DafnyPrelude")
            {
                imports.Add("dafny_DafnyPrelude", "");
                imports.Add("DafnyAssembly", "");
            }
            AddImports(imports, filename);
            List<string> importModules = imports.Keys.ToList();
            if (outListWriter != null && moduleName != "dafny_DafnyPrelude")
            {
                outListWriter.WriteLine(moduleName + String.Concat(
                    imports.Where(x => x.Value != "").Select(x => " " + x.Key)));
            }
            WriteImplementationHeader(implWriter, moduleName, importModules);
			WriteAxiomAnnotations(implWriter,
				new string[] { "Assembly", "Base", "Memory", "Word", "Io"});
				
			
            intfWriter.WriteLine("module interface " + moduleName);
            WriteInterfaceImports(intfWriter, GatherAllImports(importModules));
            intfWriter.WriteLine("{");
            outDirWriters.Add(filename, Tuple.Create(implWriter, intfWriter, moduleName, importModules));
            
            imports.Values.Where(x => x != "").ToList().ForEach(x => {ChooseOutDirWriter(x);});
        }
        return outDirWriters[filename];
    }


    
    public override Tuple<TextWriter,TextWriter,string,List<string>> ChooseWriter(
        Bpl.IToken tok, string name, TypeApply app = null)
    {
        string filename = Path.GetFullPath(tok.filename);
        bool trustedArg = (app != null && app.typeArgs.Count == 1 && TrustedType(app.typeArgs.Values));
        if (IsSeqFile(filename, true))
        {
            return Tuple.Create(trustedArg ? trustedWriter : checkedWriter,
                (name.StartsWith("lemma_Seq") ? (trustedArg ? trustedWriter : checkedWriter)
                    : (trustedArg ? trustedIWriter : checkedIWriter)),
                trustedArg ? "Trusted" : "Checked",
                trustedArg ? new List<string>() : new List<string> { "Trusted" });
        }
        else if (IsSeqFile(filename, false))
        {
            return Tuple.Create(seqWriter,
                (name.StartsWith("lemma_Seq") ? seqWriter : seqIWriter),
                "Seq",
                new List<string> { "Trusted", "Checked", "Heap" });
        }
        else
        {
            return ChooseOutDirWriter(filename);
        }
    }

    void CompileDatatype1Code(Type t, TypeApply app)
    {
        
        string dataName = app.AppName(); 
        List<DatatypeCtor> ctors = compileDatatypes[app].AsDatatype.Ctors;
        bool isSeq = dataName.StartsWith("Seq_");

        
        
        for (int i = 0; i < ctors.Count; i++)
        {
            heapIWriter.WriteLine("const Tag_" + dataName + "_" + ctors[i].Name + ":int := " + (i + 1) + ";");
        }

        
        
        
        
        
        
        heapWriter.WriteLine("function HeapWordInv_" + dataName + "(absData:[int]AbsData, objLayout:ObjLayout, wordMem:[int]int, data:" + dataName + "):bool");
        heapWriter.WriteLine("{");
        heapWriter.WriteLine("    true");

        foreach (var ctor in ctors)
        {
            var ints = ctor.Formals.Where(x => !IsPtrType(app.AppType(x.Type))).ToList();
            var ptrs = ctor.Formals.Where(x =>  IsPtrType(app.AppType(x.Type))).ToList();
            var sorted = ints.Concat(ptrs).ToList();
            string ctorName = Compile_Constructor(t, ctor.Name, app.typeArgs).AppName();

            
            
            string wordMems = "";
            for (int i = 0; i < sorted.Count; i++)
            {
                heapIWriter.WriteLine("const Offset_" + dataName + "_" + sorted[i].Name + ":int := " + (8 + 4 * i) + ";");
                if (IsPtrType(app.AppType(sorted[i].Type)))
                {
                    wordMems += " && absData[wordMem[" + (3 + i) + "]] == Abs_"
                        + TypeString(app.AppType(sorted[i].Type)) + "(" + sorted[i].Name
                        + (isSeq ? "_" : "#") + ctorName + "(data))";
                }
                else
                {
                    wordMems += " && " + CompileBase.IntEqTyped(
                        app.AppType(sorted[i].Type),
                        sorted[i].Name + (isSeq ? "_" : "#") + ctorName + "(data)",
                        "wordMem[" + (3 + i) + "]");
                }
            }

            
            string dataIs = isSeq ? ("is_" + ctorName + "(data)") : "data is " + ctorName;
            heapWriter.WriteLine("&& (" + dataIs + " ==> objLayout == ObjLayout("
                + (3 + sorted.Count) + ", " + (3 + ints.Count)
                + ") && wordMem[2] == Tag_" + dataName + "_" + ctor.Name + wordMems + ")");
        }

        heapWriter.WriteLine("}");
    }

    void CompileDatatype1(Type t, TypeApply app)
    {
        
        string dataName = app.AppName(); 
        List<DatatypeCtor> ctors = compileDatatypes[app].AsDatatype.Ctors;
        bool isSeq = dataName.StartsWith("Seq_");
        bool isTrusted = isSeq ? TrustedType(app.typeArgs.Values) : TrustedType(t);

        CompileDatatype1Ghost(t, app,
            isTrusted ? trustedWriter : checkedWriter,
            isTrusted ? trustedIWriter : checkedIWriter);
        CompileDatatype1Code(t, app);
    }

    string loadTagDecl(String List, String tags)
    {  
        return String.Format(@"
        atomic procedure loadTag_{0}(my r_old:regs, const my core_state:core_state, const linear stk:mem, const linear statics:mem, const linear io:IOState, linear mems_old:mems, $commonVars:commonVars, $gcVars:gcVars, $toAbs:[int]int, $absMem:[int][int]int, $stacksFrames:[int]Frames, objLayouts:[int]ObjLayout, heap:Heap, x:int, y:opn_mem, data:{0}, abs:int, obj:int)
          returns(my r:regs, linear mems:mems);
          requires MemInv(me,init,stk,statics,core_state,ptMem,mems_old);
          requires isStack($S);
          requires NucleusInv(objLayouts,$S,$toAbs,$absMem,$commonVars,$gcVars,me,init,stk,statics,core_state,ptMem,mems_old,$stacksFrames,io);
          requires HeapInv($absMem, objLayouts, heap);
          requires HeapAbsData(heap, abs) == Abs_{0}(data);
          requires HeapValue(objLayouts, true, $toAbs, obj, abs);
          requires EvalPtrOk(y);
          requires EvalPtr(r_old, y) == obj + 4;
          ensures  mems == mems_old;
          ensures  r.regs == r_old.regs[x := r.regs[x]];
          ensures  {1};", List, tags);
    }

    string allocDecl1(string list, string cons, string _cons, string Params, string args, string argRet)
    {
        return @"
        procedure Proc_Alloc_" + cons + @"(my r_old:regs, const my core_state:core_state, linear stk_old:mem, linear statics_old:mem, linear io_old:IOState, linear mems_old:mems, $commonVars_old:commonVars, $gcVars_old:gcVars, $toAbs_old:[int]int, $absMem_old:[int][int]int, $stacksFrames_old:[int]Frames, objLayouts_old:[int]ObjLayout, heap_old:Heap, data:" + list + @", " + Params + @")
          returns(my r:regs, linear stk:mem, linear statics:mem, linear io:IOState, linear mems:mems, $commonVars:commonVars, $gcVars:gcVars, $toAbs:[int]int, $absMem:[int][int]int, $stacksFrames:[int]Frames, objLayouts:[int]ObjLayout, heap:Heap, data_out:" + list + @");
          requires MemInv(me,init,stk_old,statics_old,core_state,ptMem,mems_old);
          requires isStack($S);
          requires NucleusInv(objLayouts_old,$S,$toAbs_old,$absMem_old,$commonVars_old,$gcVars_old,me,init,stk_old,statics_old,core_state,ptMem,mems_old,$stacksFrames_old,io_old);
          requires SMemRequireGcRA(256, " + argRet + @", stk_old, r_old.regs[ESP], RET);
          requires HeapInv($absMem_old, objLayouts_old, heap_old);
          
    ";
    }

    string allocDecl2(string list, string cons, string preserve, string args)
    {
        return @"
          modifies $Time;
          ensures  MemInv(me,init,stk,statics,core_state,ptMem,mems);
          ensures  NucleusInv(objLayouts,$S,$toAbs,$absMem,$commonVars,$gcVars,me,init,stk,statics,core_state,ptMem,mems,$stacksFrames,io);
          ensures  SMemEnsureGcF(4, stk, old(stk_old), r.regs[ESP], old(r_old.regs[ESP]), $stacksFrames, $stacksFrames_old);
          ensures  HeapInv($absMem, objLayouts, heap);
          ensures  AbsExtend($toAbs, $toAbs_old, objLayouts, objLayouts_old);
          ensures  io._inCtr == io_old._inCtr && io._outCtr == io_old._outCtr;
          ensures  heap_old.absData[frameGet($stacksFrames, r.regs[ESP] + stackGcOffset)] is AbsNone;
          ensures  StackAbsSlot(heap, $stacksFrames, r.regs[ESP] + stackGcOffset) == Abs_" + list + @"(data_out);
          ensures  data_out == " + cons + @"(" + args + @");
          ensures  " + preserve + @";
    ";
    }

    string allocDeclArray(int IPSize, string preserve)
    {
        return @"
        const stack_size__DafnyCC__Proc_AllocArrayOfInt:int := 256;
        procedure Proc_AllocArrayOfInt(my r_old:regs, const my core_state:core_state, linear stk_old:mem, linear statics_old:mem, linear io_old:IOState, linear mems_old:mems, $commonVars_old:commonVars, $gcVars_old:gcVars, $toAbs_old:[int]int, $absMem_old:[int][int]int, $stacksFrames_old:[int]Frames, objLayouts_old:[int]ObjLayout, heap_old:Heap, count:int)
          returns(my r:regs, linear stk:mem, linear statics:mem, linear io:IOState, linear mems:mems, $commonVars:commonVars, $gcVars:gcVars, $toAbs:[int]int, $absMem:[int][int]int, $stacksFrames:[int]Frames, objLayouts:[int]ObjLayout, heap:Heap, data:ArrayOfInt);
          requires MemInv(me,init,stk_old,statics_old,core_state,ptMem,mems_old);
          requires isStack($S);
          requires NucleusInv(objLayouts_old,$S,$toAbs_old,$absMem_old,$commonVars_old,$gcVars_old,me,init,stk_old,statics_old,core_state,ptMem,mems_old,$stacksFrames_old,io_old);
          requires SMemRequireGcRA(256, 4, stk_old, r_old.regs[ESP], RET);
          requires HeapInv($absMem_old, objLayouts_old, heap_old);
          requires stk_old.map[r_old.regs[ESP] + " + IPSize + @"] == count;
          modifies $Time;
          ensures  MemInv(me,init,stk,statics,core_state,ptMem,mems);
          ensures  NucleusInv(objLayouts,$S,$toAbs,$absMem,$commonVars,$gcVars,me,init,stk,statics,core_state,ptMem,mems,$stacksFrames,io);
          ensures  SMemEnsureGcF(4, stk, old(stk_old), r.regs[ESP], old(r_old.regs[ESP]), $stacksFrames, $stacksFrames_old);
          ensures  HeapInv($absMem, objLayouts, heap);
          ensures  " + preserve + @";
          ensures  AbsExtend($toAbs, $toAbs_old, objLayouts, objLayouts_old);
          ensures  io._inCtr == io_old._inCtr && io._outCtr == io_old._outCtr;
          ensures  data.arrCount == count;
          ensures  data.arrAbs == frameGet($stacksFrames, r.regs[ESP] + stackGcOffset);
          ensures  heap_old.absData[data.arrAbs] is AbsNone;
          ensures  StackAbsSlot(heap, $stacksFrames, r.regs[ESP] + stackGcOffset) == Abs_ArrayOfInt(data);
    ";
    }

    string loadField(string list, string dataIsCons, string tl)
    {
        return @"
        atomic procedure loadField_" + list + "_" + tl + @"(my r_old:regs, const my core_state:core_state, const linear stk:mem, const linear statics:mem, const linear io:IOState, linear mems_old:mems, $commonVars_old:commonVars, $gcVars_old:gcVars, $toAbs_old:[int]int, $absMem_old:[int][int]int, $stacksFrames_old:[int]Frames, objLayouts_old:[int]ObjLayout, heap:Heap, x:int, y:opn_mem, data:" + list + @", abs:int, obj:int)
          returns(my r:regs, linear mems:mems);
          requires MemInv(me,init,stk,statics,core_state,ptMem,mems_old);
          requires isStack($S);
          requires NucleusInv(objLayouts_old,$S,$toAbs_old,$absMem_old,$commonVars_old,$gcVars_old,me,init,stk,statics,core_state,ptMem,mems_old,$stacksFrames_old,io);
          requires HeapInv($absMem_old, objLayouts_old, heap);
          requires HeapAbsData(heap, abs) == Abs_" + list + @"(data);
          requires HeapValue(objLayouts_old, true, $toAbs_old, obj, abs);
          requires " + dataIsCons + @";
          requires EvalPtrOk(y);
          requires EvalPtr(r_old, y) == obj + Offset_" + list + "_" + tl + @";
          ensures  mems == mems_old;
          ensures  r.regs == r_old.regs[x := r.regs[x]];
    ";
    }

    string arrayElementProperties()
    {
        return @"
        atomic procedure arrayElementProperties(const my core_state:core_state, const linear stk:mem, const linear statics:mem, const linear io:IOState, const linear mems_old:mems, $commonVars_old:commonVars, $gcVars_old:gcVars, $toAbs_old:[int]int, $absMem_old:[int][int]int, $stacksFrames_old:[int]Frames, objLayouts_old:[int]ObjLayout, heap:Heap, index:int, abs:int, obj:int);
          requires MemInv(me,init,stk,statics,core_state,ptMem,mems_old);
          requires isStack($S);
          requires NucleusInv(objLayouts_old,$S,$toAbs_old,$absMem_old,$commonVars_old,$gcVars_old,me,init,stk,statics,core_state,ptMem,mems_old,$stacksFrames_old,io);
          requires HeapInv($absMem_old, objLayouts_old, heap);
          requires HeapAbsData(heap, abs) is Abs_ArrayOfInt;
          requires (0 - 1 == index) || (0 <= index && index < HeapAbsData(heap, abs).arr.arrCount);
          requires HeapValue(objLayouts_old, true, $toAbs_old, obj, abs);
          ensures  word(obj + 4 * (2 + index));
          ensures  abs == HeapAbsData(heap, abs).arr.arrAbs;
    ";
    }

    string loadArrayElement()
    {
        return @"
        atomic procedure loadArrayElement(my r_old:regs, const my core_state:core_state, const linear stk:mem, const linear statics:mem, const linear io:IOState, linear mems_old:mems, $commonVars_old:commonVars, $gcVars_old:gcVars, $toAbs_old:[int]int, $absMem_old:[int][int]int, $stacksFrames_old:[int]Frames, objLayouts_old:[int]ObjLayout, heap:Heap, x:int, y:opn_mem, index:int, abs:int, obj:int)
          returns(my r:regs, linear mems:mems);
          requires MemInv(me,init,stk,statics,core_state,ptMem,mems_old);
          requires isStack($S);
          requires NucleusInv(objLayouts_old,$S,$toAbs_old,$absMem_old,$commonVars_old,$gcVars_old,me,init,stk,statics,core_state,ptMem,mems_old,$stacksFrames_old,io);
          requires HeapInv($absMem_old, objLayouts_old, heap);
          requires HeapAbsData(heap, abs) is Abs_ArrayOfInt;
          requires (0 - 1 == index) || (0 <= index && index < HeapAbsData(heap, abs).arr.arrCount);
          requires HeapValue(objLayouts_old, true, $toAbs_old, obj, abs);
          requires EvalPtrOk(y);
          requires EvalPtr(r_old, y) == obj + 4 * (2 + index);
          ensures  abs == HeapAbsData(heap, abs).arr.arrAbs;
          ensures  mems == mems_old;
          ensures  r.regs == r_old.regs[x := r.regs[x]];
          ensures  r.regs[x] == if index >= 0 then fun_INTERNAL__array__elems__index($absMem_old[abs], index) else HeapAbsData(heap, abs).arr.arrCount;
          ensures  r.efl == r_old.efl;
          ensures  word(r.regs[x]);
    ";
    }

    string storeArrayElement()
    {
        return @"
        atomic procedure storeArrayElement(const my r:regs, const my core_state:core_state, const linear stk:mem, const linear statics:mem, const linear io:IOState, linear mems_old:mems, $commonVars_old:commonVars, $gcVars_old:gcVars, $toAbs_old:[int]int, $absMem_old:[int][int]int, $stacksFrames_old:[int]Frames, objLayouts_old:[int]ObjLayout, heap:Heap, x:opn_mem, y:opn, index:int, val:int, abs:int, obj:int)
          returns(linear mems:mems, absMem:[int][int]int);
          requires MemInv(me,init,stk,statics,core_state,ptMem,mems_old);
          requires isStack($S);
          requires NucleusInv(objLayouts_old,$S,$toAbs_old,$absMem_old,$commonVars_old,$gcVars_old,me,init,stk,statics,core_state,ptMem,mems_old,$stacksFrames_old,io);
          requires HeapInv($absMem_old, objLayouts_old, heap);
          requires HeapAbsData(heap, abs) is Abs_ArrayOfInt;
          requires 0 <= index && index < HeapAbsData(heap, abs).arr.arrCount;
          requires HeapValue(objLayouts_old, true, $toAbs_old, obj, abs);
          requires word(val);
          requires EvalPtrOk(x);
          requires EvalPtr(r, x) == obj + 4 * (2 + index);
          requires SrcOk(y);
          requires val == Eval(r, y);
          ensures  NucleusInv(objLayouts_old,$S,$toAbs_old,absMem,$commonVars_old,$gcVars_old,me,init,stk,statics,core_state,ptMem,mems,$stacksFrames_old,io);
          ensures  HeapInv(absMem, objLayouts_old, heap);
          ensures  tcb#mems(mems)==tcb#mems(mems_old);
          ensures  pci#mems(mems)==pci#mems(mems_old);
          ensures  frm#mems(mems)==frm#mems(mems_old);
          ensures  dat#mems(mems)==dat#mems(mems_old);
          ensures  abs == HeapAbsData(heap, abs).arr.arrAbs;
          ensures  absMem == fun_INTERNAL__array__update($absMem_old, HeapAbsData(heap, abs).arr, index, val);
          ensures  (forall i:int::{fun_INTERNAL__array__elems__index(absMem[abs], i)} i != index ==> fun_INTERNAL__array__elems__index(absMem[abs], i) == fun_INTERNAL__array__elems__index($absMem_old[abs], i));
    ";
    }

    string allocImpl1(string list, string con, string cons, string _cons, string Params, string args, string size, string sizeInts, string triggers, string seqLemma)
    {
        return @"
        implementation Proc_Alloc_" + cons + @"(my r_old:regs, const my core_state:core_state, linear stk_old:mem, linear statics_old:mem, linear io_old:IOState, linear mems_old:mems, $commonVars_old:commonVars, $gcVars_old:gcVars, $toAbs_old:[int]int, $absMem_old:[int][int]int, $stacksFrames_old:[int]Frames, objLayouts_old:[int]ObjLayout, heap_old:Heap, data:" + list + @", " + Params + @")
          returns(my r:regs, linear stk:mem, linear statics:mem, linear io:IOState, mems:mems, $commonVars:commonVars, $gcVars:gcVars, $toAbs:[int]int, $absMem:[int][int]int, $stacksFrames:[int]Frames, objLayouts:[int]ObjLayout, heap:Heap, data_out:" + list + @")
        {
          var abs:int;
          var _mem:[int]int;
          var obj:int;

          r := r_old;
          stk := stk_old;
          statics := statics_old;
          io := io_old;
          mems := mems_old;
          $commonVars := $commonVars_old;
          $gcVars := $gcVars_old;
          $toAbs := $toAbs_old;
          $absMem := $absMem_old;
          $stacksFrames := $stacksFrames_old;
          objLayouts := objLayouts_old;
          heap := heap_old;
          data_out := " + _cons + "(" + args + @");
          assert THeapInv($absMem, objLayouts, heap);
          " + seqLemma + @"

          assert TV(r.regs[ESP]) && " + triggers + @" && TO(0 - 1) && TO(0 - 2) && TO(0 - 3);          
          call r := logical_Sub(r, ESP, OConst(12));

          call heap, abs := freshAbs(?gcHi, $toAbs, heap);
          call r := instr_Mov(r, EBP, OConst(0));

          call r := instr_Mov(r, ECX, OConst(" + size + @"));
          call stk := logical_Store(r, core_state, stk, OMem(MReg(ESP,4)), OReg(ECX));

          call r := instr_Mov(r, ECX, OConst(" + sizeInts + @"));
          call stk := logical_Store(r, core_state, stk, OMem(MReg(ESP,8)), OReg(ECX));

          call alignCall(r.regs[ESP]);
          {: call r, stk := logical_Call(r, core_state, stk);
          call          r,             stk, statics,     mems, $commonVars, $gcVars, $absMem, $toAbs,                objLayouts :=
            AllocObject(r, core_state, stk, statics, io, mems, $commonVars, $gcVars, $absMem, $toAbs, $stacksFrames, objLayouts,
              abs, " + size + " div 4, " + sizeInts + @" div 4); :}

          call r := logical_Load(r, core_state, stk, EAX, OMem(MReg(ESP,0)));

          call mems, $absMem :=
            gcStoreField(r, core_state, stk, statics, io, mems, $commonVars, $gcVars, $absMem, $toAbs, $stacksFrames, objLayouts,
              OMem(MReg(EAX, 4)), OConst(Tag_" + list + "_" + con + @"), r.regs[EAX] - 4, 2, Tag_" + list + "_" + con + @");
    ";
    }

    string allocImplInt(string list, string cons, string tl, string stackOffset)
    {
        return @"
          call r := logical_Load(r, core_state, stk, EDX, OMem(MReg(ESP," + stackOffset + @")));
          call mems, $absMem :=
            gcStoreField(r, core_state, stk, statics, io, mems, $commonVars, $gcVars, $absMem, $toAbs, $stacksFrames, objLayouts,
              OMem(MReg(EAX, Offset_" + list + "_" + tl + @")), OReg(EDX), r.regs[EAX] - 4, 1 + (Offset_" + list + "_" + tl + @" div 4), r.regs[EDX]);
    ";
    }

    string allocImplPtr(string list, string cons, string tl, string stackOffset) 
    {
          return @"
          call r, mems := gcLoadStack(r, core_state, stk, statics, io, mems, $commonVars, $gcVars, $absMem, $toAbs, $stacksFrames, objLayouts,
            EDX, OMem(MReg(ESP," + stackOffset + @")), r.regs[ESP] + " + stackOffset + @");
          assert THeapValue(objLayouts, true, $toAbs, r.regs[EDX], frameGet($stacksFrames, r.regs[ESP] + " + stackOffset + @"));
          call mems, $absMem :=
            gcStoreField(r, core_state, stk, statics, io, mems, $commonVars, $gcVars, $absMem, $toAbs, $stacksFrames, objLayouts,
              OMem(MReg(EAX, Offset_" + list + "_" + tl + @")), OReg(EDX), r.regs[EAX] - 4, 1 + (Offset_" + list + "_" + tl + @" div 4), frameGet($stacksFrames, r.regs[ESP] + " + stackOffset + @"));
    ";
    }

    string allocImpl2(string list, string cons, string destOffset)
    {
        return @"
          call mems, $stacksFrames :=
            gcStoreStack(r, core_state, stk, statics, io, mems, $commonVars, $gcVars, $absMem, $toAbs, $stacksFrames, objLayouts,
              OMem(MReg(ESP, " + destOffset + @")), OReg(EAX), r.regs[ESP] + " + destOffset + @", abs);

          heap := Heap(heap.absData[abs := Abs_" + list + @"(data_out)], heap.freshAbs - 1);

          assert THeapInv($absMem, objLayouts, heap);
          call r := logical_Add(r, ESP, OConst(12));
          {: call r := logical_Ret(r, core_state, stk); return; :}
        }
    ";
    }

    string allocArrayImpl(int IPSize, string triggers, string destOffset)
    {
        return @"
        implementation Proc_AllocArrayOfInt(my r_old:regs, const my core_state:core_state, linear stk_old:mem, linear statics_old:mem, linear io_old:IOState, linear mems_old:mems, $commonVars_old:commonVars, $gcVars_old:gcVars, $toAbs_old:[int]int, $absMem_old:[int][int]int, $stacksFrames_old:[int]Frames, objLayouts_old:[int]ObjLayout, heap_old:Heap, count:int)
          returns(my r:regs, linear stk:mem, linear statics:mem, linear io:IOState, linear mems:mems, $commonVars:commonVars, $gcVars:gcVars, $toAbs:[int]int, $absMem:[int][int]int, $stacksFrames:[int]Frames, objLayouts:[int]ObjLayout, heap:Heap, data:ArrayOfInt)
        {
          var abs:int;
          var _mem:[int]int;
          var obj:int;

          r := r_old;
          stk := stk_old;
          statics := statics_old;
          io := io_old;
          mems := mems_old;
          $commonVars := $commonVars_old;
          $gcVars := $gcVars_old;
          $toAbs := $toAbs_old;
          $absMem := $absMem_old;
          $stacksFrames := $stacksFrames_old;
          objLayouts := objLayouts_old;
          heap := heap_old;
          assert THeapInv($absMem, objLayouts, heap);

          assert TV(r.regs[ESP]) && " + triggers + @" && TO(0 - 1) && TO(0 - 2) && TO(0 - 3);          
          call r := logical_Sub(r, ESP, OConst(12));

          call heap, abs := freshAbs(?gcHi, $toAbs, heap);
          call r := instr_Mov(r, EBP, OConst(0));

          call r := logical_Load(r, core_state, stk, ECX, OMem(MReg(ESP," + (12 + IPSize) + @")));
          call r := instr_AddChecked(r, ECX, OReg(ECX));
          call r := instr_AddChecked(r, ECX, OReg(ECX));
          call r := instr_AddChecked(r, ECX, OConst(12));
          call stk := logical_Store(r, core_state, stk, OMem(MReg(ESP,4)), OReg(ECX));
          call stk := logical_Store(r, core_state, stk, OMem(MReg(ESP,8)), OReg(ECX));

          call alignCall(r.regs[ESP]);
          {: call r, stk := logical_Call(r, core_state, stk);
          call          r,             stk, statics,     mems, $commonVars, $gcVars, $absMem, $toAbs,                objLayouts :=
            AllocObject(r, core_state, stk, statics, io, mems, $commonVars, $gcVars, $absMem, $toAbs, $stacksFrames, objLayouts,
              abs, count + 3, count + 3); :}
          call r := logical_Load(r, core_state, stk, EAX, OMem(MReg(ESP,0)));

          call r := logical_Load(r, core_state, stk, ECX, OMem(MReg(ESP," + (12 + IPSize) + @")));
          call mems, $absMem :=
            gcStoreField(r, core_state, stk, statics, io, mems, $commonVars, $gcVars, $absMem, $toAbs, $stacksFrames, objLayouts,
              OMem(MReg(EAX, 4)), OReg(ECX), r.regs[EAX] - 4, 2, count);

          call mems, $stacksFrames :=
            gcStoreStack(r, core_state, stk, statics, io, mems, $commonVars, $gcVars, $absMem, $toAbs, $stacksFrames, objLayouts,
              OMem(MReg(ESP," + destOffset + ")), OReg(EAX), r.regs[ESP]+" + destOffset + @", abs);

          data := ArrayOfInt(count, abs);
          heap := Heap(heap.absData[abs := Abs_ArrayOfInt(data)], heap.freshAbs - 1);

          assert THeapInv($absMem, objLayouts, heap);
          call r := logical_Add(r, ESP, OConst(12));
          {: call r := logical_Ret(r, core_state, stk); return; :}
        }
    ";
    }

    string arrayElementPropertiesImpl()
    {
        return @"
        implementation arrayElementProperties(const my core_state:core_state, const linear stk:mem, const linear statics:mem, const linear io:IOState, const linear mems_old:mems, $commonVars:commonVars, $gcVars:gcVars, $toAbs:[int]int, $absMem:[int][int]int, $stacksFrames:[int]Frames, objLayouts:[int]ObjLayout, heap:Heap, index:int, abs:int, obj:int)
        {
          assert THeapInv($absMem, objLayouts, heap);
          assert THeapValue(objLayouts, true, $toAbs, obj, abs);
          call gcFieldProperties(core_state, stk, statics, io, mems_old, $commonVars, $gcVars, $absMem, $toAbs, $stacksFrames, objLayouts,
                obj - 4, 3 + index);
        }
    ";
    }

    string loadArrayElementImpl()
    {
        return @"
        implementation loadArrayElement(my r_old:regs, const my core_state:core_state, const linear stk:mem, const linear statics:mem, const linear io:IOState, linear mems_old:mems, $commonVars:commonVars, $gcVars:gcVars, $toAbs:[int]int, $absMem:[int][int]int, $stacksFrames:[int]Frames, objLayouts:[int]ObjLayout, heap:Heap, x:int, y:opn_mem, index:int, abs:int, obj:int)
            returns(my r:regs, linear mems:mems)
        {
          assert THeapInv($absMem, objLayouts, heap);
          assert THeapValue(objLayouts, true, $toAbs, obj, abs);
          call r, mems :=
            gcLoadField(r_old, core_state, stk, statics, io, mems_old, $commonVars, $gcVars, $absMem, $toAbs, $stacksFrames, objLayouts,
              x, y, obj - 4, 3 + index);
        }
    ";
    }

    string storeArrayElementImpl()
    {
        return @"
        implementation storeArrayElement(const my r:regs, const my core_state:core_state, const linear stk:mem, const linear statics:mem, const linear io:IOState, linear mems_old:mems, $commonVars:commonVars, $gcVars:gcVars, $toAbs:[int]int, $absMem_old:[int][int]int, $stacksFrames:[int]Frames, objLayouts:[int]ObjLayout, heap:Heap, x:opn_mem, y:opn, index:int, val:int, abs:int, obj:int)
            returns(mems:mems, absMem:[int][int]int)
        {
          assert THeapValue(objLayouts, true, $toAbs, obj, abs);
          assert THeapInv($absMem_old, objLayouts, heap);
          call mems, absMem :=
            gcStoreField(r, core_state, stk, statics, io, mems_old, $commonVars, $gcVars, $absMem_old, $toAbs, $stacksFrames, objLayouts,
              x, y, obj - 4, 3 + index, val);
          assert THeapInv(absMem, objLayouts, heap);
        }
    ";
    }

    void CompileDatatype2(Type t, TypeApply app)
    {
        string dataName = app.AppName(); 
        string suffix = dataName.Substring(((UserDefinedType)t).Name.Length);
        bool isSeq = dataName.StartsWith("Seq_");
        string lemma = isSeq ? "call proc_Seq__Cons__All" + suffix + "();" : "";
        TextWriter iwriter = heapIWriter;
        List<DatatypeCtor> ctors = compileDatatypes[app].AsDatatype.Ctors;

        
        Func<string,string> dataIs = c => isSeq ? ("is_" + c + "(data)") : ("data is " + c);
        string tags = String.Join(" || ", ctors.Select(c =>
            "(r.regs[x] == Tag_" + dataName + "_" + c.Name + " && " + dataIs(
            Compile_Constructor(t, c.Name, app.typeArgs).AppName()) + ")"));
        iwriter.WriteLine(loadTagDecl(dataName, tags));
        heapWriter.WriteLine("implementation loadTag_" + dataName
            + "(my r_old:regs, const my core_state:core_state, const linear stk:mem, const linear statics:mem, const linear io:IOState, linear mems_old:mems, $commonVars:commonVars, $gcVars:gcVars, $toAbs:[int]int, $absMem:[int][int]int, $stacksFrames:[int]Frames, objLayouts:[int]ObjLayout, heap:Heap, x:int, y:opn_mem, data:"
            + dataName + ", abs:int, obj:int)");
        heapWriter.WriteLine("  returns(my r:regs, linear mems:mems)");
        heapWriter.WriteLine("{");
        heapWriter.WriteLine("  assert THeapValue(objLayouts, true, $toAbs, obj, abs);");
        heapWriter.WriteLine("  assert THeapInv($absMem, objLayouts, heap);");
        heapWriter.WriteLine("  " + lemma);
        heapWriter.WriteLine("  call r, mems := gcLoadField(r_old, core_state, stk, statics, io, mems_old,");
        heapWriter.WriteLine("    $commonVars, $gcVars, $absMem, $toAbs, $stacksFrames, objLayouts,");
        heapWriter.WriteLine("    x, y, obj - 4, 2);");
        heapWriter.WriteLine("}");

        foreach (var ctor in ctors)
        {
            var ints = ctor.Formals.Where(x => !IsPtrType(app.AppType(x.Type))).ToList();
            var ptrs = ctor.Formals.Where(x =>  IsPtrType(app.AppType(x.Type))).ToList();
            var sorted = ints.Concat(ptrs).ToList();
            string ctorName = Compile_Constructor(t, ctor.Name, app.typeArgs).AppName();
            string cons = isSeq ? ("_" + ctorName) : ctorName;

            
            string parms = String.Join(", ", ctor.Formals.Select(
                c => "arg_" + c.Name + ":" + TypeString(app.AppType(c.Type))));
            
            string args = String.Join(", ", ctor.Formals.Select(c => "arg_" + c.Name));
            int argRetSize = 4 + 4 * Math.Max(ints.Count, ptrs.Count);
            heapIWriter.WriteLine("const stack_size__DafnyCC__Proc_Alloc_" + ctorName + ":int := 256;");
            iwriter.WriteLine(allocDecl1(
                                         dataName,
                                         ctorName,
                                         cons,
                                         parms,
                                         args,
                                         argRetSize.ToString()));
            string triggers = (IPSize == 8) ? String.Format("{0} && {1}", GcTO64(1), GcTO(3)) : GcTO(1);
            for (int i = 0; i < ints.Count; i++)
            {
                
                string val = "stk_old.map[r_old.regs[ESP] + "
                    + (IPSize + 4 * i) + "]";
                iwriter.WriteLine("requires " + CompileBase.IntEqTyped(app.AppType(ints[i].Type), "arg_" + ints[i].Name, val) + ";");
                triggers += String.Format(" && {0}", (IPSize == 8 ? StackTO64(i + 1): StackTO(i + 1)));
            }
            for (int i = 0; i < ptrs.Count; i++)
            {
                
                iwriter.WriteLine("requires StackAbsSlot(heap_old, $stacksFrames_old, r_old.regs[ESP] + "
                    + (IPSize + 4 + 4 * i) + " + stackGcOffset) == Abs_" + TypeString(app.AppType(ptrs[i].Type))
                    + "(arg_" + ptrs[i].Name + ");");
                triggers += String.Format(" && {0}", (IPSize == 8 ? GcTO64(i + 2): GcTO(i + 2)));
            }
            iwriter.WriteLine(allocDecl2(
                                         dataName,
                                         cons,
                                         PreserveHeap(minVerify),
                                         args));
            heapWriter.WriteLine(allocImpl1(
                                            dataName,
                                            ctor.Name,
                                            ctorName,
                                            cons,
                                            parms,
                                            args,
                                            (12 + 4 * sorted.Count).ToString(),
                                            (12 + 4 * ints.Count).ToString(),
                                            triggers,
                                            lemma));
            for (int i = 0; i < ints.Count; i++)
            {
                heapWriter.WriteLine(allocImplInt(
                                                  dataName,
                                                  ctorName,
                                                  ints[i].Name,
                                                  (12 + IPSize + 4 * i).ToString()));
            }
            for (int i = 0; i < ptrs.Count; i++)
            {
                heapWriter.WriteLine(allocImplPtr(
                                                  dataName,
                                                  ctorName,
                                                  ptrs[i].Name,
                                                  (RegAlloc.stackGcOffset + 16 + IPSize + 4 * i).ToString() + "/* stackGcOffset + 16 + IPSize + " + (4 * i) + " */"));
            }
            heapWriter.WriteLine(allocImpl2(
                                            dataName,
                                            ctorName,
                                            (RegAlloc.stackGcOffset + 12 + IPSize).ToString() + "/* stackGcOffset + 12 + IPSize */"));

            for (int i = 0; i < sorted.Count; i++)
            {
                var formal = sorted[i];
                iwriter.WriteLine(loadField(
                                            dataName,
                                            dataIs(ctorName),
                                            formal.Name));
                if (IsPtrType(app.AppType(formal.Type)))
                {
                    
                    
                    iwriter.WriteLine("ensures  HeapAbsData(heap, $absMem_old[abs]["
                        + (3 + i) + "]) == Abs_" + TypeString(app.AppType(formal.Type))
                        + "(" + formal.Name + (isSeq ? "_" : "#") + ctorName + "(data));");
                    iwriter.WriteLine("ensures  HeapValue(objLayouts_old, true, $toAbs_old, r.regs[x], $absMem_old[abs]["
                        + (3 + i) + "]);");
                    if (DafnySpec.IsArrayType(app.AppType(formal.Type)))
                    {
                        iwriter.WriteLine("ensures  $absMem_old[abs][" + (3+i) + "] == " + formal.Name + "#" + ctorName + "(data).arrAbs;");
                    }
                }
                else
                {
                    
                    iwriter.WriteLine("ensures  " + CompileBase.IntEqTyped(
                        app.AppType(formal.Type), formal.Name + (isSeq ? "_" : "#") + ctorName + "(data)", "r.regs[x]")
                        + ";");
                }
                heapWriter.WriteLine("implementation loadField_" + dataName + "_" + formal.Name
                    + "(my r_old:regs, const my core_state:core_state, const linear stk:mem, const linear statics:mem, const linear io:IOState, linear mems_old:mems, $commonVars:commonVars, $gcVars:gcVars, $toAbs:[int]int, $absMem:[int][int]int, $stacksFrames:[int]Frames, objLayouts:[int]ObjLayout, heap:Heap, x:int, y:opn_mem, data:"
                    + dataName + ", abs:int, obj:int)");
                heapWriter.WriteLine("    returns(my r:regs, linear mems:mems)");
                heapWriter.WriteLine("{");
                heapWriter.WriteLine("    assert THeapValue(objLayouts, true, $toAbs, obj, abs);");
                heapWriter.WriteLine("    assert THeapInv($absMem, objLayouts, heap);");
                heapWriter.WriteLine("    call r, mems := gcLoadField(r_old, core_state, stk, statics, io, mems_old, $commonVars, $gcVars, $absMem, $toAbs, $stacksFrames, objLayouts,");
                heapWriter.WriteLine("        x, y, obj - 4, " + (3 + i) + ");");
                heapWriter.WriteLine("    assert THeapValue(objLayouts, true, $toAbs, r.regs[x], $absMem[abs][" + (3 + i) + "]);");
                heapWriter.WriteLine("}");
            }
        }
    }

    string heapDecl()
    {
        return @"
        type Heap = Heap(absData:[int]AbsData, freshAbs:int);
        function HeapAbsData(heap:Heap, abs:int):AbsData { heap.absData[abs] }
        function StackAbsSlot(heap:Heap, stacksFrames:[int]Frames, ptr:int):AbsData { heap.absData[frameGet(stacksFrames, ptr)] }
        function HeapValue(objLayouts:[int]ObjLayout, isPtr:bool, rev:[int]int, val:int, abs:int):bool;
        function HeapInv(absMem:[int][int]int, objLayouts:[int]ObjLayout, heap:Heap):bool;

        atomic ghost procedure initHeap(absMem:[int][int]int, objLayouts:[int]ObjLayout) returns(heap:Heap);
          requires (forall i:int::{objLayouts[i]} objLayouts[i] == NoObjLayout());
          ensures  HeapInv(absMem, objLayouts, heap);

        atomic procedure heapLoadStack(my r__BEAT__old:regs,const my core_state:core_state,const linear stk:mem,const linear statics:mem,const linear io:IOState,linear mems__BEAT__old:mems,$commonVars:commonVars,$gcVars:gcVars,$absMem:[int][int]int,$toAbs:[int]int,$stacksFrames:[int]Frames,objLayouts:[int]ObjLayout,x:int,y:opn_mem,ptr:int)
          returns(my r:regs,linear mems:mems);
          requires isStack($S);
          requires NucleusInv(objLayouts,$S,$toAbs,$absMem,$commonVars,$gcVars,me,init,stk,statics,core_state,ptMem,mems__BEAT__old,$stacksFrames,io);
          requires StackLo($S)<=ptr&&ptr<StackHi($S);
          requires Aligned(ptr);
          requires EvalPtrOk(y);
          requires EvalPtr(r__BEAT__old,y)==ptr;
          ensures mems==old(mems__BEAT__old);
          ensures (r.regs)==(old(r__BEAT__old).regs)[x:=((r.regs)[x])];
          ensures word((r.regs)[x]);
          ensures HeapValue(objLayouts,true,$toAbs,(r.regs)[x],Abss#Frames($stacksFrames[$S])[ptr]);

        atomic procedure heapStoreStack(const my r:regs,const my core_state:core_state,const linear stk:mem,const linear statics:mem,const linear io:IOState,linear mems__BEAT__old:mems,$commonVars:commonVars,$gcVars:gcVars,$absMem:[int][int]int,$toAbs:[int]int,$stacksFrames__BEAT__old:[int]Frames,objLayouts:[int]ObjLayout,x:opn_mem,y:opn,ptr:int,abs:int)
          returns(linear mems:mems,$stacksFrames:[int]Frames);
          requires isStack($S);
          requires NucleusInv(objLayouts,$S,$toAbs,$absMem,$commonVars,$gcVars,me,init,stk,statics,core_state,ptMem,mems__BEAT__old,$stacksFrames__BEAT__old,io);
          requires StackLo($S)<=ptr&&ptr<StackHi($S);
          requires Aligned(ptr);
          requires HeapValue(objLayouts,true,$toAbs,Eval(r,y),abs);
          requires EvalPtrOk(x);
          requires EvalPtr(r,x)==ptr;
          requires SrcOk(y);
          ensures NucleusInv(objLayouts,$S,$toAbs,$absMem,$commonVars,$gcVars,me,init,stk,statics,core_state,ptMem,mems,$stacksFrames,io);
          ensures $stacksFrames==old($stacksFrames__BEAT__old[$S:=Frames(Abss#Frames($stacksFrames__BEAT__old[$S])[ptr:=abs])]);
        ";
    }

    string heapProcs()
    {
        return @"
        function THeapValue(objLayouts:[int]ObjLayout, isPtr:bool, rev:[int]int, val:int, abs:int):bool { true }
        function implementation{THeapValue(objLayouts, isPtr, rev, val, abs)} HeapValue(objLayouts:[int]ObjLayout, isPtr:bool, rev:[int]int, val:int, abs:int):bool
        {
            Value(objLayouts, isPtr, rev, val, abs)
        }

        function THeapInv(absMem:[int][int]int, objLayouts:[int]ObjLayout, heap:Heap):bool { true }
        function implementation{THeapInv(absMem, objLayouts, heap)} HeapInv(absMem:[int][int]int, objLayouts:[int]ObjLayout, heap:Heap):bool
        {
            heap.freshAbs < NO_ABS
         && heap.freshAbs < 0
         && heap.absData[NO_ABS] == AbsNone()
         && (forall i:int::{absMem[i]}{heap.absData[i]}{objLayouts[i]} heap.absData[i] == AbsNone() <==> objLayouts[i] == NoObjLayout())
         && (forall i:int::{absMem[i]}{heap.absData[i]} heap.absData[i] != AbsNone() ==> !word(i))
         && (forall i:int::{heap.absData[i]} i <= heap.freshAbs ==> heap.absData[i] == AbsNone())
         && (forall i:int::{absMem[i]}{heap.absData[i]} HeapWordInv(heap.absData, objLayouts[i], absMem[i], heap.absData[i], i))
        }

        atomic ghost procedure freshAbs(k:int, $toAbs:[int]int, heap_old:Heap) returns(heap:Heap, abs:int)
          requires (forall i:int::{$toAbs[i]} k <= i && i < ?gcHi ==> heap_old.freshAbs < $toAbs[i]);
          ensures  heap == Heap(heap_old.absData, heap.freshAbs);
          ensures  abs == heap.freshAbs;
          ensures  abs < heap_old.freshAbs;
          ensures  (forall i:int::{$toAbs[i]} 0 <= i && i < ?gcHi ==> abs < $toAbs[i]);
        {
          heap := Heap(heap_old.absData, heap_old.freshAbs - 1);
          if (k > 0)
          {
            if (heap.freshAbs >= $toAbs[k - 1])
            {
              heap := Heap(heap.absData, $toAbs[k - 1] - 1);
            }
            call heap, abs := freshAbs(k - 1, $toAbs, heap);
          }
          abs := heap.freshAbs;
        }

        implementation initHeap(absMem:[int][int]int, objLayouts:[int]ObjLayout) returns(heap:Heap)
        {
          heap := Heap((lambda i:int::AbsNone()), NO_ABS - 1);
          assert THeapInv(absMem, objLayouts, heap);
        }

        implementation heapLoadStack(my r__BEAT__old:regs,const my core_state:core_state,const linear stk:mem,const linear statics:mem,const linear io:IOState,linear mems__BEAT__old:mems,$commonVars:commonVars,$gcVars:gcVars,$absMem:[int][int]int,$toAbs:[int]int,$stacksFrames:[int]Frames,objLayouts:[int]ObjLayout,x:int,y:opn_mem,ptr:int)
          returns(my r:regs,linear mems:mems)
        {
          call r, mems := gcLoadStack(r__BEAT__old,core_state,stk,statics,io,mems__BEAT__old,$commonVars,$gcVars,$absMem,$toAbs,$stacksFrames,objLayouts,x,y,ptr);
          assert THeapValue(objLayouts,true,$toAbs,(r.regs)[x],Abss#Frames($stacksFrames[$S])[ptr]);
        }

        implementation heapStoreStack(const my r:regs,const my core_state:core_state,const linear stk:mem,const linear statics:mem,const linear io:IOState,linear mems__BEAT__old:mems,$commonVars:commonVars,$gcVars:gcVars,$absMem:[int][int]int,$toAbs:[int]int,$stacksFrames__BEAT__old:[int]Frames,objLayouts:[int]ObjLayout,x:opn_mem,y:opn,ptr:int,abs:int)
          returns(linear mems:mems,$stacksFrames:[int]Frames)
        {
          assert THeapValue(objLayouts,true,$toAbs,Eval(r,y),abs);
          call mems, $stacksFrames := gcStoreStack(r,core_state,stk,statics,io,mems__BEAT__old,$commonVars,$gcVars,$absMem,$toAbs,$stacksFrames__BEAT__old,objLayouts,x,y,ptr,abs);
        }
        ";
    }

    string heapWordInvArray()
    {
        return @"
        function HeapWordInvArray(absData:[int]AbsData, objLayout:ObjLayout, wordMem:[int]int, data:ArrayOfInt, abs:int):bool
        {
            data.arrCount >= 0
         && objLayout == ObjLayout(3 + data.arrCount, 3 + data.arrCount)
         && wordMem[2] == data.arrCount
         && data.arrAbs == abs
        }
        ";
    }

    string StackTO(int offset)
    {
        return String.Format("TO({0})", offset);
    }

    string StackTO64(int offset)
    {
        return String.Format("{0} && {1}", StackTO(offset), StackTO(offset + 1));
    }

    string GcTO(int offset)
    {
        return String.Format("TO({0} + {1}) /*stackGcOffsetWord + {1} */", RegAlloc.stackGcOffset / 4, offset);
    }

    string GcTO64(int offset)
    {
        return String.Format("{0} && {1}", GcTO(offset), GcTO(offset + 1));
    }

    void CompileDatatypes()
    {
        heapIWriter.WriteLine("    function Arr_Index(absMem:[int][int]int, arr:ArrayOfInt, i:int):int { absMem[arr.arrAbs][3 + i] }");
        heapIWriter.WriteLine("    function Arr_Length(arr:ArrayOfInt):int { if arr.arrCount >= 0 then arr.arrCount else 0 }");
        heapIWriter.WriteLine("    function fun_INTERNAL__array__elems(absMem:[int][int]int, arr:ArrayOfInt):[int]int { absMem[arr.arrAbs] }");
        heapIWriter.WriteLine("    function fun_INTERNAL__array__elems__index(arr:[int]int, k:int):int { arr[3 + k] }");
        heapIWriter.WriteLine("    function fun_INTERNAL__array__elems__update(arr:[int]int, k:int, v:int):[int]int { arr[3 + k := v] }");
        heapIWriter.WriteLine("    function fun_INTERNAL__array__update(absMem:[int][int]int, arr:ArrayOfInt, k:int, v:int):[int][int]int { absMem[arr.arrAbs := absMem[arr.arrAbs][3 + k := v]] }");
        heapIWriter.WriteLine(allocDeclArray(IPSize, PreserveHeap(minVerify)));
        heapIWriter.WriteLine(arrayElementProperties());
        heapIWriter.WriteLine(loadArrayElement());
        heapIWriter.WriteLine(storeArrayElement());

        heapWriter.WriteLine(heapWordInvArray());
        for (int i = 0; i < compileDatatypeList.Count; i++)
        {
            
            var app = compileDatatypeList[i];
            CompileDatatype1(compileDatatypes[app], app);
        }

        
        heapIWriter.WriteLine("type AbsData = AbsNone() | Abs_ArrayOfInt(arr:ArrayOfInt) | "
            + String.Join(" | ", compileDatatypes.Select(d => d.Key.AppName())
                .Select(x => "Abs_" + x + "(" + x + ":" + x + ")")) + ";");

        
        
        
        
        
        heapWriter.WriteLine("function HeapWordInv(absData:[int]AbsData, objLayout:ObjLayout, wordMem:[int]int, data:AbsData, abs:int):bool");
        heapWriter.WriteLine("{");
        heapWriter.WriteLine("    true");
        heapWriter.WriteLine(" && (data is Abs_ArrayOfInt ==> HeapWordInvArray(absData, objLayout, wordMem, data.arr, abs))");
        foreach (var d in compileDatatypes)
        {
            string name = d.Key.AppName();
            heapWriter.WriteLine(" && (data is Abs_" + name + " ==> HeapWordInv_"
                + name + "(absData, objLayout, wordMem, data." + name + "))");
        }
        heapWriter.WriteLine("}");

        heapIWriter.WriteLine(heapDecl());
        heapWriter.WriteLine(heapProcs());
        heapWriter.WriteLine(allocArrayImpl(IPSize,
                             String.Format("{0} && {1}", 
                                          (IPSize == 8 ? StackTO64(1): StackTO(1)),
                                          (IPSize == 8 ? GcTO64(1): GcTO(1))),
                             (RegAlloc.stackGcOffset + 12 + IPSize).ToString()));
        heapWriter.WriteLine(arrayElementPropertiesImpl());
        heapWriter.WriteLine(loadArrayElementImpl());
        heapWriter.WriteLine(storeArrayElementImpl());

        compileDatatypes.ToList().ForEach(p => CompileDatatype2(p.Value, p.Key));
    }

    public override void AddDatatypeLemmas(UserDefinedType t, TypeApply apply)
    {
        switch (t.Name)
        {
            case "Seq":
            {
                List<TypeApply> lemmaApps = new List<TypeApply>();
                Dictionary<string,string> loopLemmas = new Dictionary<string,string>();
                foreach (string lemmaName in seqLemmas)
                {
                    Method lemma = FindMethod(lemmaName);
                    var a = Compile_Method(lemma, apply.typeArgs);
                    lemmaApps.Add(a);
                    if (Attributes.Contains(lemma.Attributes, "loop_lemma"))
                    {
                        loopLemmas.Add(a.AppName(), "");
                    }
                }
                
                Type elementType = (t.TypeArgs.Count == 1) ? t.TypeArgs[0] : null;
                lemmaApps.ForEach(a => lemmas.Add(new LemmaCall("Seq", elementType,
                    "call " + ProcName(true, SimpleName(a.AppName())) + "();",
                    loopLemmas.ContainsKey(a.AppName()))));
                break;
            }
        }
    }

    public override CompileMethodGhost NewCompileMethod(DafnySpec dafnySpec, Method method,
        TypeApply typeApply, TextWriter writer, TextWriter iwriter, string moduleName, List<string> imports)
    {
        return new CompileMethod(dafnySpec, method, typeApply, writer, iwriter, moduleName, imports);
    }

    public override void Compile_FunctionAsMethod(Function function, Dictionary<TypeParameter,Type> typeArgs,
        Dictionary<string,TypeParameter> substArgs)
    {
        var tok = function.tok;
        if (Attributes.Contains(function.Attributes, "CompiledSpec"))
        {
            
            
            string specName = function.Name.Substring("CompiledSpec_".Length);
            function = FindFunction(specName);
        }
        bool hidden = Attributes.Contains(function.Attributes, "opaque");
        Formal result = new Formal(function.tok, "__result", function.ResultType, false, function.IsGhost);
        string funName = function.Name;
        string name = FunName(DafnySpec.SimpleSanitizedName(function));
        FunctionCallExpr call = new FunctionCallExpr(tok, name, new ThisExpr(tok), tok,
            function.Formals.ConvertAll(f => (Expression)
                MakeIdentifierExpr(f.Name, f.Type, f.IsGhost)));
        call.Function = function;
        call.TypeArgumentSubstitutions = typeArgs;
        call.Type = function.ResultType;
        CallStmt revealCall = null;
        if (hidden)
        {
            var selectExpr = new MemberSelectExpr(tok, new ThisExpr(tok), "reveal_" + function.Name);
            selectExpr.Member = FindMethod(selectExpr.MemberName);  // Manually resolve here
            selectExpr.TypeApplication = new List<Type>();  // Manually resolve here
            selectExpr.Type = new InferredTypeProxy();  // Manually resolve here            

            revealCall = new CallStmt(tok, tok, new List<Expression>(), selectExpr, new List<Expression>());
            revealCall.IsGhost = true;                                    
            ClassDecl cls = (ClassDecl)function.EnclosingClass;
            string fullName = "#" + function.Name + "_FULL";
            function = (Function)cls.Members.Find(m => m.Name == fullName);
            if (function == null)
            {
                throw new Exception("internal error: could not find function " + fullName);
            }
            substArgs = new Dictionary<string,TypeParameter>();
            function.TypeArgs.ForEach(t => substArgs.Add(t.Name, t));
            typeArgs = typeArgs.ToDictionary(p => substArgs[p.Key.Name], p => p.Value);
        }
        Expression funBody = function.Body;
        BlockStmt body = null;
        if (funBody != null)
        {
            ReturnStmt retStmt = new ReturnStmt(tok, tok, new List<AssignmentRhs>() {
                    new ExprRhs(funBody)
                });
            body = new BlockStmt(tok, tok,
                hidden
                    ? (new List<Statement>() { revealCall, retStmt })
                    : (new List<Statement>() { retStmt }));
        }
        List<Expression> ens = new List<Expression> {
                MakeBinaryExpr(BinaryExpr.Opcode.Eq, BinaryExpr.ResolvedOpcode.EqCommon, Type.Bool,
                    MakeIdentifierExpr("__result", function.ResultType, function.IsGhost),
                    call)
            }.Concat(function.Ens).ToList();
        Method method = new Method(tok, funName, function.IsStatic, function.IsGhost,
            function.TypeArgs, function.Formals, new List<Formal> { result },
            function.Req.ConvertAll(e => new MaybeFreeExpression(e)),
            new Specification<FrameExpression>(new List<FrameExpression>(), null),
            ens.ConvertAll(e => new MaybeFreeExpression(e)),
            function.Decreases,
            body, function.Attributes, function.SignatureEllipsis);
        method.EnclosingClass = function.EnclosingClass;
        Compile_Method(method, typeArgs);
    }

    public Tuple<Method,TypeApply> GetSeqBuildMethod(Type t, SeqTree tree, List<bool> elemDimensions)
    {
        
        
        if (elemDimensions.Count == 0)
        {
            return GetSeqMethod(t, "seq_Empty");
        }
        if (elemDimensions.Count == 2 && elemDimensions[0] && elemDimensions[1])
        {
            return GetSeqMethod(t, "seq_Append");
        }
        string op = "seq_" + SeqTree.TreeName(tree);
        DatatypeDecl seqDecl = FindDatatype("Seq");
        var tok = new Bpl.Token(0, 0);
        tok.filename = @"!\Seq.dfy";
        TypeApply tApp = Compile_SeqType((SeqType)t);
        Type dataType = new UserDefinedType(tok, "Seq", seqDecl, new List<Type> { ((SeqType)t).Arg });
        Type elemType = ((SeqType)t).Arg;
        Func<string,Type,Expression> idExpr = (x, typ) => {
            var e = new IdentifierExpr(tok, x);
            e.Type = typ;
            e.Var = new LocalVariable(tok, tok, x, typ, false);
            return e;
        };
        Func<string,List<Expression>,FunctionCallExpr> seqCall = (x, args) => {
            var seqOp = GetSeqOperation(t, x);
            FunctionCallExpr callExpr = new FunctionCallExpr(
                tok, "Seq_Empty", new ThisExpr(tok), tok, args);
            callExpr.Function = seqOp.Item1;
            callExpr.TypeArgumentSubstitutions = seqOp.Item2.typeArgs;
            return callExpr;
        };
        Expression empty = seqCall("Seq_Empty", new List<Expression> {});
        int varCount = 0;
        Func<SeqTree,Expression> resultRec = null;
        resultRec = (subtree) =>
        {
            if (subtree == null)
            {
                return idExpr("s" + (varCount++), dataType);
            }
            if (subtree.buildCount >= 0)
            {
                Expression build = empty;
                for (int i = 0; i < subtree.buildCount; i++)
                {
                    build = seqCall("Seq_Build", new List<Expression>
                        { build, idExpr("a" + (varCount++), elemType) });
                }
                return build;
            }
            else
            {
                return seqCall("Seq_Append", new List<Expression>
                    { resultRec(subtree.left), resultRec(subtree.right) });
            }
        };
        Expression result = resultRec(tree);
        Expression post = seqCall("Seq_Equal", new List<Expression> { idExpr("s", dataType), result });
        List<Statement> stmts = new List<Statement>();
        for (int i = elemDimensions.Count; i > 0;)
        {
            bool isFirst = (i == elemDimensions.Count);
            i--;
            if (elemDimensions[i])
            {
                if (isFirst)
                {
                    
                    stmts.Add(new AssignStmt(tok, tok, idExpr("s", dataType),
                        new ExprRhs(idExpr("s" + i, dataType))));
                }
                else
                {
                    // s := seq_Append(s9, s);
                    var selectExpr = new MemberSelectExpr(tok, new ThisExpr(tok), "seq_Append");
                    selectExpr.Member = FindMethod(selectExpr.MemberName);  // Manually resolve here
                    selectExpr.TypeApplication = new List<Type>() { elemType }; // Manually resolve here
                    selectExpr.Type = new InferredTypeProxy();  // Manually resolve here
                    
                    CallStmt callStmt = new CallStmt(tok, tok,
                        new List<Expression> {idExpr("s", dataType)},
                        selectExpr, new List<Expression>
                            { idExpr("s" + i, dataType), idExpr("s", dataType) });                                                        
                    stmts.Add(callStmt);
                }
            }
            else
            {
                if (isFirst)
                {
                    
                    DatatypeValue nil = new DatatypeValue(tok, "Seq", "Nil", new List<Expression>() {});
                    nil.Type = dataType;
                    nil.InferredTypeArgs = new List<Type> { elemType };
                    nil.Ctor = seqDecl.Ctors[0];
                    Util.Assert(nil.Ctor.Name == "Seq_Nil");
                    stmts.Add(new AssignStmt(tok, tok, idExpr("s", dataType), new ExprRhs(nil)));
                }
                // lemma_Seq_Cons(ai, s);
                var selectExpr = new MemberSelectExpr(tok, new ThisExpr(tok), "lemma_Seq_Cons");                
                selectExpr.Member = FindMethod(selectExpr.MemberName);   // Manually resolve here
                selectExpr.TypeApplication = new List<Type>() { elemType }; // Manually resolve here
                selectExpr.Type = new InferredTypeProxy();  // Manually resolve here
                
                CallStmt callStmt = new CallStmt(tok, tok,
                    new List<Expression> {},
                    selectExpr, new List<Expression>
                        { idExpr("a" + i, elemType), idExpr("s", dataType) });                                
                callStmt.IsGhost = true;
                stmts.Add(callStmt);
                
                DatatypeValue cons = new DatatypeValue(tok, "Seq", "Cons", new List<Expression>()
                    { idExpr("a" + i, elemType), idExpr("s", dataType) });
                cons.Type = dataType;
                cons.InferredTypeArgs = new List<Type> { elemType };
                cons.Ctor = seqDecl.Ctors[1];
                Util.Assert(cons.Ctor.Name == "Seq_Cons");
                stmts.Add(new AssignStmt(tok, tok, idExpr("s", dataType), new ExprRhs(cons)));
            }
        }
        BlockStmt body = new BlockStmt(tok, tok, stmts);
        List<Formal> ins = new List<Formal>();
        for (int i = 0; i < elemDimensions.Count; i++)
        {
            bool isSeq = elemDimensions[i];
            ins.Add(new Formal(tok, (isSeq ? "s" : "a") + i, isSeq ? dataType : elemType, true, false));
        }
        List<Formal> outs = new List<Formal> { new Formal(tok, "s", dataType, false, false) };
        List<MaybeFreeExpression> reqs = new List<MaybeFreeExpression>();
        List<MaybeFreeExpression> enss = new List<MaybeFreeExpression> { new MaybeFreeExpression(post) };
        Specification<FrameExpression> mods = new Specification<FrameExpression>(new List<FrameExpression>(), null);
        Specification<Expression> decs = new Specification<Expression>(new List<Expression>(), null);
        Attributes attrs = new Attributes("dafnycc_conservative_seq_triggers", new List<Expression>(), null);
        Method m = new Method(tok, op, true, false, tApp.typeParams, ins, outs, reqs, mods, enss, decs, body, attrs, tok);
        m.EnclosingClass = GetSeqMethod(t, "seq_Append").Item1.EnclosingClass;
        return Tuple.Create(m, Compile_Method(m, tApp.typeArgs));
    }

    void addAxioms(TextWriter sw, IEnumerable<string> axiomModules)
    {
        foreach (string axiomModule in axiomModules)
        {
            sw.WriteLine(String.Format("//<NuBuild AddBoogieAxiom {0} />", axiomModule));
        }
    }

    public Dictionary<string,string> CompileCodeStart(DafnyCC_Options options, IList<string> files)
    {
        IEnumerable<string> axioms = new string[] {
            "Base_axioms", "Word_axioms", "Memory_axioms", "Assembly_axioms", "Io_axioms" };
        Dictionary<string,string> allModules = CompileSpecStart(options, files);

        relational = options.relational;
        x64 = options.x64;
        IPSize = x64 ? 8 : 4;
        useFramePointer = options.useFramePointer;
        framePointerCount = useFramePointer ? 1 : 0;

        heapWriter = new StreamWriter(Path.Combine(outDir, "Heap"+ImpBasmExtn));
        heapIWriter = new StreamWriter(Path.Combine(outDir, "Heap"+IfcBasmExtn));
        checkedWriter = new StreamWriter(Path.Combine(outDir, "Checked"+ImpBasmExtn));
        checkedIWriter = new StreamWriter(Path.Combine(outDir, "Checked"+IfcBasmExtn));

        List<string> checkedImports = new List<string> { "Trusted" };
        checkedIWriter.WriteLine("module interface Checked");
        WriteInterfaceImports(checkedIWriter, GatherAllImports(checkedImports));
        checkedIWriter.WriteLine("{");
        checkedIWriter.WriteLine("type ArrayOfInt = ArrayOfInt(arrCount:int, arrAbs:int);");
        WriteImplementationHeader(checkedWriter, "Checked", new List<string>() { "Trusted" });

        List<string> heapImports = new List<string> { "Trusted", "Checked" };
        heapIWriter.WriteLine("module interface Heap");
        WriteInterfaceImports(heapIWriter, GatherAllImports(heapImports));
        addAxioms(heapWriter, axioms);
        heapIWriter.WriteLine("{");
        WriteImplementationHeader(heapWriter, "Heap", heapImports);

        List<string> seqImports = new List<string> { "Trusted", "Checked", "Heap" };
        seqWriter = new StreamWriter(Path.Combine(outDir, "Seq"+ImpBasmExtn));
        seqIWriter = new StreamWriter(Path.Combine(outDir, "Seq"+IfcBasmExtn));
        seqIWriter.WriteLine("module interface Seq");
        WriteInterfaceImports(seqIWriter, GatherAllImports(seqImports));
        seqIWriter.WriteLine("{");
        addAxioms(seqWriter, axioms);
        WriteImplementationHeader(seqWriter, "Seq", seqImports);

        return allModules;
    }

    public void CompileCodeEnd(DafnyCC_Options options)
    {
        checkedIWriter.WriteLine("}");
        checkedWriter.WriteLine("}");
        checkedIWriter.Close();
        checkedWriter.Close();

        heapIWriter.WriteLine("}");
        heapWriter.WriteLine("}");

        seqIWriter.WriteLine("}");
        seqWriter.WriteLine("}");
        seqIWriter.Close();
        seqWriter.Close();

        if (outDir == null)
        {
            mainWriter.WriteLine("}");
        }

        heapWriter.Close();
        heapIWriter.Close();

        CompileSpecEnd();
    }

    public void CompileCode(DafnyCC_Options options, IList<string> files)
    {
        Dictionary<string,string> allModules = CompileCodeStart(options, files);

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
        CompileDatatypes();

        CompileCodeEnd(options);
    }
}

