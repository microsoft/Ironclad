open Ast
open Parse
open Parse_util
open Emit_bpl
open Microsoft.FSharp.Math

let check_concurrent = ref false

let proc_name (s:string) = "_?" + s
let const_name (s:string) = "?_" + s
let label (ctxt:string) (s:string) = ctxt ^ "$" ^ s

let sym = ref 0
let gensym () = incr sym; "$$" ^ (string_of_int !sym)

let list_remove x l = List.filter (fun y -> x <> y) l

type width = W8 | W16 | W32
let string_of_width w = match w with W8 -> "byte" | W16 -> "word" | W32 -> "dword"

type con = string
type operand =
| OConst of con
| OReg of reg
| OTmpReg of reg
| OSelector of string
| OConstPtr of con
| OOffset of reg * con
| OIndex of reg * con * reg * con
| OExp of bigint option

type varMap = (id * operand) list
type insCtxt = string * varMap
type inlineMap = InlineMap of (string * (operand list -> inlineMap * insCtxt * (loc * stmt) list)) list
type inlinePreMap = (string * (operand list -> insCtxt * (loc * stmt) list)) list

let is_32bit_bigint i = BigInt.Zero <= i && i < (BigInt.Parse "4294967296")
let is_32bit_bigint_signed i = (BigInt.Parse "-4294967296") <= i && i < (BigInt.Parse "4294967296")

let x64 = ref false //32-bit by default

let const_of_exp (e:exp):con =
  match e with
  | EInt i when is_32bit_bigint i -> i.ToString()
  | EVar x -> const_name x
  | _ -> err "unexpected constant"

let const_of_exp_signed (e:exp):con =
  match e with
  | EInt i when is_32bit_bigint_signed i -> i.ToString()
  | EOp (Uop "-", [EInt i]) when is_32bit_bigint_signed (-i) -> (-i).ToString()
  | _ -> const_of_exp e

let operand_of_exp (varMap:varMap) (e:exp):operand =
  match e with
  | EApply ("OConst", [c]) -> OConst (const_of_exp c)
  | EApply ("OReg", [EVar x]) when x.StartsWith("TMP") -> OTmpReg x
  | EApply ("OReg", [EVar x]) -> OReg x
  | EApply ("OMem", [EApply ("MConst", [c])]) -> OConstPtr (const_of_exp c)
  | EApply ("OMem", [EApply ("MReg", [EVar x; c])]) -> OOffset (x, const_of_exp_signed c)
  | EApply ("OMem", [EApply ("MIndex", [EVar xb; EInt i; EVar xi; c])])
      when (match i.ToString() with "1" | "2" | "4" | "8" -> true | _ -> false) ->
      OIndex (xb, i.ToString(), xi, const_of_exp_signed c)
  | EVar x when List.mem_assoc x varMap -> List.assoc x varMap
  | EVar ("EAX" | "EBX" | "ECX" | "EDX" | "ESI" | "EDI" | "EBP" | "ESP" as x) -> OReg x
  | EVar x when x.StartsWith("TMP") -> OTmpReg x
  | EVar ("CS" | "DS" | "ES" | "FS" | "GS" | "SS" as x) -> OSelector x
  | EInt i -> OExp (Some i)
  | _ -> OExp None

let rec free_vars_exp (scopeVars:string list) (e:exp):string list =
  match e with
  | EVar x -> if (List.mem x scopeVars) then [] else [x]
  | EInt _ | EReal _ | EBv32 _ | EBool _ -> []
  | EOp (_, es) -> List.collect (free_vars_exp scopeVars) es
  | EApply (_, es) -> List.collect (free_vars_exp scopeVars) es
  | EQuant (_, xs, ts, e) -> List.collect (free_vars_exp ((List.map fst xs) @ scopeVars)) (e::(List.concat ts))

let check_module (included:_module list) (ifc:_module) (imp:_module) =
  let allDs = (List.collect (fun m -> m.mDecls) (imp::ifc::included)) in
  let pubDs = (List.collect (fun m -> m.mDecls) (ifc::included)) in
  let procMap =
    List.collect
      (fun (_, d) -> match d with DProc ((x, Procedure (g, a), _, _, _, specs, _) as p) -> [(x, ((g, a), specs))] | _ -> [])
      allDs in
  let includeNames = List.map (fun i -> i.mName) included in
  let ds = ifc.mDecls @ imp.mDecls in
  let allVars = List.collect (fun (_, d) -> match d with DStaticGhost (x, _, _, _) -> [x] | _ -> []) allDs in
  let allRwVars = List.collect (fun (_, d) -> match d with DStaticGhost (x, _, _, ReadWrite) -> [x] | _ -> []) allDs in
  let declVars = List.collect (fun (_, d) -> match d with DStaticGhost (x, _, _, _) -> [x] | _ -> []) ds in
  let implVars = List.collect (fun (_, d) -> match d with DStaticGhost (x, _, _, _) -> [x] | _ -> []) imp.mDecls in
  let ifcProcs = List.collect (fun (_, d) -> match d with DProc (x, _, _, _, _, _, _) -> [x] | _ -> []) ifc.mDecls in
  let pubProcs = List.collect (fun (_, d) -> match d with DProc (x, _, _, _, _, _, _) -> [x] | _ -> []) pubDs in
  // check that all procedures have implementations
  let mProcDecls = List.collect (fun (_, d) -> match d with DProc (x, _, _, _, _, _, _) -> [x] | _ -> []) (imp.mDecls @ ifc.mDecls) in
  let mProcDefs = List.collect (fun (_, d) -> match d with DProc (x, _, _, _, _, _, Some _) -> [x] | _ -> []) (imp.mDecls @ ifc.mDecls) in
  List.iter (fun x -> if (not (List.mem x mProcDefs)) then err ("module " + ifc.mName + " does not implement procedure " + x)) mProcDecls;
  // check that untrusted modules do not declare built-in instructions
  List.iter (fun (x:string) -> if x.StartsWith("instr_") then err ("untrusted module " + ifc.mName + " cannot declare instruction " + x)) mProcDecls;
  // check that imported module list matches included list
// TODO consult Chris about synchronization between include/import
// I think we're delegating all this responsibility to build system anyway.
//  List.iter (fun x -> if not (List.mem x imp.mImports) then err ("included module " + x + " must be imported")) includeNames;
//  List.iter (fun x -> if not (List.mem x includeNames) then err ("imported module " + x + " must be included")) imp.mImports;
  // check each procedure
  List.iter
    (fun ((locF, locL), d) ->
      match d with
      | DProc (xp, _, ik, ps, rs, specs, b_opt) ->
        (
          try
          (
            let check_spec spec =
              match spec with
              | (_, Requires (IsRel, _)) | (_, Ensures (IsRel, _)) when not !symdiff_allow ->
                  err "'relation' expression only allowed when using -symdiffok flag or -symdiffms option"
              | _ -> ()
              in
            List.iter check_spec specs;
            let proc_decl = try List.assoc xp procMap with :? System.Collections.Generic.KeyNotFoundException as x -> err ("procedure " + xp + " not found") in
            let ((ghost, atomicity), dspecs) = proc_decl in
            let procRel = List.exists (fun spec ->
              match spec with (_, Ensures (IsRel, _)) -> true | (_, Requires (IsRel, _)) -> true | _ -> false) dspecs in
            let locals = ps @ rs @ (match b_opt with None -> [] | Some (ls, _) -> ls) in
            let local_xs = List.map (fun (x, _, _) -> x) locals in
            // public variables in yield statements must be declared in module yields
            let check_yield e =
              List.iter
                (fun x ->
                  match (List.mem x allVars, List.mem x implVars, List.mem x ifc.mModifies, List.mem x ifc.mYields) with
                  | (false, _, _, _) -> () // not a variable (is a constant, or an invalid variable that will cause a Boogie error)
                  | (true, true, false, _) -> () // private variable; no one else is allowed to modify x
                  | (true, _, _, true) -> () // variable declared in yields
                  | (true, _, _, false) -> err ("variable " + x + " occurs in yield, must be declared in module yields"))
                (free_vars_exp local_xs e) in
            // if any assigned variables are in the module's modifies list, check that the assignment is in public atomic action
            let check_assign forallScope x =
              match forallScope with
              | Some fa_xs -> if not (List.mem x fa_xs) then err ("cannot assign to variable " + x + " inside forall statement") else ()
              | None ->
                (
                  if List.mem x local_xs then () else
                  match (List.mem x allVars, List.mem x allRwVars, List.mem x declVars, List.mem x ifc.mModifies, atomicity, List.mem xp ifcProcs) with
                  | (false, _, _, _, _, _) -> err ("in procedure " + xp + ", cannot find declaration of variable " + x)
                  | (true, false, _, _, _, _) -> err ("procedure " + xp + " assigns to readonly variable " + x)
                  | (true, true, false, false, _, _) -> err ("procedure " + xp + " assigns to " + x + " without declaring " + x + " in module modifies")
                  | (true, true, true, false, _, _) -> () // private variable; no one else is allowed to yield on x (REVIEW: require List.mem x implVars here for clarity?)
                  | (true, true, _, true, Atomic, true) -> () // assignment is publicized via public atomic procedure
                  | (true, true, _, true, _, true) -> err ("procedure " + xp + " must be atomic to assign to variable " + x)
                  | (true, true, _, true, _, false) -> err ("procedure " + xp + " must be declared in module interface to assign to variable " + x)
                )
              in
            let check_call is_inline ghost forallScope (xc:id) =
              if xc.StartsWith("construct##") || xc.StartsWith("destruct##") then () else
              try
                let ((gc, ac), specs) = List.assoc xc procMap in
                List.iter (fun (_, s) ->
                    match (forallScope, s) with
                    | (Some _, Modifies _) -> err "forall statement cannot call procedure with modifies clause"
                    | (_, Requires (IsRel, _)) when not !symdiff_allow -> err "call to procedure with relational requires only allowed when using -symdiffok flag or -symdiffms option"
                    | (_, Requires (IsRel, _)) when not procRel -> err "call to procedure with relational requires only allowed from procedure with relational requires or relational ensures (hint: try adding 'ensures public(true);')"
                    | _ -> ())
                  specs;
                if xp = xc then
                  (
                    match (ghost, is_inline, ps) with
                    | (PGhost, true, _::_) -> ()
                    | _ -> err ("recursive procedures must be ghost, inline, with a decreasing, non-negative first parameter: " + xc)
                  );
                (match (atomicity, ac) with
                | (Atomic, Yields) | (Atomic, Stable) -> err ("atomic procedure " + xp + " cannot call non-atomic procedure " + xc)
                | _ -> ());
                (match (ghost, gc) with
                | (PGhost, PReal) -> err ("cannot call non-ghost procedure " + xc + " in ghost context")
                | (PGhost, PGhost) | (PReal, _) -> ())
              with :? System.Collections.Generic.KeyNotFoundException as x -> err ("procedure " + xc + " not found") in
            let check_par forallScope xc (xpar, _) =
              try
                let ((_, ac), _) = List.assoc xc procMap in
                let ((gpar, apar), specs) = List.assoc xpar procMap in
                List.iter (fun s ->
                  match (forallScope, s) with (Some _, (_, Modifies _)) -> err "forall statement cannot call procedure with modifies clause" | _ -> ()) specs;
                if xp = xc then err ("recursive parallel calls not allowed: " + xc);
                match (ac, apar, gpar) with
                // All parallel call targets must be stable
                // All parallel call targets except for first must be ghost
                | (Atomic, _, _) | (Yields, _, _) -> err ("target of parallel call " + xc + " must be declared 'stable'")
                | (Stable, Atomic, _) | (Stable, Yields, _) -> err ("target of parallel call " + xpar + " must be declared 'stable'")
                | (Stable, Stable, PReal) -> err ("target of parallel call " + xpar + " must be declared 'ghost'")
                | (Stable, Stable, PGhost) -> ()
              with :? System.Collections.Generic.KeyNotFoundException as x -> err ("procedure " + xc + " or " + xpar + " not found") in
            // if specifications must be stable, check that variables are declared in yields
            (if atomicity = Stable then
                List.iter (fun (_, s) -> match s with Requires (_, e) | Ensures (_, e) -> check_yield e | _ -> ()) specs
              else ());
            // check all statements
            let rec check_stmt ghost forallScope =
              (fun ((locF, locL), stmt) ->
                try
                (
                  (match (stmt, ik) with ((SReturn | SIReturn), Inline) -> err "return not allowed in inline procedure" | _ -> ());
                  match stmt with
                  | SLabel _ | SGoto _ | SReturn | SIReturn | SIfJcc _ ->
                      (match ghost with PReal -> () | PGhost -> err ("illegal control construct in ghost context"))
                  | SGroup b -> List.iter (check_stmt ghost forallScope) b
                  | SIfGhost (_, b) -> List.iter (check_stmt PGhost forallScope) b
                  // REVIEW: we allow forall bodies to read (but not write) linear variables
                  | SForallGhost (_, _, _, fVars, b) -> List.iter (check_stmt PGhost (Some (List.map fst fVars))) b
                  | SExistsGhost (_, _, _) -> ()
                  | SAssert _ -> ()
                  | SSplit -> ()
                  | SYield _ when atomicity = Atomic -> err ("procedure " + xp + " cannot be declared atomic because it contains a yield statement")
                  | SYield _ when ghost = PGhost -> err ("yield cannot appear in ghost context")
                  | SYield e -> check_yield e
                  | SAssign (x, _) -> check_assign forallScope x
                  | SInline (xs, target, _, pars) ->
                      check_call true ghost forallScope target;
                      List.iter (check_assign forallScope) xs;
                      List.iter (check_par forallScope target) pars
                  | SCall _ when ghost = PGhost -> err ("call to non-inline procedure cannot appear in ghost context")
                  | SCall (xs, target, _) -> check_call false ghost forallScope target; List.iter (check_assign forallScope) xs
                ) with Err s -> err ("In procedure " + xp + " (" + locF + " line " + (string locL) + "):" + System.Environment.NewLine + s))
              in
            let check_stmts b =
              let rec body_end b =
                match b with
                | (_, SGroup b)::_ -> body_end (List.rev b)
                | (_, (SReturn | SIReturn | SGoto _))::_ -> ()
                | _ -> err "body must end with return or goto"
                in
              (match ik with Inline -> () | Outline -> body_end (List.rev b));
              List.iter (check_stmt ghost None) b
              in
            (match b_opt with None -> () | Some (_, stmts) -> check_stmts stmts)
          ) with Err s -> err ("In procedure " + xp + " (" + locF + " line " + (string locL) + "):" + System.Environment.NewLine + s)
        )
      | _ -> ())
    ds;
  ()

let rec applied_funs_exp (maskVars:string list) (e:exp):string list =
  let f = applied_funs_exp maskVars in
  match e with
  | EVar _ | EInt _ | EReal _ | EBv32 _ | EBool _ -> []
  | EOp (_, es) -> List.collect f es
  | EApply (x, es) ->
      let x = x + "(...)" in
      (if (List.mem x maskVars) then [] else [x]) @ (List.collect f es)
  | EQuant (_, _, ts, e) -> List.collect f (e::(List.concat ts))

// Returns list of declarations that e depends on
let rec link_check_exp (scopeVars:string list) (e:exp):string list =
  (free_vars_exp scopeVars e) @ (applied_funs_exp scopeVars e)

let rec stmt_calls (_, stmt:stmt):string list =
  match stmt with
  | SLabel _ | SGoto _ | SReturn | SIReturn | SIfJcc _ | SAssert _ | SSplit | SYield _ | SAssign _ | SExistsGhost _ -> []
  | SGroup b -> List.collect stmt_calls b
  | SIfGhost (_, b) -> List.collect stmt_calls b
  | SForallGhost (_, _, _, _, b) -> List.collect stmt_calls b
  | SInline (_, target, _, pars) -> [target] @ (List.map fst pars)
  | SCall (_, target, _) -> [target]

let link_check_module (scopeVars:string list) (mIntf:_module, mImpl:_module):string list =
  let intf = mIntf.mDecls in
  let impl = mImpl.mDecls in
  let check_decl (_, d:decl):string list * (string * string list) list =
    let pid (x:string):string = x + "(..);" in
    let fid (ps_opt:formal list option) (x:string):string =
      match ps_opt with None -> x | Some _ -> x + "(...)" in
    let param_ids (ps_opt:formal list option):id list =
      match ps_opt with None -> [] | Some ps -> List.map fst ps in
    match d with
    | DFunDecl (x, ps_opt, _, None, _, _) -> ([fid ps_opt x], [])
    | DFunDecl (x, ps_opt, _, Some e, _, Some _) ->
        ([], [(fid ps_opt x, link_check_exp ((x + "(...)")::(param_ids ps_opt) @ scopeVars) e)])
    | DFunDecl (x, ps_opt, _, Some e, _, None) ->
        ([fid ps_opt x], [(fid ps_opt x, link_check_exp ((x + "(...)")::(param_ids ps_opt) @ scopeVars) e)])
    | DType (xt, _, _, None) -> ([("sizeof##" + xt + "(...)")], [])
    | DType (xt, overload, impl, Some cs) ->
        // Note: we use sizeof##'s checking to check for correct definition of xt (e.g. to check that xt not defined more than once)
        // TODO: check that xc not declared twice?
        ((if impl then [] else ["sizeof##" + xt + "(...)"]) @ (List.collect (fun (_, xc, fs) ->
          (xc + "(...)")::(pid ("construct##" + xc))::(pid ("destruct##" + xc))::("is#" + xc + "(...)")
            ::(List.collect (fun (xf, _, _) ->
              (if overload then [] else ["." + xf + "(...)"]) @ [xf + "#" + xc + "(...)"]) fs)) cs),
                [("sizeof##" + xt + "(...)"), []])
    | DStatic x -> (["?ADDR__" + x], [])
    | DStaticGhost _ -> ([], [])
    | DProc (x, _, _, _, _, _, None) -> ([pid x], [])
    | DProc (x, Implementation, _, _, _, _, Some (_, b)) ->
        ([], [(pid x, List.filter (fun y -> not (List.mem y ((pid x)::scopeVars))) (List.map pid (List.collect stmt_calls b)))])
    | DProc (x, Procedure _, _, _, _, _, Some (_, b)) ->
        ([pid x], [(pid x, List.filter (fun y -> not (List.mem y ((pid x)::scopeVars))) (List.map pid (List.collect stmt_calls b)))])
  let pubs = List.map check_decl intf in
  let prvs = List.map check_decl impl in
  let (pub_decls, pub_defs) = (List.collect fst pubs, List.collect snd pubs) in
  let (prv_decls, prv_defs) = (List.collect fst prvs, List.collect snd prvs) in
  let decls = pub_decls @ prv_decls in
  List.iter (fun d -> if List.mem d scopeVars then err (d ^ " declared more than once")) decls;
  let defs = pub_defs @ prv_defs in
  let undefs = List.filter (fun d -> not (List.mem_assoc d defs)) decls in
  let rec check_defs (ds:(string * string list) list):unit =
    // move definitions with no unresolved dependencies to front
    //System.Console.WriteLine(); List.iter (fun ds -> System.Console.WriteLine("" + (fst ds) + " --> " + (String.concat "," (snd ds)))) ds;
    let (defs_ready, defs_wait) = List.partition (fun (x, deps) -> List.isEmpty deps) ds in
    match (defs_ready @ defs_wait) with
    | [] -> ()
    | (d,[])::_ when not (List.mem d decls) -> err (d ^ " not declared in current module")
    | (d,[])::ds when (List.mem_assoc d ds) -> err (d ^ " defined more than once")
    | (d,[])::ds -> check_defs (List.map (fun (d2,deps) -> (d2, list_remove d deps)) ds)
    | (d1,(d2::_))::_ -> err (d1 ^ " can't find dependency " ^ d2 ^ " (or these are circularly defined). This in module " ^ mIntf.mName)
  in
  let () = check_defs ((List.map (fun d -> (d, [])) undefs) @ defs) in
  pub_decls @ scopeVars

let link_check_modules (ms:(_module * _module) list):unit =
  // check that all module names are unique
  List.iter
    (fun ({mName = ifName; mIsImpl = ifImpl}, {mName = imName; mIsImpl = imImpl}) ->
      if ifName <> imName then err ("module interface and implementation have different names: " + ifName + ", " + imName) else
      if ifImpl then err ("expected module interface, found implementation: " + ifName) else
      if not imImpl then err ("expected module implementation, found interface: " + imName) else
      if (List.length (List.filter (fun ({mName = x}, _) -> ifName = x) ms) <> 1)
        then err ("more than one module named " + ifName))
    ms;
  // For each variable x modified by xM, check that anyone yielding on x imports xM
  // For each variable x declared in xM but not modified by xM, check that no one yields on x
  List.iter
    (fun ({mName = xM; mModifies = xMods; mDecls = xDs}, _) ->
      List.iter
        (fun ({mName = yM; mYields = yYields}, {mName=_ (* mImports = yImports*) }) ->
          List.iter (fun (_, d) ->
              match d with
              | DStaticGhost (x, _, _, _) ->
                (
                  if List.mem x yYields && not (List.mem x xMods) then
                    err ("module " + yM + " yields on non-exported variable " + x)
                )
              | _ -> ())
            xDs;
          List.iter (fun x ->
//              if List.mem x yYields && not (List.mem xM (yM::yImports)) then
// This branch has no yield (concurrency) support, and the import
// behavior has changed, so for now, we disallow all yields on the
// grounds that we can't check the import sanity.
              if List.mem x yYields && true then
                err ("module " + yM + " must import " + xM + " to yield on variable " + x))
            xMods)
        ms)
    ms;
  // check that definitions are well founded
  let _ = List.fold link_check_module [] ms in
  ()

let sw_reg (w:width) (r:reg): string =
  match (w, r) with
  | (W32, "EAX") -> "eax"
  | (W32, "EBX") -> "ebx"
  | (W32, "ECX") -> "ecx"
  | (W32, "EDX") -> "edx"
  | (W32, "ESI") -> "esi"
  | (W32, "EDI") -> "edi"
  | (W32, "EBP") -> "ebp"
  | (W32, "ESP") -> "esp"
  | (W16, "EAX") -> "ax"
  | (W16, "EBX") -> "bx"
  | (W16, "ECX") -> "cx"
  | (W16, "EDX") -> "dx"
  | (W8, "EAX") -> "al"
  | (W8, "EBX") -> "bl"
  | (W8, "ECX") -> "cl"
  | (W8, "EDX") -> "dl"
  | _ -> err "unexpected register"
let s_reg (r:reg): string = sw_reg W32 r

let seg_reg (r:reg): string =
  match r with
//  | "CS" -> "cs"
  | "DS" -> "ds"
  | "SS" -> "ss"
  | "FS" -> "fs"
  | "GS" -> "gs"
  | _ -> err "unexpected segment register"

let simple_w_operand (w:width) (o:operand): string =
  match (w, o) with
  | (W32, OConst i) -> i
  | (_, OReg r) -> sw_reg w r
  | _ -> err "unexpected operand"
let simple_operand (o:operand): string = simple_w_operand W32 o

let src_operand (ctxt:string) (o:operand): string =
  match o with
  | OConst i -> i
  | OReg r -> s_reg r
  | _ -> err "unexpected operand"

let r_operand (o:operand): string =
  match o with
  | OReg r -> s_reg r
  | _ -> err "unexpected reg operand"

let addr_operand (o:operand): string =
  match o with
  (* TODO: check offset and scale *)
  (* TODO: 1-byte and 2-byte mems *)
  | OConstPtr i -> i
  | OOffset (r, i) -> (s_reg r) ^ " + " ^ (i)
  | OIndex (rb, s, rs, i) -> (s_reg rb) ^ " + " ^ (s) ^ " * " ^ (s_reg rs) ^ " + " ^ (i)
  | _ -> err "unexpected addr operand"

let mem_operand (width:width) (o:operand): string = (string_of_width width) ^ " ptr [" ^ (addr_operand o) ^ "]"

let src_mem_operand (ctxt:string) (width:width) (o:operand): string =
  match o with
  | OConst _ | OReg _ -> src_operand ctxt o
  | OConstPtr _ | OOffset _ | OIndex _ -> mem_operand width o
  | _ -> err "unexpected src_mem operand"

let dest_mem_operand (ctxt:string) (width:width) (o:operand): string =
  match o with
  | OReg r -> s_reg r
  | OConstPtr _ | OOffset _ | OIndex _ -> mem_operand width o
  | _ -> err "unexpected dest_mem operand"

let s_pair (s1:string) (s2:string): string = s1 ^ ", " ^ s2

let bin_operands (ctxt:string) (args:operand list): string =
  match args with
  | [_; OReg r1; o2] -> s_pair (s_reg r1) (src_operand ctxt o2)
  | _ -> err "unexpected bin operands"

let bin_lock (args:operand list): string =
  match args with
  | _ when not !check_concurrent -> ""
  | [_; OReg r1; _] -> ""
  | _ -> "lock "

let shift_operands (ctxt:string) (args:operand list): string =
  match args with
  | [_; OReg r1; OConst i] -> s_pair (s_reg r1) i
  | [_; OReg r1; OReg Ecx] -> s_pair (s_reg r1) "cl"
  | _ -> err "unexpected shift operands"

let mul_operands (ctxt:string) (args:operand list): string =
  (* TODO: operand o3 cannot be a constant *)
  match args with
  | ([_; o3]) -> src_operand ctxt o3
  | _ -> err "unexpected mul operands"

let div_operands (ctxt:string) (args:operand list): string =
  (* TODO: operand o3 cannot be a constant *)
  match args with
  | [_; o3] -> r_operand o3
  | _ -> err "unexpected div operands"

let unary_operands1 (ctxt:string) (args:operand list): string =
  match args with
  | [_; o1] -> (dest_mem_operand ctxt W32 o1)
  | _ -> err "unexpected unary operands"

let unary_operands_small (args:operand list): string =
  match args with
  | [_; OReg r1] -> (sw_reg W8 r1)
  | _ -> err "unexpected small unary operands"

let unary_lock (args:operand list): string =
  match args with
  | _ when not !check_concurrent -> ""
  | [_; OReg r1] -> ""
  | _ -> "lock "

let lea_operands (ctxt:string) (args:operand list): string =
  match args with
  | [_; OReg rd; o2] -> s_pair (s_reg rd) (mem_operand W32 o2)
  | _ -> err "unexpected lea operands"

let lea_signed_index_operands (ctxt:string) (args:operand list): string =
  match args with
  | [_; OReg rd; OReg r1; OExp (Some c1); OReg r2; OConst c2] ->
      s_pair (s_reg rd) ("dword ptr [" ^ (s_reg r1) ^ " + " ^ (c1.ToString()) ^ " * " ^ (s_reg r2) ^ " + " ^ c2 ^ "]")
  | _ -> err "unexpected lea_signed operands"

let load_operands (ctxt:string) (width:width) (args:operand list): string =
  match args with
  | [_; _; _; OReg rd; o2] -> s_pair (s_reg rd) (mem_operand width o2)
  | _ -> err "unexpected load operands"

let iom_reg_load_operands (ctxt:string) (width:width) (args:operand list): string =
  match args with
  | [OExp _; OReg rd; o2] -> s_pair (s_reg rd) (mem_operand width o2)
  | _ -> err "unexpected iom_reg_load operands"

let store_operands (ctxt:string) (width:width) (args:operand list): string =
  match args with
  | [_; _; _; o1; o2] -> s_pair (mem_operand width o1) (simple_w_operand width o2)
  | _ -> err "unexpected store operands"

let idt_store_operands (ctxt:string) (width:width) (args:operand list): string =
  match args with
  | [OExp _; OExp _; OExp _; o1; o2] -> s_pair (mem_operand width o1) (simple_w_operand width o2)
  | _ -> err "unexpected idt store operands"

let iom_reg_store_operands (ctxt:string) (width:width) (args:operand list): string =
  match args with
  | [OExp _; o1; o2] -> s_pair (mem_operand width o1) (simple_w_operand width o2)
  | _ -> err "unexpected iom_reg_store operands"

let lidt_operands (ctxt:string) (args:operand list): string =
  match args with
  | [o] -> "fword ptr [" ^ (addr_operand o) ^ "]"
  | _ -> err "unexpected lidt operands"

let cmp_operands (ctxt:string) (args:operand list): string =
  match args with
  (* TODO: o1 cannot be OConst *)
  (* TODO: support more cases ? *)
  | [_; OReg r1; o2] -> s_pair (s_reg r1) (src_mem_operand ctxt W32 o2)
  | [_; o1; OReg r2] -> s_pair (src_mem_operand ctxt W32 o1) (s_reg r2)
  | [_; o1; (OConst c2) as o2] -> s_pair (src_mem_operand ctxt W32 o1) (src_operand ctxt o2)
  | _ -> err "unexpected cmp operands"

let cmpxchg_operands (ctxt:string) (args:operand list): string =
  match args with
  | [o1; OReg r2] -> s_pair (mem_operand W32 o1) (s_reg r2)
  | _ -> err "unexpected operands"

let launch_operands (ctxt:string) (args:operand list): string =
  match args with
  | [_;_;_;_;_;_;_;_;_] -> "ebx" //(s_reg r)
  | _ -> err "unexpected launch operands"

let print_ins (ctxt:string) (i:string) (args:operand list): unit =
  let bin s = print_endline ("    " ^ (bin_lock args) ^ s ^ " " ^ (bin_operands ctxt args)) in
  let check_over () = print_endline "    jc _?Overflow" in
  // Note: when check_concurrent is true, instructions with multiple memory accesses must be marked "lock"
  // (currently, these are just the bin_operands and unary_operands instructions whose destination is memory, plus cmpxchg)
  match i with
  | "DropTempRegs" -> ()
  | "Mov" -> bin "mov"
  | "Not" -> print_endline ("    " ^ (unary_lock args) ^ "not " ^ (unary_operands1 ctxt args))
  | "Add" -> bin "add"
  | "AddCarry" -> bin "adc"
  | "AddChecked" -> bin "add"; check_over ()
  | "Sub" -> bin "sub"
  | "SubChecked" -> bin "sub"; check_over ()
  | "Mul" -> print_endline ("    mul " ^ (mul_operands ctxt args))
  | "Mul64" -> print_endline ("    mul " ^ (mul_operands ctxt args))
  | "MulChecked" -> print_endline ("    mul " ^ (mul_operands ctxt args)); check_over ()
  | "Div" -> print_endline ("    div " ^ (div_operands ctxt args))
  | "And" -> bin "and"
  | "Or" -> bin "or"
  | "Xor" -> bin "xor"
  | "Shl" -> print_endline ("    shl " ^ (shift_operands ctxt args))
  | "Shr" -> print_endline ("    shr " ^ (shift_operands ctxt args))
  | "Rol" -> print_endline ("    rol " ^ (shift_operands ctxt args))
  | "Ror" -> print_endline ("    ror " ^ (shift_operands ctxt args))
  | "GetCf" -> print_endline ("    " ^ (unary_lock args) ^ "setc " ^ (unary_operands_small args))
  | "Cmp" -> print_endline ("    cmp " ^ (cmp_operands ctxt args))
// TODO  | "Cmpxchg" -> print_endline ("    lock cmpxchg " ^ (cmpxchg_operands ctxt args))
  | "KeyboardDataIn8" -> print_endline "    in al, 060h"
  | "KeyboardStatusIn8" -> print_endline "    in al, 064h"
  | "SerialDbgConfigOut" -> print_endline "    out dx, al"
  | "SerialDbgDataOut8" -> print_endline "    out dx, al"
  | "SerialDbgStatusOut8" -> print_endline "    in al, dx"
(*
  | "SerialDbgDataIn8" -> print_endline "    in al, dx"
  | "SerialDbgStatusIn8" -> print_endline "    in al, dx"
  | "SampleIn32" -> print_endline ("    rdrand eax")
  | "PicOut8" -> print_endline "    out dx, al"
  | "PitModeOut8" -> print_endline "    out 43h, al"
  | "PitFreqOut8" -> print_endline "    out 40h, al"
*)
  | "PciConfigAddrOut32" -> print_endline "    out dx, eax"
  | "PciConfigDataOut32" -> print_endline "    out dx, eax"
  | "PciConfigDataIn32" -> print_endline "    in eax, dx"
  | "DEV_PciConfigDataOut32" -> print_endline "    out dx, eax"
  | "DEV_PciConfigDataIn32" -> print_endline "    in eax, dx"
(*
  | "RoLoadU8" ->
      print_endline ("    movzx " ^ (load_operands ctxt W8 args))
  | "RoLoadS8" ->
      print_endline ("    movsx " ^ (load_operands ctxt W8 args))
  | "RoLoadU16" ->
      print_endline ("    movzx " ^ (load_operands ctxt W16 args))
  | "RoLoadS16" ->
      print_endline ("    movsx " ^ (load_operands ctxt W16 args))
  | "RoLoad32"
  | "SectionLoad" ->
*)
  | "Load" -> print_endline ("    mov " ^ (load_operands ctxt W32 args))
//  | "IomRegLoad" | "PciMemLoad32" ->
//      print_endline ("    mov " ^ (iom_reg_load_operands ctxt W32 args))
  | "VgaTextStore16" -> print_endline ("    mov " ^ (store_operands ctxt W16 ((OExp None)::args)))
  | "VgaDebugStore16" -> print_endline ("    mov " ^ (store_operands ctxt W16 ((OExp None)::(OExp None)::args)))
(*
  | "IdtStore" ->
      print_endline ("    mov " ^ (idt_store_operands ctxt W32 args))
  | "IomRegStore" | "PciMemStore32" ->
      print_endline ("    mov " ^ (iom_reg_store_operands ctxt W32 args))
*)
  | "Store" -> print_endline ("    mov " ^ (store_operands ctxt W32 args))
  //| "SectionStore" | "IomStore" ->
  | "ghost_IomEnabled" -> print_endline "    ; instr_ghost_IomEnabled" // TODO: this is not an instruction
//  | "Lidt" -> print_endline ("    lidt " ^ (lidt_operands ctxt args))
  | "Lea" -> print_endline ("    lea " ^ (lea_operands ctxt args))
  | "LeaUnchecked" -> print_endline ("    lea " ^ (lea_operands ctxt args))
  | "LeaSignedIndex" -> print_endline ("    lea " ^ (lea_signed_index_operands ctxt args))
  | "Rdtsc" -> print_endline ("    rdtsc")
  | "Launch" -> print_endline ("     jmp " ^ (launch_operands ctxt args))
  | _ ->
    (
      let  load32 o1 o2 = print_endline ("    mov "   ^ (s_pair (r_operand o1) (mem_operand W32 o2))) in
      let store32 o1 o2 = print_endline ("    mov "   ^ (s_pair (mem_operand W32 o1) (simple_w_operand W32 o2))) in
      let   load8 o1 o2 = print_endline ("    movzx " ^ (s_pair (r_operand o1) (mem_operand W8 o2))) in
      let  store8 o1 o2 = print_endline ("    mov "   ^ (s_pair (mem_operand W8 o1) (simple_w_operand W8 o2))) in 
      match (i, args) with
      | ("DeviceLoad", [_; _; o1; o2]) -> load32 o1 o2
      | ("DeviceStore", [_; _; o1; o2 ]) -> store32 o1 o2
      | ("PciMemLoad32", [_; _; _; o1; o2]) -> load32 o1 o2
      | ("PciMemStore32", [_; _; _; o1; o2]) -> store32 o1 o2
      | ("ActivateDataSelector", [_; _; _; OExp _; OExp _; OReg r; OSelector s]) ->
          print_endline ("    mov " ^ (s_pair (seg_reg s) (sw_reg W16 r)))
      | ("LoadGDT", [_; _; _; OExp _; OExp _; o]) ->
          print_endline ("    lgdt fword ptr [" ^ (addr_operand o) ^ "]")
      | ("ReadCR0", [_; _; OReg r]) -> print_endline ("    mov " ^ (s_reg r) ^ ", cr0")
      | ("WriteCR0", [_; _; OReg r]) -> print_endline ("    mov cr0, " ^ (s_reg r) )
      | ("WriteCR3", [_; _; OReg r]) -> print_endline ("    mov cr3, " ^ (s_reg r) ) 
      | ("IoMemAddrRead",  [_;o1;o2]) ->  load8 o1 o2
      | ("IoMemAddrWrite", [_;o1;o2]) -> store8 o1 o2
      | _ -> err ("instruction " ^ i ^ " : unsupported instruction or operands")
    )

let print_ins_group (inss:(string * string * operand list) list): unit =
  let inss = List.map (fun (c, i:string, a) ->
      if not (i.StartsWith("instr_")) then err ("unsupported instruction: " + i) else
      (c, i.Substring("instr_".Length), a)) inss in
  match inss with
  | [(ctxt, i, args)] -> print_ins ctxt i args
  | [(_, "SubNoFlags", [_; OReg "ESP"; OConst "4"]);
     (_, "StoreStack", [_; _; _; OOffset ("ESP", "0"); OReg r])] ->
      print_endline ("    push " ^ (s_reg r))
  | [(_, "Load", [_; _; _; OTmpReg "TMP1"; omem]);
     (_, "Sub",  [_; OReg r; OTmpReg "TMP1"])] ->
     // TODO: check for yields
      print_endline ("    sub " ^ (s_reg r) ^ ", " ^ (mem_operand W32 omem))
  | [(_,    "Load", [_; _; _; OTmpReg "TMP1"; omem]);
     (ctxt, "Cmp",  [_; OTmpReg "TMP1"; (OReg _ | OConst _) as o2])] ->
      print_endline ("    cmp " ^ (mem_operand W32 omem) ^ ", " ^ (src_operand ctxt o2))
  | _ -> err ("unrecognized instruction group: " ^ (String.concat ", " (List.map (fun (_, i, _) -> i) inss)))

let rec print_stmt_group (stmts:(insCtxt * loc * stmt) list): unit =
  let rec get_ins_group stmts =
    match stmts with
    | [] -> []
    | ((ctxt, varMap), l, SInline (_, p, args, []))::tl ->
        (ctxt, p, (List.map (operand_of_exp varMap) args))::(get_ins_group tl)
    | (_, l, _)::_ -> err ("unrecognized instruction at location " ^ (string l))
  let print_yielded stmts =
    match stmts with
    | [] -> ()
    | [((ctxt, _), _, SGoto l)] ->
        print_endline ("    jmp " ^ (label ctxt l))
    | [ins1; ins2; ins3; ins4; (_, l, SReturn)] ->
      (
        match get_ins_group [ins1; ins2; ins3; ins4] with
        | [(_, "instr_LoadStack", [_; _; _; OTmpReg "TMP1"; OOffset ("ESP", "0")]);
           (_, "instr_AddNoFlags", [_; OReg "ESP"; OConst "4"]);
           (_, "instr_Ret", _);
           (_, "instr_DropTempRegs", _)] when not !x64 ->
            print_endline "    ret"
        | inss -> err ("at location " ^ (string l) ^ ": incorrect (32-bit) ret: " ^ (String.concat ", " (List.map (fun (_, i, _) -> i) inss)))
        )

    | [ins1; ins2; ins3; ins4; ins5; (_, l, SReturn)] ->
      (
        match get_ins_group [ins1; ins2; ins3; ins4; ins5] with
        //64 bit return
        | [(_, "instr_LoadStack", [_; _; _; OTmpReg "TMP1"; OOffset ("ESP", "0")]);
           (_, "instr_LoadStack", [_; _; _; OTmpReg "TMP2"; OOffset ("ESP", "4")]);
           (_, "instr_AddNoFlags", [_; OReg "ESP"; OConst "8"]);
           (_, "instr_Ret", _);
           (_, "instr_DropTempRegs", _)] when !x64 ->
            print_endline "    ret"
        | inss -> err ("at location " ^ (string l) ^ ": incorrect (64-bit) ret: " ^ (String.concat ", " (List.map (fun (_, i, _) -> i) inss)))
      )

// TODO:    | [(_, _, SInline ("instr_IRet", [])); (_, _, SIReturn)] -> print_endline "    iretd"
    | [((ctxt, _), _, SIfJcc (_, jcc, l))] ->
      (
        // REVIEW: maybe redesign the AST rather than matching on strings?
        match jcc with
          | "Je" | "Jne" | "Jbe" | "Jb" | "Jae" | "Ja" ->
            print_endline ("    " ^ (jcc.ToLower ()) ^ " " ^ (label ctxt l))
          | _ -> err ("unexpected conditional jump: " + jcc)
      )
    | [ins1; ins2; ins3; (_, l, SCall (_, p, _))] ->
      (
        match get_ins_group [ins1; ins2; ins3] with
        | [(_, "instr_SubNoFlags", [_; OReg "ESP"; OConst "4"]);
           (_, "instr_MovNextEip32", [_; OTmpReg "TMP1"]);
           (_, "instr_StoreStack", [_; _; _; OOffset ("ESP", "0"); OTmpReg "TMP1"]);
          ] when not !x64 ->
            print_endline ("    call " ^ (proc_name p))
        | inss -> err ("at location " ^ (string l) ^ ": incorrect (32-bit) call: " ^ (String.concat ", " (List.map (fun (_, i, _) -> i) inss)))
      )

    //64 bit call
    | [ins1; ins2; ins3; ins4; (_, l, SCall (_, p, _))] ->
      (
        match get_ins_group [ins1; ins2; ins3; ins4] with
        | [(_, "instr_SubNoFlags", [_; OReg "ESP"; OConst "8"]);
           (_, "instr_MovNextEip64", [_; OTmpReg "TMP1"; OTmpReg "TMP2"]);
           (_, "instr_StoreStack", [_; _; _; OOffset ("ESP", "0"); OTmpReg "TMP1"]);
           (_, "instr_StoreStack", [_; _; _; OOffset ("ESP", "4"); OTmpReg "TMP2"]);
          ] when !x64 ->
            print_endline ("    call " ^ (proc_name p))
        | inss -> err ("at location " ^ (string l) ^ ": incorrect (64-bit) call: " ^ (String.concat ", " (List.map (fun (_, i, _) -> i) inss)))
      )

    | (_, l, _)::_ ->
        try print_ins_group (get_ins_group stmts)
        with Err e -> err ("at location " ^ (string l) ^ ": " ^ (string e))
    in
  match stmts with
  | [] -> ()
  | [((ctxt, _), _, SLabel l)] -> print_endline ("  " ^ label ctxt l ^ ":")
  | (_, _, SYield _)::tl -> print_yielded tl
  | _ when not !check_concurrent -> print_yielded stmts
  | (_, l, _)::_ -> err ("missing yield before instruction at location " ^ (string l))

// expand all inline procedure calls, and eliminate ghost operations
let rec expand_inline_calls (ic:insCtxt) (InlineMap inlines) (l:loc, s:stmt):(insCtxt * loc * stmt) list list =
  match s with
  | SLabel _ | SGoto _ | SReturn | SIReturn | SYield _ | SIfJcc _ | SCall _ -> [[(ic, l, s)]]
  | SAssert _ | SSplit | SAssign _ | SIfGhost _ | SForallGhost _ | SExistsGhost _ -> []
  | SGroup b -> [List.concat (List.collect (expand_inline_calls ic (InlineMap inlines)) b)]
  | SInline (_, p, _, []) when p.StartsWith("instr_") -> [[(ic, l, s)]]
  | SInline (_, p, _, []) when p.StartsWith("construct##") -> []
  | SInline (_, p, _, []) when p.StartsWith("destruct##") -> []
  | SInline (_, p, args, _) ->
      let (_, varMap) = ic in
      let (inline_inlines, inline_ic, stmts) =
        try List.assoc p inlines (List.map (operand_of_exp varMap) args)
        with :? System.Collections.Generic.KeyNotFoundException as x ->
          err ("at location " ^ (string l) ^ ": procedure " ^ p ^ " not found")
        in
      List.collect (expand_inline_calls inline_ic inline_inlines) stmts

let print_decl (inlines:inlineMap) (_, d:decl): unit =
  match d with
  | DType _ -> ()
  | DFunDecl (x, None, _, Some (EInt i), None, _) when BigInt.Zero <= i && i < (BigInt.Parse "4294967296") ->
      print_endline ("?_" ^ x ^ " EQU " ^ ((string)i))
  | DFunDecl _ -> ()
  | DStatic x ->
      print_endline ".data";
      print_endline "align 4";
      print_endline ("?_?ADDR__" ^ x ^ " DD 0")
  | DStaticGhost _ -> ()
  | DProc (p, pk, Inline, ps, _, _, Some (_, b)) -> ()
  | DProc (p, _, Outline, _, _, _, Some (_, b)) ->
      print_endline ".code";
      print_endline "align 16";
      print_endline ((proc_name p) ^ " proc");
      let stmts = List.collect (expand_inline_calls (p, []) inlines) b in
      List.iter print_stmt_group stmts;
      print_endline ((proc_name p) ^ " endp")
  | DProc (_, _, _, _, _, _, None) -> ()

#nowarn "40"
let rec print_modules (ghost_procs:string list) (InlineMap inlines) (p:(_module * _module) list): unit =
  let find_all_procs (_, d:decl) =
    match d with
    | DType _ | DFunDecl _ | DStatic _ | DStaticGhost _ -> []
    | DProc (x, pk, _, _, _, _, _) -> [x]
  let find_ghost_procs (_, d:decl) =
    match d with
    | DType _ | DFunDecl _ | DStatic _ | DStaticGhost _ -> []
    | DProc (x, pk, _, _, _, _, _) -> (match pk with Implementation -> [] | Procedure (PReal, _) -> [] | Procedure (PGhost, _) -> [x])
  let add_inline (ghost_procs:string list) (_, d:decl):inlinePreMap =
    match d with
    | DType _ | DFunDecl _ | DStatic _ | DStaticGhost _ -> []
    | DProc (_, _, _, _, _, _, None) -> []
    | DProc (p, pk, inlining, ps, _, _, Some (_, b)) ->
        [(p, fun args ->
          match inlining with
          | Inline ->
              let ctxt = gensym () in
              let varMap = List.zip (List.map (fun (x, _, _) -> x) ps) args in
              let stmts = if List.mem p ghost_procs then [] else b in
              ((ctxt, varMap), stmts)
          | Outline -> err ("cannot inline " ^ p))]
    in
  match p with
  | [] -> ()
  | (intf, impl)::ms ->
      let intf_procs = List.collect find_all_procs intf.mDecls in
      let intf_ghost_procs = (List.collect find_ghost_procs intf.mDecls) @ ghost_procs in
      let impl_ghost_procs = (List.collect find_ghost_procs impl.mDecls) @ intf_ghost_procs in
      let inft_pre_inlines = List.collect (add_inline intf_ghost_procs) intf.mDecls in
      let impl_pre_inlines = List.collect (add_inline impl_ghost_procs) impl.mDecls in
      let pre_inlines = inft_pre_inlines @ impl_pre_inlines in
      let rec lazy_impl_inlines = lazy (List.map (fun (x, f) ->
        (x, fun args -> let (ic, ss) = f args in (InlineMap (lazy_impl_inlines.Force() @ inlines), ic, ss))) pre_inlines) in
      let impl_inlines = lazy_impl_inlines.Force() in
      let intf_inlines = List.filter (fun (x, _) -> List.mem x intf_procs) impl_inlines in
      print_endline (";; BEGIN_MODULE: " + impl.mName);
      List.iter (print_decl (InlineMap (intf_inlines @ inlines))) intf.mDecls;
      List.iter (print_decl (InlineMap (impl_inlines @ inlines))) impl.mDecls;
      print_endline (";; END_MODULE: " + impl.mName);
      print_modules intf_ghost_procs (InlineMap (intf_inlines @ inlines)) ms

let rec print_program (inlines:inlineMap) (p:(_module * _module) list): unit =
  //if not !x64 then (
  print_endline ".686p";
  print_endline ".model flat";
  //);
  print_modules [] inlines p;
  print_endline "end";
  ()

(* Each command-line argument is the name of a module *)
(* Each module M must contain two files: M_i.bpl and M.bpl *)
let main (argv) =
  let print_error_prefix () = print_endline ("error near line " + (string !line) + " of file " + !file) in
  try
  (
    let mods_rev = ref ([]:(bool * string) list) in
    let link = ref false in
    let outfile = ref (None:string option) in
    let symdiff_file = ref (None:string option) in
    let distinctLinearInts = ref false in
    let add_mod (trusted:bool) (s:string) = mods_rev := (trusted, s)::(!mods_rev) in 
    Arg.parse_argv (ref 0) argv
      [
        ("-trusted" , Arg.String (add_mod true), "Trusted module");
        ("-verify"  , Arg.Clear link           , "Verify single module");
        ("-link"    , Arg.Set link             , "Link modules together and generate code");
        ("-symdiffok" , Arg.Set symdiff_allow, "Allow relational specifications for symdiff");
        ("-symdiffms" , Arg.String (fun s -> symdiff_allow := true; symdiff := true; symdiff_file := Some s), "Generate symdiff mutual summary file for relational checks");
        ("-distinctLinearInts", Arg.Set distinctLinearInts, "Use axioms ensuring distinctness of linear integers (sound, but may be slow)");
        ("-out"     , Arg.String (fun s -> outfile := Some s) , "Specify output file");
        ("-def"     , Arg.String (fun s -> Lex.macros := Map.add s [] !Lex.macros), "Define a macro (as an empty string) for use by ifdef/ifndef");
        ("-x64"     , Arg.Set x64              , "Compile 64 bit binaries");
      ]
      (add_mod false)
      "error parsing arguments";
    let mods = List.rev (!mods_rev) in
    let parse_file comment name =
      print_endline (comment + "parsing " + name);
      file := name;
      line := 1;
      Parse.start Lex.token (Lexing.from_channel (open_in name)) in
    if !link then
      let (_, modIfcs, modImps) = List.foldBack (fun (_, x) (b, l1, l2) ->
        (not b, (if b then l1 else x::l1), (if b then x::l2 else l2))) mods (true, [], []) in
      let modIfcImps = List.combine modIfcs modImps in
      let modules = List.map (fun (xIfc, xImp) -> (parse_file ";;" xIfc, parse_file ";;" xImp)) modIfcImps in
      link_check_modules modules;
      print_program (InlineMap []) modules
    else
      (match !symdiff_file with None -> () | Some s -> symdiff_writer := ((new System.IO.StreamWriter(new System.IO.FileStream(s, System.IO.FileMode.Create))):>System.IO.TextWriter));
      let stream =
        match !outfile with
        | None -> System.Console.Out
        | Some s -> (new System.IO.StreamWriter(new System.IO.FileStream(s, System.IO.FileMode.Create))):>System.IO.TextWriter in
      if (!distinctLinearInts) then
        (
          stream.WriteLine ("function {:builtin \"MapConst\"} MapConstBool(bool) : [int]bool;");
          stream.WriteLine ("function {:inline} {:linear \"our\"} LinearIntDistinctness(x:int) : [int]bool { MapConstBool(false)[x := true] }")
        );
      let xms_rev =
        List.fold
          (fun xms_rev (_, x:string) ->
            if x.StartsWith("/trustedBoogie:") then
              let x = x.Substring("/trustedBoogie:".Length) in
              let f = new System.IO.StreamReader(new System.IO.FileStream(x, System.IO.FileMode.Open, System.IO.FileAccess.Read)) in
              stream.WriteLine ("#line 1 " + x);
              stream.WriteLine (f.ReadToEnd());
              f.Close ();
              xms_rev
            else
              let m = parse_file "//" x in
              (x, m)::xms_rev)
          []
          mods in
      let ms_rev = List.map snd xms_rev in
      (match ms_rev with
      | [] -> ()
      | {mIsImpl = false}::_ -> ()
      | ({mName = imName; mIsImpl = true} as m)::({mName = ifName; mIsImpl = false} as i)::ifs when imName = ifName ->
          check_module (List.rev ifs) i m
      | _ -> err "expected last file to be interface, or last two files to be interface/implementation");
      stream.WriteLine ("#line 1 fake entry point");
      let publics = List.collect (fun m -> if m.mIsImpl then [] else m.mDecls) ms_rev in
      let impls = List.collect (fun m -> if m.mIsImpl then m.mDecls else []) ms_rev in
      let all_vars = List.collect (fun (_, d) -> match d with DStaticGhost (x, _, _, _) -> [x] | _ -> []) publics in
      let all_typedefs = List.collect (fun (_, d) -> match d with DType (x, _, _, Some _) -> [x] | _ -> []) impls in
      let all_procs = List.collect (fun (_, d) ->
        match d with DProc ((x, Procedure _, _, _, _, _, _) as p) -> [(x, p)] | _ -> []) (publics @ impls) in
      let ctxt x =
        {
          all_vars = (if !check_concurrent then all_vars else []);
          all_typedefs = all_typedefs;
          all_procs = all_procs;
          publics = publics;
          print_out = stream;
          cur_loc = ref (x, 1);
          cur_indent = ref "";
        } in
// TODO:      (if not !symdiff then emit_entry_point { print_out = stream; cur_loc = ref ("fake entry point", 1); cur_indent = ref ""; } publics);
      stream.WriteLine("function {:linear \"our\"} OurCollector(x:[int]bool):[int]bool { x }");
      List.iter (fun (x, m) ->
          (if !symdiff then
            symdiff_globals := (List.collect (fun (_, d) ->
              match d with DStaticGhost (x, t, lin, _) -> [(x, t, lin)] | _ -> []) (List.collect (fun m -> m.mDecls) (List.rev ms_rev)));
            symdiff_consts := (List.collect (fun (_, d) ->
              match d with DFunDecl (x, None, _, _, _, _) -> [x] | _ -> []) (List.collect (fun m -> m.mDecls) (List.rev ms_rev))));
          stream.WriteLine ("#line 1 " + x);
          emit_module (ctxt x) m)
        (List.rev xms_rev);
      (if !symdiff then (!symdiff_writer).Close ());
      stream.Close ()
  )
  with
     | (Err s) as x -> (print_endline "error:"; print_endline s; print_endline (x.ToString ()); exit 1)
     | ParseErr x -> (print_error_prefix (); print_endline x; exit 1)
     | :? System.ArgumentException as x -> (print_error_prefix (); print_endline (x.ToString ()); exit 1)
     | Failure x -> (print_error_prefix (); print_endline x; exit 1)
     | x -> (print_endline (x.ToString ()); exit 1)
;;

(* TODO: check that procedure implementations are correctly placed and not duplicated? *)
(* TODO: check that no procedures are recursive, even if they aren't used (e.g. readField) *)

let () = main (System.Environment.GetCommandLineArgs ())

