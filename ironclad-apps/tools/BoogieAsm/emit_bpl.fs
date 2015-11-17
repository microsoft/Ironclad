open Ast
open Parse
open Parse_util
open Microsoft.FSharp.Math

let symdiff = ref false
let symdiff_allow = ref false
let symdiff_lin_decls = ref (["me"]) // symdiff doesn't handle linear variables yet
let symdiff_invariant = ref ("", (([]:string list), ([]:(string * string) list)))
let symdiff_proc = ref ("", (fun loop -> ""))
let symdiff_globals = ref ([]:pformal list)
let symdiff_consts = ref ([]:string list)
let symdiff_rets = ref ([]:string list)
let symdiff_params = ref ([]:string list)
let symdiff_locals = ref ([]:string list)
let symdiff_writer = ref (null:System.IO.TextWriter)
let symdiff_proc_mods = ref ([]:(string * pformal list) list)
let symdiff_proc_local_clones = ref ([]:(string * int ref) list)
let symdiff_proc_global_clones = ref ([]:(string * int ref) list)
let symdiff_current_exp_scope = ref ([]:string list)

let rec sep_list (sep:string) (l:string list) =
  match l with
  | [] -> ""
  | [x] -> x
  | h::t -> h + sep + (sep_list sep t)

let rec string_of_typ (t:typ):string =
  match t with
  | TInt -> "int"
  | TBool -> "bool"
  | TReal -> "real"
  | TName x -> x
  | TMap (t1, t2) -> "[" + (string_of_typ t1) + "]" + (string_of_typ t2)

let string_of_lin_param (l:linearity):string =
  match (!symdiff, l) with
  | (false, Lin (LinVar, LinOur)) -> "{:linear_in \"our\"}"
  | (false, Lin (LinConst, LinOur)) -> "{:linear \"our\"}"
  | (false, Lin (LinVar, LinMy)) -> "{:linear_in \"my\"}"
  | (false, Lin (LinConst, LinMy)) -> "{:linear \"my\"}"
  | _ -> ""
let string_of_lin_var (l:linearity):string =
  match (!symdiff, l) with
  | (false, Lin (_, LinOur)) -> "{:linear \"our\"}"
  | (false, Lin (_, LinMy)) -> "{:linear \"my\"}"
  | _ -> ""
let string_of_quant (q:quant):string = match q with Forall -> "forall" | Exists -> "exists" | Lambda -> "lambda"
let string_of_formal ((x, t):formal) = x + ":" + (string_of_typ t)
let string_of_pformal_param ((x, t, l):pformal) = (string_of_lin_param l) + x + ":" + (string_of_typ t)
let string_of_pformal_var ((x, t, l):pformal) = (string_of_lin_var l) + x + ":" + (string_of_typ t)
let string_of_formals (fs:formal list) = String.concat "," (List.map string_of_formal fs)
let string_of_pformals_param (fs:pformal list) = String.concat "," (List.map string_of_pformal_param fs)
let string_of_pformals_var (fs:pformal list) = String.concat "," (List.map string_of_pformal_var fs)

type rel = NoRel | RelPre of bool | RelPost of bool
type side = Outside | Left | Right

let rec string_of_exp_r ((r:rel), (side:side)) (e:exp):string =
  let symdiff_nonglobal x = (List.mem x !symdiff_rets) || (List.mem x !symdiff_params) || (List.mem x !symdiff_locals) in
  let symdiff_const x = List.mem x !symdiff_consts in
  let pre loop n x =
    "v" + n + "_u."
      + ( if symdiff_nonglobal x then
            (if loop then "in_" else "") + x
          else if symdiff_const x then x
          else "" + x + "_old") in
  let post loop n x =
    "v" + n + "_u."
      + ( if symdiff_nonglobal x then
            (if loop then (if List.mem x !symdiff_params then "in_" else "out_") else "") + x
          else if symdiff_const x then x
          else "" + x + "_")
  let is_datatype_field (x:id) = x.Contains("#") && x.IndexOf('#') == x.LastIndexOf('#') in
  match (r, side, e) with
  | (_, _, EVar x) when List.mem x !symdiff_current_exp_scope -> "(" + x + ")"
  | ((RelPre _ | RelPost _), Outside, EVar x) -> err ("variable " + x + " must appear inside left or right expression")
  | (NoRel, _, EOp (Uop ("left" | "right"), _)) -> err ("'left' and 'right' can only be used inside a relation expression")
  | (_, (Outside | Left), EOp (Uop "left", [e0])) -> string_of_exp_r (r, Left) e0
  | (_, (Outside | Right), EOp (Uop "right", [e0])) -> string_of_exp_r (r, Right) e0
  | (_, (Left | Right), EOp (Uop ("left" | "right"), _)) -> err ("'left' appears inside 'right', or vice-versa")
  | (RelPre loop, Left, EVar x) -> "(" + (pre loop "1" x) + ")"
  | (RelPre loop, Right, EVar x) -> "(" + (pre loop "2" x) + ")"
  | (RelPost loop, Left, EVar x) -> "(" + (post loop "1" x) + ")"
  | (RelPost loop, Right, EVar x) -> "(" + (post loop "2" x) + ")"
  | (RelPost loop, Left, EOp (Uop "old", [EVar x])) -> "(v1_u." + x + "_old)"
  | (RelPost loop, Right, EOp (Uop "old", [EVar x])) -> "(v2_u." + x + "_old)"
  | ((RelPre _ | RelPost _), _, EApply (x, es)) when not (is_datatype_field x) ->
      "(v2_u." + x + "(" + (string_of_exps (r, side) es) + "))"
  | _ -> string_of_exp_norel (r, side) e
and string_of_exp_norel (r:rel * side) (e:exp):string =
  let s =
    match e with
    | EVar x -> x
    | EInt i -> string i
    | EReal r -> r
    | EBv32 i -> (string i) + "bv32"
    | EBool true -> "true"
    | EBool false -> "false"
    | EOp (Bop op, [e1; e2]) -> (string_of_exp_r r e1) + op + (string_of_exp_r r e2)
    | EOp (Uop "relation", _) -> err "'relation' and 'public' can only be used around an entire 'requires', 'ensures', or 'invariant'"
    | EOp (Uop ("left" | "right"), _) -> err "internal error: left/right"
    | EOp (Uop op, [e1]) -> op + (string_of_exp_r r e1)
    | EOp (Subscript, [e1; e2]) -> (string_of_exp_r r e1) + "[" + (string_of_exp_r r e2) + "]"
    | EOp (Update, [e1; e2; e3]) -> (string_of_exp_r r e1) + "[" + (string_of_exp_r r e2) + ":=" + (string_of_exp_r r e3) + "]"
    | EOp (Cond, [e1; e2; e3]) -> "if " + (string_of_exp_r r e1) + " then " + (string_of_exp_r r e2) + " else " + (string_of_exp_r r e3)
    | EOp _ -> err "internal error: EOp"
    | EApply (x, es) -> x + "(" + (string_of_exps r es) + ")"
    | EQuant (_, [], _, e) -> string_of_exp_r r e
    | EQuant (q, fs, ts, e) ->
      (
        let save_scope = !symdiff_current_exp_scope in
        symdiff_current_exp_scope := (List.map fst fs) @ !symdiff_current_exp_scope;
        let rhs = (string_of_triggers r ts) + (string_of_exp_r r e) in
        symdiff_current_exp_scope := save_scope;
        (string_of_quant q) + " " + (string_of_formals fs) + "::" + rhs
      )
  in "(" + s + ")"
and string_of_exps (r:rel * side) (es:exp list):string = String.concat "," (List.map (string_of_exp_r r) es)
and string_of_trigger (r:rel * side) (t:exp list):string = "{" + (string_of_exps r t) + "}"
and string_of_triggers (r:rel * side) (ts:exp list list):string = String.concat "" (List.map (string_of_trigger r) ts)
let string_of_exp = string_of_exp_r (NoRel, Outside)
let string_of_exp_ignore_rel (r:is_relation) (e:exp):string = match r with IsRel -> "true" | NotRel -> string_of_exp e

let string_of_outs (xs:id list):string = match xs with [] -> "" | _ -> (String.concat "," xs) + " := "

let dummyCounter = ref 0;

let string_of_stmt (s:stmt):string =
  match s with
  | SLabel l -> l + ":"
  | SGoto l -> "goto " + l + ";"
  | SGroup _ -> ""
  | SIfJcc (x, cond, l) -> "call boogie_CheckJcc(me, RET, " + x + "); if (" + cond + "(.efl(" + x + "))) { goto " + l + "; }"
  | SIfGhost (e, b) -> "if (" + (string_of_exp e) + ")"
  | SForallGhost _ -> "if (*)"
  | SExistsGhost _ -> "if (*)"
  | SAssert (NotInv, e) -> "assert " + (string_of_exp e) + ";"
  | SAssert (IsInv r, e) -> "assert " + (string_of_exp_ignore_rel r e) + ";"
  | SSplit -> "assert {:split_here} true;"
  | SYield e -> incr dummyCounter; "yield; assert " + (string_of_exp e) + "; #DUMMY_LABEL" + (string !dummyCounter) + ":"
  | SAssign (x, e) -> x + " := " + (string_of_exp e) + ";"
  | SInline (xs, p, es, pars) ->
      let f x es = x + "(" + (String.concat "," ("me"::"RET"::(List.map (string_of_exp) es))) + ")" in
      "call " + (string_of_outs xs) + (f p es)
        + (String.concat "" (List.map (fun (x, es) -> " | " + f x es) pars)) + ";"
  | SCall (xs, p, es) ->
      let xr = List.hd xs in
      "call boogie_CheckCall(me, RET, " + xr + "); "
        + "call " + (string_of_outs xs) + p
        + "(" + (String.concat "," ("me"::"ReturnToCaller(" + xr + ")"::(List.map (string_of_exp) es))) + ");"
  | SReturn -> "return;"
  | SIReturn -> "return;"

let string_of_spec (s:spec):string =
  match s with
  | Requires (r, e) -> "requires " + (string_of_exp_ignore_rel r e) + ";"
  | Ensures (r, e) -> "ensures " + (string_of_exp_ignore_rel r e) + ";"
  | Modifies xs -> "modifies " + (String.concat "," xs) + ";"

let string_of_attrs (a:attr option):string = match a with None -> "" | Some s -> "{:" + s + "}"

type print_state =
  {
    all_vars:id list;
    all_typedefs:id list;
    all_procs:(id * proc_decl) list;
    publics:(loc * decl) list;
    print_out:System.IO.TextWriter;
    cur_loc:loc ref;
    cur_indent:string ref;
  }
  member this.PrintLine (s:string) =
    let (f, i) = !this.cur_loc in (this.cur_loc := (f, i + 1));
    this.print_out.WriteLine (!this.cur_indent + s)
  member this.Indent () = this.cur_indent := "  " + !this.cur_indent
  member this.Unindent () = this.cur_indent := (!this.cur_indent).Substring(2)
  member this.SetLoc (((f, i) as l):loc) =
    let (cf, ci) as cl = !this.cur_loc in
    if l = cl then ()
    else if f <> cf || i < ci || i > ci + 8 then this.cur_loc := l; this.print_out.WriteLine ("#line " + (string i) + " " + f)
    else this.PrintLine ""; this.SetLoc l

let string_of_proc_kind (pk:proc_kind):string =
  match pk with
  | Procedure (_, Atomic) -> "procedure"
  | Procedure (_, Yields) | Procedure (_, Stable) -> "procedure" // TODO: "procedure{:yields}"
  | Implementation -> "implementation"

let rename_var xs x = if List.mem x xs then "#RENAME#" + x else x in
let rename_formals xs fs = List.map (fun (x, t) -> (rename_var xs x, t)) fs in
let rec rename_exp xs e =
  let rs = List.map (rename_exp xs) in
  match e with
  | EVar x -> EVar (rename_var xs x)
  | EInt _ | EReal _ | EBv32 _ | EBool _ -> e
  | EOp (op, es) -> EOp (op, rs es)
  | EApply (x, es) -> EApply (x, rs es)
  | EQuant (q, fs, ts, e) ->
      let xs = (List.map fst fs) @ xs in
      let rs = List.map (rename_exp xs) in
      EQuant (q, rename_formals xs fs, List.map rs ts, rename_exp xs e) in

let rec symdiff_emit_linearity (state:print_state):unit =
  let assumes = List.mapi (fun i s -> "###symdiff_linearity[" + s + "] == " + (string i)) !symdiff_lin_decls in
  let terms = sep_list " && " assumes in
  state.PrintLine ("assume (exists ###symdiff_linearity:[int]int::" + terms + ");")

let symdiff_write_fun (loop:bool) (impl:bool) (pre:string list) (post:string list):unit =
  if pre = [] && post = [] then () else
  let s_loop = if loop then "_loop_" + (fst !symdiff_invariant) else "" in
  let s_pre  = String.concat "" (List.map (fun s -> " && " + s) pre) in
  let s_post = String.concat "" (List.map (fun s -> " && " + s) post) in
  let write_decl s =
    (!symdiff_writer).WriteLine(
      "function {:inline true} " + s
        + "$v1_u." + (fst !symdiff_proc) + s_loop
        + "$v2_u." + (fst !symdiff_proc) + s_loop
        + "(" + (snd !symdiff_proc loop) + "):bool")
    in
  write_decl "MP";
  (!symdiff_writer).WriteLine("{");
  (!symdiff_writer).WriteLine("  true" + s_pre);
  (!symdiff_writer).WriteLine("}");
  // warning: this does not handle recursion
  write_decl "MS";
  (!symdiff_writer).WriteLine("{")
  (!symdiff_writer).WriteLine("      (true" + s_pre + ")");
  (!symdiff_writer).WriteLine("  ==> (true" + s_post + ")");
  (!symdiff_writer).WriteLine("}");
  (!symdiff_writer).WriteLine()

// NOTE: Since we're providing symdiff with two copies of the same code,
// we can restrict programs to the special case where a call in the
// left program must match the same call in the right program (not
// another call to the same procedure).
// To encode this for SymDiff, rename the called procedure at each call site
// so that different call sites in a procedure are distinguished.
let symdiff_clone_call (state:print_state) (p:string):string =
  if not (List.mem_assoc p state.all_procs) then p else 
  let (_, _, _, _, _, specs, _) = List.assoc p state.all_procs in
  let rels = List.filter (fun (_, spec) ->
    match spec with Requires (IsRel, _) | Ensures (IsRel, _) -> true | _ -> false) specs in
  if rels = [] then p else
  let get_int_ref l =
    if not (List.mem_assoc p !l) then l := (p, ref 0)::!l;
    List.assoc p !l in
  let (li, gi) = (get_int_ref symdiff_proc_local_clones, get_int_ref symdiff_proc_global_clones) in
  incr li;
  if !li > !gi then gi := !li;
  "#clone" + (string !li) + "#" + p

let rec emit_stmt (rec_context:string * pformal list) (state:print_state) (l:loc, s:stmt):unit =
  state.SetLoc l;
  (match (rec_context, s) with
  | ((xp, (x0, _, _)::xs), SInline (_, xc, e0::es, _)) when xp = xc ->
      // inductive call to self; check termination
      let se0 = string_of_exp e0 in
      state.PrintLine ("assert 0 <= " + se0 + " && " + se0 + " < " + x0 + ";")
  | (_, SAssert (NotInv, e)) when !symdiff -> state.PrintLine ("assume " + (string_of_exp e) + ";")
  | _ -> ()
  );
  let s_clone =
    (
      match (!symdiff, s) with
      | (true, SInline (xs, p, es, pars)) -> SInline (xs, symdiff_clone_call state p, es, pars)
      | (true, SCall (xs, p, es)) -> SCall (xs, symdiff_clone_call state p, es)
      | _ -> s
    ) in
  state.PrintLine (string_of_stmt s_clone);
  (match s with
  | SAssert (IsInv IsRel, e) when !symdiff -> 
      symdiff_invariant :=
        (fst !symdiff_invariant,
          ((fst (snd !symdiff_invariant)),
            (string_of_exp_r (RelPre true, Outside) e, string_of_exp_r (RelPost true, Outside) e)::(snd (snd !symdiff_invariant))))
  | SAssert (IsInv NotRel, e) when !symdiff ->
      symdiff_invariant := (fst !symdiff_invariant,
        (((string_of_exp e)::(fst (snd !symdiff_invariant))), snd (snd !symdiff_invariant)))
  | SAssert (IsInv _, _) -> ()
  | SSplit -> ()
  | _ when !symdiff && (snd !symdiff_invariant <> ([], [])) ->
      symdiff_write_fun true false
        (List.map fst (snd (snd !symdiff_invariant)))
        (List.map snd (snd (snd !symdiff_invariant)));
      List.iter (fun x -> state.PrintLine ("assert " + x + " == " + x + ";")) !symdiff_params; // tell symdiff not to prune loop procedure's parameter list
      List.iter (fun s -> state.PrintLine ("assume " + s + ";")) (fst (snd !symdiff_invariant));
      List.iter (fun x -> state.PrintLine (x + " := " + x + ";")) !symdiff_locals; // tell symdiff not to prune loop procedure's parameter list
      symdiff_invariant := ("", ([], []))
  | _ -> ()
  );
  (match s with
  | SGroup b -> List.iter (emit_stmt rec_context state) b
  | SIfGhost (e, b) ->
    (
      state.PrintLine "{";
      state.Indent ();
      List.iter (emit_stmt rec_context state) b;
      state.Unindent ();
      state.PrintLine "}"
    )
  | SForallGhost (fs, ts, e, _, b) ->
    (
      state.PrintLine "{";
      state.Indent ();
      List.iter (fun (x, _) -> state.PrintLine ("havoc " + x + ";")) fs;
      // need some constants or havoc'd variables; declare at top level? as locals?
      List.iter (emit_stmt rec_context state) b;
      state.PrintLine ("assert " + (string_of_exp e) + ";");
      state.PrintLine ("assume false;"); // in one branch, prove assertion, then block (assume false)
      state.Unindent ();
      state.PrintLine "}"
      // in other branch, assume what was asserted, but quantify over all variables
      state.PrintLine ("assume " + (string_of_exp (rename_exp [] (EQuant (Forall, fs, ts, e)))) + ";");
    )
  | SExistsGhost (fs, ts, e) ->
    (
      state.PrintLine "{";
      state.Indent ();
      state.PrintLine ("assert " + (string_of_exp (rename_exp [] (EQuant (Exists, fs, ts, e)))) + ";");
      state.PrintLine ("assume false;"); // in one branch, prove assertion, then block (assume false)
      state.Unindent ();
      state.PrintLine "}"
      List.iter (fun (x, _) -> state.PrintLine ("havoc " + x + ";")) fs;
      // in other branch, assume what was asserted, but for newly havoc'd variables
      state.PrintLine ("assume " + (string_of_exp e) + ";")
    )
  //| SAssert (EOp (Uop "!", [EBool false])) when !symdiff -> symdiff_emit_linearity state // HACK
  | SLabel x when !symdiff -> symdiff_invariant := (x, ([], []))
  | _ -> ())

let rec emit_stmt_decl (forall_vars:id list) (state:print_state) (l:loc, s:stmt):unit =
  // HACK: we don't yet support duplicate variable names across forall statements,
  // so just declare all the variables together, and rely on Boogie to flag duplicates as errors
  let check_assign x = if List.mem x forall_vars then err ("cannot assign to readonly variable " + x) in
  match s with
  | SLabel _ | SGoto _ | SReturn | SIReturn | SIfJcc _ -> () // illegal in ghost code
  | SYield _ | SAssert _ | SSplit -> ()
  | SAssign (x, _) -> check_assign x
  | SInline (xs, _, _, _) | SCall (xs, _, _) -> List.iter check_assign xs
  | SGroup b -> List.iter (emit_stmt_decl forall_vars state) b
  | SIfGhost (_, b) -> List.iter (emit_stmt_decl forall_vars state) b
  | SForallGhost (fs, _, _, fa_vars, b) ->
    (
      List.iter
        (fun (x, t) -> state.PrintLine ("var " + x + ":" + (string_of_typ t) + ";"))
        (fs @ fa_vars);
      List.iter (emit_stmt_decl ((List.map fst fs) @ forall_vars) state) b
    )
  | SExistsGhost (fs, _, _) ->
    (
      List.iter
        (fun (x, t) -> state.PrintLine ("var " + x + ":" + (string_of_typ t) + ";"))
        fs
    )

let rec collect_forall_vars (l:loc, s:stmt):formal list =
  match s with
  | SLabel _ | SGoto _ | SReturn | SIReturn | SIfJcc _ -> []
  | SYield _ | SAssert _ | SSplit -> []
  | SAssign (x, _) -> []
  | SInline (xs, _, _, _) | SCall (xs, _, _) -> []
  | SGroup b -> List.collect collect_forall_vars b
  | SIfGhost (_, b) -> List.collect collect_forall_vars b
  | SForallGhost (fs, _, _, vars, b) -> vars @ (List.collect collect_forall_vars b)
  | SExistsGhost (fs, _, _) -> []

let emit_spec (state:print_state) (l:loc, s:spec):unit =
  state.SetLoc l;
  state.PrintLine (string_of_spec s)

// Rather than raising an error for non-terminating functions, we rewrite
// non-terminating functions to be terminating: non-terminating calls (calls that
// fail to decrease the termination metric or produce a negative termination metric)
// simply return unspecified dummy values.
let rewrite_recursive_fun (state:print_state) (x:string) (fs:formal list) (t:typ) (e:exp):exp =
  let emitted = ref false in
  let call_rec_fun (args:exp list):exp =
    let name = "##rec##" + x in
    match (fs, args) with
    | ((x0, TInt)::_, _::_) ->
      (
        if not (!emitted) then
          (
            let app = name + "(##d, " + (sep_list "," (List.map fst fs)) + ")" in
            let app0 = x + "(" + (sep_list "," (List.map fst fs)) + ")" in
            state.PrintLine ("function " + name + "(##d:int, " + (string_of_formals fs) + "):" + (string_of_typ t) + ";");
            state.PrintLine ("axiom (forall ##d:int, " + (string_of_formals fs) + "::{" + app
              + "} 0 <= " + x0 + " && " + x0 + " < ##d ==> " + app + " == " + app0 + ");");
            emitted := true
          );
        EApply (name, (EVar x0)::args)
      )
    | _ -> err ("recursive function " + x + " must have a decreasing, nonnegative integer first argument")
    in
  let rec r e =
    match e with
    | EVar _ | EInt _ | EReal _ | EBv32 _ | EBool _ -> e
    | EOp (op, es) -> EOp (op, List.map r es)
    | EApply (y, es) when x = y -> call_rec_fun (List.map r es)
    | EApply (y, es) -> EApply (y, List.map r es)
    | EQuant (q, qfs, ts, e) -> EQuant (q, qfs, List.map (List.map r) ts, r e)
    in
  r e

let rec emit_decl (state:print_state) (l:loc, d:decl):unit =
  state.SetLoc l;
  match d with
  | DType (x, _, _, None) ->
    (
      (if not (List.mem x state.all_typedefs) then state.PrintLine ("type " + x + ";"));
      state.PrintLine ("function sizeof##" + x + "(x:" + x + "):int;")
    )
  | DType (x, overload, impl, Some cs) ->
      state.PrintLine ("type{:datatype} " + x + ";");
      (if not impl then state.PrintLine ("function sizeof##" + x + "(x:" + x + "):int;"));
      state.PrintLine ("axiom (forall x:" + x + "::{sizeof##" + x + "(x)} sizeof##" + x + "(x) >= 0);");
      List.iter
        (fun (lin, c, fs) ->
          let ffs = List.map (fun (fx, ft, fl) -> (fx, ft)) fs in
          state.PrintLine ("function{:constructor} " + c + "(" + (string_of_formals ffs) + "):" + x + ";");
          (match lin with
            | Non -> ()
            | Lin (LinConst, _) -> err ("in type " + x + ", linear constructor cannot be declared const")
            | _ ->
              let sfs = string_of_pformals_param fs in
              let sfs_out = string_of_pformals_var fs in
              let sc = (string_of_lin_var lin) + "#x:" + x in
              let sc_out = (string_of_lin_param lin) + "#x:" + x in
              let sis = "is#" + c + "(#x);" in
              let ens = " ensures #x == " + c + "(" + (String.concat "," (List.map fst ffs)) + ");" in
              state.PrintLine ("procedure construct##" + c + "(#me:int, #r:ReturnTo, " + sfs + ") returns(" + sc + ");" + ens);
              state.PrintLine ("procedure destruct##" + c + "(#me:int, #r:ReturnTo, " + sc_out + ") returns(" + sfs_out + "); requires " + sis + ens));
          (List.iter (fun (fx, ft, fl) ->
              (match (lin, fl) with
                | (_, Lin (LinConst, _)) -> err ("in type " + x + ", linear field cannot be declared const")
                | (Lin (_, LinOur), Lin (_, LinMy)) -> err ("in type " + x + ", linear constructor cannot contain 'my' field")
                | _ -> ());
              match ft with
                | TInt | TBool | TReal | TMap _ -> ()
                | TName xft ->
                  let subsize = "sizeof##" + xft + "(" + fx + "#" + c + "(x))" in
                  state.PrintLine ("axiom (forall x:" + x + "::{" + subsize + "} is#" + c + "(x) ==> " + subsize + " < sizeof##" + x + "(x));"))
            fs);
          if not overload then
            List.iter
              (fun (fx, ft, _) -> state.PrintLine ("function{:inline true} ." + fx + "(x:" + x + "):" + (string_of_typ ft) + " { " + fx + "#" + c + "(x) }"))
              fs)
        cs
  | DStatic x ->
      let a = "?ADDR__" + x in
      let id = "#ID__" + x in
      state.PrintLine ("const " + a + ":int;");
      state.PrintLine ("const unique " + id + ":int;");
      state.PrintLine ("axiom StaticAddrToId(" + a + ") == " + id + ";");
      state.PrintLine ("axiom Aligned(" + a + ");");
      state.PrintLine ("axiom word(" + a + ");");
      state.PrintLine ("axiom ge(" + a + ", 4096);");
      state.PrintLine ("axiom memAddr(" + a + ");");
      state.PrintLine ("axiom !memAddrMain(" + a + ");")
  | DStaticGhost (x, t, lin, _) ->
      (if (!symdiff && lin <> Non) then symdiff_lin_decls := x::!symdiff_lin_decls);
      state.PrintLine ("var " + (string_of_lin_var lin) + x + ":" + (string_of_typ t) + ";")
  | DFunDecl (x, None, Some t, e_opt, None, None) ->
    (
      state.PrintLine ("const " + x + ":" + (string_of_typ t) + ";")
      match e_opt with None -> () | Some e -> state.PrintLine ("axiom " + x + " == " + (string_of_exp e) + ";")
    )
  | DFunDecl (x, Some fs, Some t, e_opt, a, None) ->
      let e_opt = (match e_opt with None -> None | Some e -> Some (rewrite_recursive_fun state x fs t e)) in
      state.PrintLine ("function " + (string_of_attrs a) + x + "(" + (string_of_formals fs) + ") returns(" + (string_of_typ t) + ")");
      state.PrintLine (match e_opt with None -> ";" | Some e -> "{ " + (string_of_exp e) + "}")
  | DFunDecl (x, Some fs, Some t, Some e, None, Some ts) ->
    (
      let e = rewrite_recursive_fun state x fs t e in
      let forall = (match fs with [] -> "" | _ -> "forall " + (string_of_formals fs) + "::" + (string_of_triggers (NoRel, Outside) ts)) in
      state.PrintLine
        ("axiom (" + forall
          + x + "(" + (String.concat "," (List.map fst fs)) + ") == " + (string_of_exp e) + ");");
    )
  | DFunDecl (x, _, _, _, _, _) -> err ("internal error: const/function " + x)
  | DProc (x, pk, ik, fs, rs, specs, b_opt) ->
    (
      let rec_context = (x, fs) in
      let x2 = "##verify##" + x in
      let specs =
        match pk with
        | Procedure (_, Atomic) | Implementation -> specs
        | Procedure (_, Yields) | Procedure (_, Stable) -> (l, Modifies state.all_vars)::specs in
      let fs = ("me", TInt, Lin (LinConst, LinOur))::("RET", TName "ReturnTo", Non)::fs in
      let impl_fs = List.map (fun (x, t, l) -> (x, t, Non)) fs in // Boogie only allows "linear" on proc, not impl
      let impl_rs = List.map (fun (x, t, _) -> (x, t, Non)) rs in
      let symdiff_mods =
        if not !symdiff then [] else
          match pk with
          | Procedure _ ->
              let mods = List.collect (fun s -> match s with (_, Modifies xs) -> xs | _ -> []) specs in
              let globs = List.map (fun (x, t, lin) -> (x, (t, lin))) !symdiff_globals in
              let mods = List.map (fun x -> 
                  (if not (List.mem_assoc x globs) then err ("Found " + x + " in a modifies clause.  Cannot find in global variables.")); 
                  let (t, lin) = List.assoc x globs in (x, t, lin)) mods in
              symdiff_proc_mods := (x, mods)::!symdiff_proc_mods;
              mods
          | Implementation _ -> List.assoc x !symdiff_proc_mods in
      (if !symdiff then
        symdiff_invariant := ("", ([], []));
        symdiff_proc_local_clones := [];
        let pfdecl n pre suf (x, t, _) = "v" + n + "_u." + pre + x + suf + ": " + (string_of_typ t) in
        let local_vars = match b_opt with None -> [] | Some (vars, _) -> vars in
        let ins loop n = List.map (pfdecl n (if loop then "in_" else "") "") fs in
        let outs_ins loop n = List.map (pfdecl n "in_" "") rs in
        let outs loop n = List.map (pfdecl n (if loop then "out_" else "") "") rs in
        let locals is_out n =
          List.map (pfdecl n (if is_out then "out_" else "in_") "") local_vars in
        let globals is_out n =
          List.map (pfdecl n "" (if is_out then "_" else "_old"))
            (if is_out then symdiff_mods else !symdiff_globals) in
        let vars loop n =
          if loop then
            (ins loop n) @ (outs_ins loop n) @ (locals false n) @ (globals false n) @ (globals true n)
              @ (outs loop n) @ (locals true n)
          else (ins loop n) @ (globals false n) @ (globals true n) @ (outs loop n) in
        let vars12 loop = (vars loop "1") @ (vars loop "2") in
        let f_vars loop = sep_list ", " (vars12 loop) in
        symdiff_proc := (x, f_vars);
        symdiff_rets := List.map (fun (x, _, _) -> x) rs;
        symdiff_params := List.map (fun (x, _, _) -> x) fs;
        symdiff_locals := List.map (fun (x, _, _) -> x) local_vars;
        let pres = List.collect (fun s ->
          match s with (_, Requires (IsRel, e)) -> [string_of_exp_r (RelPre false, Outside) e] | _ -> []) specs in
        let posts = List.collect (fun s ->
          match s with (_, Ensures (IsRel, e)) -> [string_of_exp_r (RelPost false, Outside) e] | _ -> []) specs in
        symdiff_proc := (x, f_vars);
        (match pk with Implementation -> () | Procedure _ -> symdiff_write_fun false false pres posts);
        symdiff_proc := (x2, f_vars);
        (match pk with
          | Implementation -> ()
          | Procedure _ ->
              let req_strings = List.collect (fun s ->
                match s with (_, Requires (r, e)) -> [" && " + (string_of_exp_ignore_rel r e)] | _ -> []) specs in
              state.PrintLine ("procedure #symdiff_proc_reqs##" + x2 + "(" + (string_of_pformals_var fs) + ");");
              state.PrintLine ("  ensures true " + (String.concat "" req_strings) + ";");
              symdiff_write_fun false true pres posts)
      );
      let f x pk p_fs p_rs b_opt =
        let rets = match p_rs with [] -> "" | _ -> "returns(" + (string_of_pformals_var p_rs) + ")" in
        let semi = match pk with Procedure _ -> ";" | Implementation -> "" in 
        state.PrintLine ((string_of_proc_kind pk) + " " + x + "(" + (string_of_pformals_param p_fs) + ")" + rets + semi);
        state.Indent ();
        List.iter (emit_spec state) (match pk with Procedure _ -> specs | Implementation -> []);
        state.Unindent ();
        (match b_opt with
        | None -> ()
        | Some (vars, b) ->
          (
            state.PrintLine "{";
            state.Indent ();
            List.iter (fun (x, t, l) ->
              state.PrintLine ("var " + (string_of_lin_var l) + x + ":" + (string_of_typ t) + ";")) vars;
            List.iter (emit_stmt_decl [] state) b;
            (if !symdiff then
              state.PrintLine ("call #symdiff_proc_reqs##" + x2 + "(" + (String.concat "," (List.map (fun (x, _, _) -> x) p_fs)) + ");");
              List.iter (fun (x, _, _) -> state.PrintLine(x + " := " + x + ";")) symdiff_mods; // make sure symdiff reports modified variables in predictable order (TODO: get /doModSetAnalysis completely turned off)
              () // symdiff_emit_linearity state
            );
            List.iter (emit_stmt rec_context state) b;
            state.Unindent ();
            state.PrintLine "}"
          )) in
      ( match (b_opt, pk) with
        | (None, Procedure _) ->
            f x pk fs rs None;
            f x2 pk fs rs None
        | (None, Implementation) -> err "implementation must have body"
        | (Some _, Procedure _) ->
            f x pk fs rs None;
            f x2 pk fs rs None;
            f x2 Implementation impl_fs impl_rs b_opt
        | (Some _, Implementation) ->
            f x2 Implementation impl_fs impl_rs b_opt);
      state.PrintLine ""
    )

let emit_module (state:print_state) (m:_module):unit =
  try
    List.iter (emit_decl state) m.mDecls
  with Err s -> let (f, l) = !state.cur_loc in err ("error near location " + f + " line " + (string l) + ": " + s);
  if !symdiff then
    // generate clone procedure declarations
    List.iter (fun (p, count) ->
        let (_, pk, ik, fs, rs, specs, ts) = List.assoc p state.all_procs in
        for i = 1 to !count do
          let pc = "#clone" + (string i) + "#" + p in
          let d = DProc (pc, pk, ik, fs, rs, specs, ts) in
          emit_decl state (("clone", 0), d)
        )
      !symdiff_proc_global_clones

let emit_entry_point (state:print_state):unit =
  // call all interface procedures from a dummy entry point
  let vars = List.collect (fun (_, d) -> match d with DStaticGhost (x, _, _, _) -> [x] | _ -> []) state.publics in
  let mods = "modifies " + (String.concat "," vars) + ";" in
  state.PrintLine "procedure{:yields} ###DummyCallTarget();";
  let procs =
    List.fold_left
      (fun procs (loc, d) ->
        match d with
        | DProc (xp, Procedure (_, atomicity), ik, fs, rs, specs, _) ->
          (
            state.SetLoc(loc);
            let fs = ("me", TInt, Lin (LinConst, LinOur))::("RET", TName "ReturnTo", Non)::fs in
            let attr = match atomicity with Atomic -> "" | _ -> "{:verify false}" in
            state.PrintLine ("procedure{:yields}" + attr + " ###Dummy#" + xp + "()");
            state.Indent ();
            state.PrintLine mods;
            state.Unindent ();
            state.PrintLine "{";
            state.Indent ();
            List.iter
              (fun (x, t, lin) ->
                state.PrintLine ("var" + (string_of_lin_var lin) + " " + x + ":" + (string_of_typ t) + ";"))
              (fs @ rs);
            state.SetLoc(loc);
            List.iter
              (fun (_, s) ->
                match (atomicity, s) with
                | (Atomic, Requires (r, e)) -> state.PrintLine ("assume " + (string_of_exp_ignore_rel r e) + ";")
                | _ -> ())
              specs;
            let stable = match atomicity with Stable -> "###DummyEntryPoint() | " | _ -> "" in
            let args = String.concat "," (List.map (fun (x, _, _) -> x) fs) in
            let rets = String.concat "," (List.map (fun (x, _, _) -> x) rs) in
            let rets = rets + (if List.length rs = 0 then "" else " := ") in
            state.SetLoc(loc);
            state.PrintLine ("free call " + stable + rets + "##verify##" + xp + "(" + args + ");");
            state.Unindent ();
            state.PrintLine "}";
            (xp, atomicity)::procs
          )
        | _ -> procs)
      []
      state.publics
  if procs.Length > 0 then
    state.SetLoc(("fake entry point", 1));
    state.PrintLine "procedure{:entrypoint}{:verify false} ###DummyEntryPoint()";
    state.PrintLine mods;
    state.PrintLine "{";
    state.Indent ();
    state.PrintLine ("###loop: goto " + (String.concat "," (List.map fst procs)) + ";");
    List.iter
      (fun (xp, atomicity) -> state.PrintLine (xp + ": async call ###Dummy#" + xp + "(); goto ###loop;"))
      (List.rev procs);
    state.Unindent ();
    state.PrintLine "}"

