open Ast
open Parse
open Parse_util
open Microsoft.FSharp.Compatibility.OCaml.Big_int;;

exception LocErr of loc * exn

let print_and_exit = ref false
let print_nonghost_and_exit = ref false

let Map_containsKey (x:'a) (m:Map<'a,'b>) = match m.TryFind x with None -> false | Some _ -> true
let Map_ofList (l:('k * 'a) list):Map<'k,'a> = List.fold (fun m (k, a) -> Map.add k a m) Map.empty l
let Map_toList (m:Map<'k,'a>):('k * 'a) list = Map.fold (fun k a l -> (k, a)::l) m []
let Map_cardinal (m:Map<'k,'a>):int = List.length (Map_toList m)
let Set_ofList (l:'a list):Set<'a> = List.fold (fun s a -> Set.add a s) Set.empty l
let Set_toList (s:Set<'a>):'a list = Set.fold (fun l a -> a::l) [] s
let Set_difference (s1:Set<'a>) (s2:Set<'a>) = Set.fold (fun s a -> Set.remove a s) s1 s2

exception InternalError of string

let multi_add (k:'k) (a:'a) (m:Map<'k,'a list>) =
  match m.TryFind(k) with
  | None -> m.Add(k, [a])
  | Some l -> m.Add(k, a::l)

type env =
  {
    global_decls:Map<id,btyp>;
    global_static_decls:Map<id,id>;
    const_decls:Map<id,btyp * bexp option>;
    type_decls:Map<id,(id list * (linearity * id * bpformal list) list) option>;
    fun_decls:Map<id,loc * fun_decl>;
    proc_decls:Map<id,loc * proc_decl>;
  }

let build_env decls:env =
  List.fold_left
    (fun env (l, decl) ->
      match decl with
      | BGlobalDecl (x, t, _, _) -> {env with global_decls = env.global_decls.Add(x, t)}
      | BGlobalStaticDecl (x, mem) -> {env with global_static_decls = env.global_static_decls.Add(x, mem)}
      | BConstDecl (x, t, e) -> {env with const_decls = env.const_decls.Add(x, (t, e))}
      | BTypeDecl (x, t) -> {env with type_decls = env.type_decls.Add(x, t)}
      | BFunDecl ((x, _, _, _, _, _) as d) -> {env with fun_decls = env.fun_decls.Add(x, (l, d))}
      | BProcDecl ((x, _, _, _, _, _) as d) when not (Map_containsKey x env.proc_decls) ->
          {env with proc_decls = env.proc_decls.Add(x, (l, d))}
      | BProcDecl ((x, _, _, _, _, _) as d) -> env
      | _ -> env)
    {global_decls = Map.empty;
     global_static_decls = Map.empty;
     const_decls = Map.empty;
     type_decls = Map.empty;
     fun_decls = Map.empty;
     proc_decls = Map.empty;
     }
    decls

let extra_proc_invariants = ref (Map.empty:Map<id, (loc * bexp) list>)
let extra_proc_modifies = ref (Map.empty:Map<id, id list>)

let find_constructor (env:env) (xt:id) (xc:id):(linearity * bpformal list) =
  match Map.tryFind xt env.type_decls with
  | None -> err ("cannot find declaration of type " + xt)
  | Some None -> err ("cannot find case " + xc + " in type " + xt)
  | Some (Some (_, cases)) ->
    (
      let cases = List.map (fun (lin, x, fs) -> (x, (lin, fs))) cases in
      if not (List.mem_assoc xc cases) then err ("cannot find case " + xc + " in type " + xt) else
      List.assoc xc cases
    )

let static_addr (x:id):id = "?ADDR__" + x

(*****************************************************************************)

let rec map_exp (f:bexp -> bexp option) (e:bexp):bexp =
  match (f e) with
  | Some e -> e
  | None ->
    (
      let r = map_exp f in
      match e with
      | BLoc (l, e) -> BLoc (l, r e)
      | BVar x -> BVar x
      | BIntConst _ -> e
      | BRealConst _ -> e
      | BBv32 _ -> e
      | BBoolConst _ -> e
      | BUop (op, e) -> BUop (op, r e)
      | BBop (op, e1, e2) -> BBop (op, r e1, r e2)
      | BQuant (q, fs, ts, e) -> BQuant (q, fs, List.map (List.map r) ts, r e)
      | BSubscript (e, es) -> BSubscript (r e, List.map r es)
      | BUpdate (e, es, ee) -> BUpdate (r e, List.map r es, r ee)
      | BApply (x, es) -> BApply (x, List.map r es)
      | BCond (e1, e2, e3) -> BCond (r e1, r e2, r e3)
    )

let rec map_stmt (fe:bexp -> bexp) (fs:bstmt -> bstmt option) (l:loc, s:bstmt):(loc * bstmt) =
  match fs s with
  | Some s -> (l, s)
  | None ->
    (
      match s with
      | BLocalDecl (x, t, lin, None) -> (l, s)
      | BLocalDecl (x, t, lin, Some e) -> (l, BLocalDecl (x, t, lin, Some (fe e)))
      | BLabel x -> (l, s)
      | BGoto x -> (l, s)
      | BAssign (x, e) -> (l, BAssign (x, fe e))
      | BGroup b -> (l, BGroup (map_block fe fs b))
      | BIf (e, b1, None) -> (l, BIf (fe e, map_block fe fs b1, None))
      | BIf (e, b1, Some b2) -> (l, BIf (fe e, map_block fe fs b1, Some (map_block fe fs b2)))
      | BWhile (e, invs, b) ->
          (l, BWhile (
            fe e,
            List.map (fun (l, e) -> (l, fe e)) invs,
            map_block fe fs b))
      | BForallGhost (xs, ts, e, b) ->
          (l, BForallGhost (xs, List.map (List.map fe) ts, fe e, map_block fe fs b))
      | BAssume e -> (l, BAssume (fe e))
      | BAssert (e, inv) -> (l, BAssert (fe e, inv))
      | BSplit -> (l, BSplit)
      | BYield e -> (l, BYield (fe e))
      | BHavoc e -> (l, BHavoc (fe e))
      | BCall (xs, f, es, pars) ->
          (l, BCall (xs, f, List.map (fe) es, List.map (fun (x, es) -> (x, List.map fe es)) pars))
      | BReturn _ -> (l, s)
    )
and map_block (fe:bexp -> bexp) (fs:bstmt -> bstmt option) (b:bblock):bblock = List.map (map_stmt fe fs) b

let map_spec (fe:bexp -> bexp) (l:loc, s:bspec):(loc * bspec) =
  match s with
  | BRequires e -> (l, BRequires (fe e))
  | BEnsures e -> (l, BEnsures (fe e))
  | BModifies es -> (l, BModifies (List.map fe es))
  | BInOut _ -> (l, s)

// TODO: make more robust?
let rename_formal_funs (fs:bformal_fun list) (m:Map<id,bexp>):(bformal_fun list * Map<id,bexp>) =
  let m = List.fold (fun m (x, _, _) -> Map.add x (BVar (x + "__BEAT")) m) m fs in
  let fs = List.map (fun (x, t, e) -> (x + "__BEAT", t, e)) fs in
  (fs, m)

let rename_formals (fs:bformal list) (m:Map<id,bexp>):(bformal list * Map<id,bexp>) =
  let (fs, m) = rename_formal_funs (List.map (fun (x, t) -> (x, t, None)) fs) m in
  (List.map (fun (x, t, _) -> (x, t)) fs, m)

let subst_id (m:Map<id,bexp>) (x:id):id =
  if (m.ContainsKey(x)) then
    match m.[x] with
    | BVar y -> y
    | _ -> err ("internal substitution error: " + x)
  else x

let rec subst_exp (m:Map<id,bexp>) (e:bexp):bexp =
  map_exp
    (fun e ->
      match e with
      | BVar x when m.ContainsKey(x) -> Some (m.[x])
      | BQuant (q, fs, ts, e) ->
          let (fs, m) = rename_formals fs m in
          Some (BQuant (q, fs, List.map (List.map (subst_exp m)) ts, subst_exp m e))
      | _ -> None)
    e

let rec subst_stmt (m:Map<id,bexp>) (l:loc, s:bstmt):(loc * bstmt) =
  map_stmt
    (subst_exp m)
    (fun s ->
      match s with
      | BAssign (x, e) ->
          Some (BAssign (subst_exp m x, subst_exp m e))
      | BCall (xs, f, es, pars) ->
          Some
            (BCall (List.map (subst_exp m) xs, f, List.map (subst_exp m) es,
              List.map (fun (x, es) -> (x, List.map (subst_exp m) es)) pars))
      | _ -> None)
    (l, s)

let subst_block (m:Map<id,bexp>) (b:bblock):bblock = List.map (subst_stmt m) b

let subst_spec (m:Map<id,bexp>) (l:loc, s:bspec):(loc * bspec) =
  map_spec (subst_exp m) (l, s)

(*****************************************************************************)

let regs_id = "r"
let regs_arr = BUop (BField ("regs", None), BVar regs_id)
let reg_efl = BUop (BField ("efl", None), BVar regs_id)
let all_regs = ["eax"; "ebx"; "ecx"; "edx"; "esi"; "edi"; "esp"; "ebp"]
let id_is_reg (x:id) =
  match x with "eax" | "ebx" | "ecx" | "edx" | "esi" | "edi" | "ebp" | "esp" -> true | _ -> false

type procKind = PIns | PInline | PProc

let proc_kind (x:id):procKind =
  let rec f i =
    match x.[i] with
    | '_' -> f (i + 1)
    | c when System.Char.IsLower(c) -> PInline
    | c when System.Char.IsUpper(c) -> PProc
    | _ -> err ("bad procedure name: " + x) in
  if x.StartsWith("instr_") then PIns else f 0

(*
let get_op f =
  match f with
  | "Add" | "AddChecked" -> BAdd
  | "Sub" | "SubChecked" -> BSub
  | _ -> err ("unsupported memory operation: " + f) in
*)

let expand_deep_conjuncts = ref true;

let rec list_of_conjuncts (env:env) (depth:int) ((fBase, lBase):loc) ((f, l):loc) (e:bexp):(loc * bexp) list =
  let lb = if lBase = l && fBase.EndsWith(f) then (fBase, lBase) else (fBase + "(" + (string lBase) + ") --> " + f, l) in
  match e with
  | (BApply ("&&&", [ee])) -> list_of_conjuncts env (depth + 1) (fBase, lBase) (f, l) ee
  | _ ->
    (
      if depth = 0 then [(lb, e)] else
      let f0 = list_of_conjuncts env (depth - 0) lb in
      let f1 = list_of_conjuncts env (depth - 1) lb in
      match e with
        | BLoc (lAnd, BBop (BAnd, e1, e2)) ->
            (f0 lb e1) @ (f1 lAnd e2)
        | BApply (x, es) when env.fun_decls.ContainsKey(x) ->
          (
            let (lf, (_, fs, _, ee, _, _)) = env.fun_decls.[x] in
            match ee with
            | None -> [(lb, e)]
            | Some ee ->
                let m = List.map2 (fun (x, _, _) e -> (x, e)) fs es in
                let s = new Map<id,bexp>(m)
                f0 lf (subst_exp s ee)
          )
        | BBop (BImply, e1, e2) when !expand_deep_conjuncts ->
            List.map (fun (l, e) -> (l, BBop (BImply, e1, e))) (f0 lb e2)
        | BCond (e1, e2, e3) when !expand_deep_conjuncts ->
            f0 lb (BLoc (lb, BBop (BAnd, BBop(BImply, e1, e2), BBop(BImply, BUop(BNot, e1), e3))))
        | BQuant (q, fs, ts, e) when !expand_deep_conjuncts ->
            List.map (fun (l, e) -> (l, BQuant (q, fs, ts, e))) (f0 lb e)
        | _ -> [(lb, e)]
    )

let rec expand_conjuncts_stmt (env:env) (depth:int) (l:loc, s:bstmt):(loc * bstmt) list =
  let f = expand_conjuncts_block env depth in
  match s with
  | BIf (e, b1, b2) -> [(l, BIf (e, f b1, match b2 with None -> None | Some b2 -> Some (f b2)))]
  | BWhile (e, invs, b) ->
      let invs = List.flatten (List.map (fun (l, e) -> list_of_conjuncts env depth l l e) invs) in
      [(l, BWhile (e, invs, f b))]
  | BAssert (e, inv) -> List.map (fun (l, e) -> (l, BAssert (e, inv))) (list_of_conjuncts env depth l l e)
  | _ -> [(l, s)]
and expand_conjuncts_block (env:env) (depth:int) (b:bblock):bblock =
  List.flatten (List.map (expand_conjuncts_stmt env depth) b)

let expand_conjuncts_spec (env:env) (depth:int) (l:loc, s:bspec):(loc * bspec) list =
  match s with
  | BRequires e -> List.map (fun (l, e) -> (l, BRequires e)) (list_of_conjuncts env depth l l e)
  | BEnsures e -> List.map (fun (l, e) -> (l, BEnsures e)) (list_of_conjuncts env depth l l e)
  | _ -> [(l, s)]

let expand_conjuncts_decl (env:env) (depth:int) (l:loc, d:bdecl):(loc * bdecl) =
  match d with
  | BProcDecl (x, ps, rets, specs, b, p) ->
      (l, BProcDecl (x, ps, rets,
        List.flatten (List.map (expand_conjuncts_spec env depth) specs),
        (match b with None -> None | Some b -> Some (expand_conjuncts_block env depth b)),
        p))
  | _-> (l, d)

let expand_conjuncts_decls (env:env) (depth:int) = List.map (expand_conjuncts_decl env depth)


(*
let expand_apply_decl (env:env) (l:loc, d:bdecl):(loc * bdecl) =
  let rec fe e =
    match e with
    | BApply (x, es) when x.StartsWith("&") && x.Length > 1 ->
      (
        match Map.tryFind (x.Substring(1)) env.fun_decls with
        | Some (_, (_, fs, _, Some ef, _, _)) ->
            let m = List.map2 (fun (xf, _, _) ea -> (xf, ea)) fs es in
            Some (BApply ("&", [map_exp fe (subst_exp (Map_ofList m) ef)]))
        | _ -> err ("could not find definition for function instantiation " + x)
      )
    | _ -> None
    in
  match d with
  | BProcDecl (x, ps, rets, specs, b, p) ->
      (l, BProcDecl (x, ps, rets,
        (List.map (map_spec (map_exp fe)) specs),
        (match b with None -> None | Some b -> Some (map_block (map_exp fe) (fun s -> None) b)),
        p))
  | _-> (l, d)

let expand_apply_decls (env:env) = List.map (expand_apply_decl env)
*)

(*****************************************************************************)

let rec sep_list (sep:string) (l:string list) =
  match l with
  | [] -> ""
  | [x] -> x
  | h::t -> h + sep + (sep_list sep t)

let rec string_of_btyp t =
  match t with
  | BInt -> "int"
  | BBool -> "bool"
  | BReal -> "real"
  | BArray (ts, t) -> "[" + (sep_list "," (List.map string_of_btyp ts)) + "]" + (string_of_btyp t)
  | BNamedType x -> x

let string_of_buop op =
  match op with
  | BNot -> "!"
  | BNeg -> "-"
  | BOld -> "old"
  | _ -> "<<<internal error: uop>>>"

let string_of_bbop op =
  match op with
  | BEquiv -> "<==>"
  | BImply -> "==>"
  | BAnd -> "&&"
  | BOr -> "||"
  | BEq -> "=="
  | BNe -> "!="
  | BLt -> "<"
  | BGt -> ">"
  | BLe -> "<="
  | BGe -> ">="
  | BAdd -> "+"
  | BSub -> "-"
  | BMul -> "*"
  | BDiv -> " div "
  | BMod -> " mod "
  | BRealDiv -> " / "
  | BAddChecked -> "$+"
  | BSubChecked -> "$-"
  | _ -> "<<<internal error: bop>>>"

let string_of_bquant q =
  match q with
  | BForall -> "forall"
  | BExists -> "exists"
  | BLambda -> "lambda"

let string_of_linearity (l:linearity) =
  match l with
  | Lin (LinVar, LinOur) -> "linear "
  | Lin (LinVar, LinMy) -> "my "
  | Lin (LinConst, LinOur) -> "const linear "
  | Lin (LinConst, LinMy) -> "const my "
  | Lin (LinInOut, LinOur) -> "inout linear "
  | Lin (LinInOut, LinMy) -> "inout my "
  | Non -> ""

let string_of_bformal (x, t) = x + ":" + (string_of_btyp t)
let string_of_bpformal (x, t, lin) = (string_of_linearity lin) + x + ":" + (string_of_btyp t)
let string_of_bformal_fun (x, t, _) = x + ":" + (string_of_btyp t)

let string_of_bformal_var (x, t) =
  match t with
  | BFormalType t -> x + ":" + (string_of_btyp t)
  | BFormalAlias t -> ("<<<unexpected alias " + x + ">>>")

let string_of_bpformal_var (x, t, lin) = (string_of_linearity lin) + (string_of_bformal_var (x, t))

let prec_of_uop op = match op with | BNot -> 50 | BNeg -> 50 | BOld -> 99 | _ -> 99
let prec_of_bop op =
  match op with
  | BEquiv -> 10 | BImply -> 10
  | BAnd -> 15 | BOr -> 15
  | BEq -> 20 | BNe -> 20 | BLt -> 20 | BGt -> 20 | BLe -> 20 | BGe -> 20
  | BAdd -> 30 | BSub -> 30 | BAddChecked -> 30 | BSubChecked -> 30
  | BMul -> 35 | BDiv -> 35 | BMod -> 35 | BRealDiv -> 35
  | _ -> 99

let can_eval_op op =
  match op with
    | BAdd
    | BSub
    | BMul
    | BDiv -> true
    | _ -> false

//-evaluates integers only
let eval_op op (i1:bigint) (i2:bigint) =
  match op with
    | BAdd -> i1 + i2
    | BSub -> i1 - i2
    | BMul -> i1 * i2
    | BDiv -> i1 / i2
    | _ -> raise (InternalError("eval_op does not expect this operator"))

//-evaluates integer constants only    
let rec eval_constants_in_bexp e =
  match e with
    | BBop (op, e1, e2) when (can_eval_op op) ->
      let e1' = eval_constants_in_bexp e1 in
      let e2' = eval_constants_in_bexp e2 in
      (match e1', e2' with
       //do not reduce 0-1 etc
       | (BIntConst i1), (BIntConst i2) when not (i1 = 0I && op = BSub) -> BIntConst (eval_op op i1 i2)
       | _ -> BBop(op, e1', e2')
       )
    | _ -> e

let rec multiline_string_of_bexp (multiline:bool) (prec:int) (e:bexp):string =
  let string_of_bexp = multiline_string_of_bexp multiline in
  let e' = eval_constants_in_bexp e in
  let loc_string (f, i) = "/*LOC*//*LOC:" + f + "," + (string i) + "*/" in
  let bbop s op e1 e2 =
    let ep = prec_of_bop op in
    let (epLeft, epRight) =
      match op with
      | BAdd | BSub | BMul | BDiv | BMod | BRealDiv | BAddChecked | BSubChecked -> (ep, ep + 1)
      | _ -> (ep + 1, ep + 1)
    ((string_of_bexp epLeft e1) + s + (string_of_bbop op) + (string_of_bexp epRight e2), ep)
  let (s, ePrec) =
    match e' with
    | BVar x -> (x, 99)
    | BIntConst i -> (string i, 99)
    | BRealConst r -> (r, 99)
    | BBv32 i -> ((string i) + "bv32", 99)
    | BBoolConst true -> ("true", 99)
    | BBoolConst false -> ("false", 99)
    | BUop (BField (x, Some (_, xc, BFieldNative)), e) -> (x + "#" + xc + "(" + (string_of_bexp 5 e) + ")", 99)
    | BUop (BField (x, Some (_, xc, BFieldFun)), e) -> (xc + "__" + x + "(" + (string_of_bexp 5 e) + ")", 99)
    | BUop (BField (x, _), e) -> ("(" + (string_of_bexp 5 e) + "." + x + ")", 99)
    | BUop (BNeg, e) -> ("(-" + (string_of_bexp ((prec_of_uop BNot) + 1) e) + ")", 99)
    | BUop (BIs x, e) -> ("(" + (string_of_bexp 5 e) + " is " + x + ")", 99)
    | BUop (op, e) -> let ep = prec_of_uop op in ((string_of_buop op) + (string_of_bexp (ep + 1) e), ep)
    | BBop (BFieldUpdate (xf, Some xc), e1, e2) ->
        (xc + "_update__" + xf + "(" + (string_of_bexp 5 e1) + "," + (string_of_bexp 5 e2) + ")", 99)
    | BBop (BFieldUpdate (xf, None), e1, e2) -> ("<<<internal error: unresolved field update: " + (string_of_bexp 99 e1) + "." + xf + ">>>", 99)
    | BLoc (l, (BBop (op, e1, e2))) when multiline -> bbop (loc_string l) op e1 e2
    | BBop (op, e1, e2) -> bbop "" op e1 e2
    | BQuant (q, fs, ts, e) ->
      (   (string_of_bquant q) + " "
        + (sep_list "," (List.map string_of_bformal fs))
        + "::"
        + (sep_list "" (List.map (fun t -> "{"+ (sep_list "," (List.map (string_of_bexp 5) t)) + "}") ts))
        + (string_of_bexp 6 e),
          (-5)
      )
    | BSubscript (e, es) -> ((string_of_bexp 90 e) + "[" + (sep_list "," (List.map (string_of_bexp 5) es)) + "]", 40)
    | BUpdate (e, es, ee) -> ((string_of_bexp 90 e) + "[" + (sep_list "," (List.map (string_of_bexp 90) es)) + ":=" + (string_of_bexp 90 ee) + "]", 40)
    | BApply ("&&&", [ee]) -> (string_of_bexp prec ee, prec)
    | BApply ("static", [emem; BApply (x, _)]) ->
        (string_of_bexp prec (BSubscript (BUop (BField ("map", Some ("mem", "mem", BFieldNative)), emem), [BVar (static_addr x)])), prec)
    | BApply (x, es) -> (x + "(" + (sep_list "," (List.map (string_of_bexp 5) es)) + ")", 90)
    | BCond (e1, e2, e3) -> ("if " + (string_of_bexp 90 e1) + " then " + (string_of_bexp 90 e2) + " else " + (string_of_bexp 90 e3), 0)
    | BLoc (l, e) when multiline -> (loc_string l + (string_of_bexp prec e), 0)
    | BLoc ((f, i), e) -> (string_of_bexp prec e, 0)
  in if prec <= ePrec then s else "(" + s + ")"

type print_state =
  {
    print_out:System.IO.TextWriter;
    indent:string;
    cur_loc:loc ref;
  }
  member this.PrintLine (s:string) =
    if s.Trim() = "" && (!print_and_exit || !print_nonghost_and_exit) then () else
    let ss = s.Split ([|"/*LOC*/"|], System.StringSplitOptions.None) in
    this.print_out.Write (this.indent)
    let newline () =
      let (f, i) = !this.cur_loc in (this.cur_loc := (f, i + 1));
      this.print_out.WriteLine () in
    for s in ss do
      (
        if s.StartsWith("/*LOC:") then
          let i1 = "/*LOC:".Length in
          let i2 = s.IndexOf(",") in
          let i3 = i2 + (",".Length) in
          let i4 = s.IndexOf("*/") in
          let i5 = i4 + ("*/".Length) in
          let f = s.Substring(i1, i2 - i1) in
          let i = System.Int32.Parse(s.Substring(i3, i4 - i3)) in
          let rest = s.Substring(i5) in
          let (cf, ci) = !this.cur_loc in
          if f = cf && i <= ci then
            this.print_out.Write (rest)
          else
            newline ();
            this.SetLoc (f, i);
            this.print_out.Write ("  " + rest)
        else
          this.print_out.Write (s)
      );
    newline ()
  member this.SetLoc (((f, i) as l):loc) =
    if (!print_and_exit || !print_nonghost_and_exit) then this.cur_loc := l else
    let (cf, ci) as cl = !this.cur_loc in
    if l = cl then ()
    else if f <> cf || i < ci || i > ci + 8 then this.cur_loc := l; this.print_out.WriteLine ("#line " + (string i) + " " + f)
    else this.PrintLine ""; this.SetLoc l

let rec print_bstmt (state:print_state) (l:loc, s) =
  let () = state.SetLoc l in
  let p:(string -> unit) = state.PrintLine in
  let string_of_bexp = multiline_string_of_bexp true
  let fcall x es = x + "(" + (sep_list "," (List.map (string_of_bexp 5) es)) + ")" in
  let fpars pars = String.concat "" (List.map (fun (x, es) -> " | " + fcall x es) pars) in
  match s with
  | BLocalDecl (x, t, lin, None) -> p ((string_of_linearity lin) + "var " + (string_of_bformal_var (x, t)) + ";")
  | BLocalDecl (x, t, lin, Some e) -> p ((string_of_linearity lin) + "var " + (string_of_bformal_var (x, t)) + "=" + (string_of_bexp 0 e) + ";")
  | BLabel x -> p (x + ":")
  | BGoto x -> p ("goto " + x + ";")
  | BAssign (x, e) -> p ((string_of_bexp (-5) x) + ":=" + (string_of_bexp 0 e) + ";")
  | BGroup b -> print_bblock_s state "{:" ":}" b
  | BIf (e, b1, b2) ->
    (
      p ("if(" + (string_of_bexp 0 e) + ")");
      print_bblock state b1;
      (match b2 with None -> () | Some b -> print_bblock state b)
    )
  | BWhile (e, invs, b) ->
    (
      p ("while(" + (string_of_bexp 0 e) + ")");
      List.iter (fun (l:loc, e) -> state.SetLoc l; p ("invariant " + (string_of_bexp 0 e))) invs;
      print_bblock state b
    )
  | BForallGhost (fs, ts, e, b) ->
    (
      p ("forall " + (sep_list "," (List.map string_of_bformal fs)) + "::"
          + (sep_list "" (List.map (fun t -> "{" + (sep_list "," (List.map (string_of_bexp 5) t)) + "}") ts))
          + (string_of_bexp 6 e));
      print_bblock state b
    )
  | BAssume e -> p ("assume " + (string_of_bexp 0 e) + ";")
  | BAssert (e, inv) -> p ((if inv then "invariant " else "assert ") + (string_of_bexp 0 e) + ";")
  | BSplit -> p ("assert {:split_here} true;")
  | BYield e -> p ("yield " + (string_of_bexp 0 e) + ";")
  | BHavoc e -> p ("havoc " + (string_of_bexp (-5) e) + ";")
  | BCall (xs, f, es, []) when f.StartsWith("construct##") ->
      let f = f.Substring("construct##".Length) in
      p ("let " + (sep_list "," (List.map (string_of_bexp (-5)) xs)) + ":=" + (fcall f es) + ";")
  | BCall (es, f, xs, []) when f.StartsWith("destruct##") ->
      let f = f.Substring("destruct##".Length) in
      p ("let " + (fcall f es) + ":=" + (sep_list "," (List.map (string_of_bexp (-5)) xs)) + ";")
  | BCall ([], f, es, pars) -> p ("call " + (fcall f es) + (fpars pars) + ";")
  | BCall (xs, f, es, pars) -> p ("call " + (sep_list "," (List.map (string_of_bexp (-5)) xs)) + ":=" + (fcall f es) + (fpars pars) + ";")
  | BReturn BRet -> p "return;"
  | BReturn BIRet -> p "ireturn;"
  | BReturn BEmbellishRet -> p "Return;"
and print_bblock (state:print_state) b = print_bblock_s state "{" "}" b
and print_bblock_s (state:print_state) sl sr b =
  state.PrintLine sl;
  List.iter (print_bstmt {state with indent = "  " + state.indent}) b;
  state.PrintLine sr

let print_bspec (state:print_state) (l:loc, s) =
  let () = state.SetLoc l in
  let p:(string -> unit) = state.PrintLine in
  let string_of_bexp = multiline_string_of_bexp true
  match s with
  | BRequires e -> p ("requires " + (string_of_bexp 0 e) + ";")
  | BEnsures e -> p ("ensures " + (string_of_bexp 0 e) + ";")
  | BModifies [] | BInOut [] -> ()
  | BModifies es -> p ("modifies " + (sep_list "," (List.map (string_of_bexp (-99) ) es)) + ";")
  | BInOut fs -> p ("inout " + (sep_list "," (List.map string_of_bpformal fs)) + ";")

let string_of_procimpl p =
  let gs g = match g with PReal -> "" | PGhost -> "ghost " in
  match p with
  | Procedure (g, Yields) -> (gs g) + "procedure"
  | Procedure (g, Atomic) -> "atomic " + (gs g) + "procedure"
  | Procedure (g, Stable) -> "stable " + (gs g) + "procedure"
  | Implementation -> "implementation"
  | Instruction -> "instruction"

let string_of_readwrite rw = match rw with Readonly -> "readonly " | ReadWrite -> ""

let print_bdecl (state:print_state) (l:loc, decl) =
  let () = state.SetLoc l in
  let p:(string -> unit) = state.PrintLine in
  let string_of_bexp = multiline_string_of_bexp true
  match decl with
  | BGlobalDecl (x, t, l, rw) -> p ((string_of_readwrite rw) + (string_of_linearity l) + "var " + x + ":" + (string_of_btyp t) + ";")
  | BGlobalStaticDecl (x, mem) -> p ("var " + x + " @ " + mem + ";")
  | BConstDecl (x, t, e_opt) ->
      let init = (match e_opt with None -> "" | Some e -> " := " + (string_of_bexp 0 e)) in
      p ("const " + x + ":" + (string_of_btyp t) + init + ";")
  | BStaticDecl x -> p ("static " + x + ";")
  | BAxiomDecl e -> p ("axiom " + (string_of_bexp 0 e) + ";")
  | BTypeDecl (x, None) -> p ("type " + x + ";")
  | BTypeDecl (x, Some (_, cs)) ->
      p ("type{:overload} " + x + " = "
        + (String.concat " | " (List.map (fun (lin, x, fs) -> (string_of_linearity lin) + x + "(" + (String.concat "," (List.map string_of_bpformal fs)) + ")") cs)) + ";")
  | BFunDecl (x, ps, t, e, a, ts_opt) ->
    (
      let attr = match a with None -> "" | Some s -> "{" + s + "}" in
      let impl =
        match ts_opt with
        | None -> ""
        | Some ts ->
            " implementation" + (sep_list "" (List.map (fun t ->
              "{"+ (sep_list "," (List.map (string_of_bexp 5) t)) + "}") ts)) in
      let r = ":" + (string_of_btyp t) + (match e with None -> ";" | _ -> "") in
      p ("function" + attr + impl + " " + x + "(" + (sep_list "," (List.map string_of_bformal_fun ps)) + ")" + r);
      (match e with
          None -> ()
        | Some e ->
          (
            p ("{");
            p ("  " + (string_of_bexp 0 e));
            p ("}")
          )
      )
    )
  | BProcDecl (x, ps, rets, specs, b, pi) ->
    (
      let r = (match rets with _::_ -> ("returns(" + (sep_list "," (List.map string_of_bpformal rets)) + ")") | _ -> "") in
      let semi = (match b with None -> ";" | _ -> "") in
      p ((string_of_procimpl pi) + " " + x + "(" + (sep_list "," (List.map string_of_bpformal_var ps)) + ")" + r + semi)
      List.iter (print_bspec state) specs;
      (match b with None -> () | Some b -> print_bblock state b)
    )

let print_module (state:print_state) (m:_module):unit =
  state.PrintLine ("module " + (if m.mIsImpl then "implementation" else "interface") + " " + m.mName);
  (if List.length m.mImports > 0 then state.PrintLine ("  import " + (String.concat ", " (m.mImports)) + ";"));
  (if List.length m.mModifies > 0 then state.PrintLine ("  modifies " + (String.concat ", " (m.mModifies)) + ";"));
  (if List.length m.mYields > 0 then state.PrintLine ("  yield " + (String.concat ", " (m.mYields)) + ";"));
  //state.PrintLine "{"; // HACK: omit braces to enable file concatenation
  List.iter (print_bdecl state) m.mDecls;
  //state.PrintLine "}"

let string_of_bexp = multiline_string_of_bexp false

(*****************************************************************************)

let expand_opaque_decl (l:loc, d:bdecl):(loc * bdecl) list =
  try
  (
    match d with
    | BFunDecl (x, ps, t, Some e, Some a, None) when a = ":opaque" ->
        // function{:opaque} f(x:tx):tr { e }
        //  ==>
        // function T___BEAT_f(x:tx):bool { true }
        // function f(x:tx):tr;
        // function implementation{T___BEAT_f(x)} f(x:tx):tr { e }
        // atomic ghost procedure reveal_f() ensures (forall x:tx::{f(x)} f(x) == e);
        // { forall x:t::{f(x)} f(x) == e {assert T___BEAT_f(x);} }
        let xtrig = "T___BEAT_" + x in
        let args = List.map (fun (xf, _, _) -> BVar xf) ps in
        let ps_bformal = List.map (fun (xf, tf, _) -> (xf, tf)) ps in
        let ftrig = BFunDecl (xtrig, ps, BBool, Some (BBoolConst true), None, None) in
        let fdecl = BFunDecl (x, ps, t, None, None, None) in
        let fimpl = BFunDecl (x, ps, t, Some e, None, Some [[BApply (xtrig, args)]]) in
        let fapp = BApply (x, args) in
        let eq = BBop (BEq, fapp, e) in
        let ens = BEnsures (BQuant (BForall, ps_bformal, [[fapp]], eq)) in
        let s_assert = BAssert (BApply (xtrig, args), false) in
        let s_forall = BForallGhost (ps_bformal, [[fapp]], eq, [(l, s_assert)]) in
        let pk = Procedure (PGhost, Atomic) in
        let preveal = BProcDecl ("reveal_" + x, [], [], [(l, ens)], Some [(l, s_forall)], pk) in
        [(l, ftrig); (l, fdecl); (l, fimpl); (l, preveal)]
    | _ -> [(l, d)]
  ) with e -> raise (LocErr (l, e))

let expand_opaque_decls ds = List.collect expand_opaque_decl ds

(*****************************************************************************)

type senv = Map<id, btyp> //- map function name to function return type
type cenv = Map<id, (id * id list) list> //- map type name to constructor names and field names
let do_compile = ref false

let add_summary_env (decls:bdecl list) (senv:senv) (cenv:cenv):(senv * cenv) =
  List.fold
    (fun (senv, cenv) d ->
      match d with
      | BGlobalDecl (x, t, _, _) -> (Map.add x t senv, cenv)
      | BTypeDecl (xt, Some (_, cases)) ->
        (
          let senv =
            List.fold (fun senv (_, xc, ps) ->
                let senv = Map.add ("##" + xc) (BNamedType xt) senv in
                List.fold (fun senv (xf, tf, _) -> Map.add (xf + "#" + xc) tf senv) senv ps)
              senv
              cases in
          let cenv = Map.add xt (List.map (fun (_, xc, ps) -> (xc, List.map (fun (xf, _, _) -> xf) ps)) cases) cenv in
          (senv, cenv)
        )
      | BFunDecl (x, _, ret, _, _, _) -> (Map.add ("##" + x) ret senv, cenv)
      | _ -> (senv, cenv))
    (senv, cenv)
    decls

let summary_env (decls:bdecl list):(senv * cenv) = add_summary_env decls Map.empty Map.empty

(*****************************************************************************)

//- replace f with this.f for each f in this's datatype
let expand_this_decl (cenv:cenv) (l:loc, d:bdecl):(loc * bdecl) =
  try
  (
    let this_subst (t:btyp) =
      match t with
      | BNamedType xt ->
        (
          match Map.tryFind xt cenv with
          | Some cs ->
              let fields = List.collect (fun (xc, fs) -> List.map (fun xf -> (xc, xf)) fs) cs in
              List.fold
                (fun m (xc, xf) -> Map.add xf (BUop (BField (xf, Some (xt, xc, BFieldNative)), BVar "this")) m)
                Map.empty
                fields
          | None -> err ("could not find fields of type " + xt)
        )
      | _ -> err ("'this' parameter must be a datatype")
      in
    match d with
    | BFunDecl (xfun, ps, tret, Some e, a, ts) when List.exists (fun (x, _, _) -> x = "this") ps ->
        let (_, t, _) = List.find (fun (x, _, _) -> x = "this") ps in
        let e = subst_exp (this_subst t) e
        (l, BFunDecl (xfun, ps, tret, Some e, a, ts))
    | BProcDecl (xp, ps, rs, specs, b_opt, pk) ->
      (
        let var_ps = List.choose (fun (x, tf, _) ->
          match tf with BFormalType t -> Some (x, t) | _ -> None) ps in
        let inouts = List.collect (fun (_, s) -> match s with BInOut es -> es | _ -> []) specs in
        let var_rs = List.map (fun (x, t, _) -> (x, t)) (inouts @ rs) in
        let vars = var_ps @ var_rs in
        if (List.mem_assoc "this" vars) then
          let subst_map = this_subst (List.assoc "this" vars) in
          let specs = List.map (subst_spec subst_map) specs in
          let b_opt = match b_opt with None -> None | Some b -> Some (subst_block subst_map b) in
          (l, BProcDecl (xp, ps, rs, specs, b_opt, pk))
        else (l, BProcDecl (xp, ps, rs, specs, b_opt, pk))
      )
    | _ -> (l, d)
  ) with e -> raise (LocErr (l, e))

let expand_this_decls (cenv:cenv) ds = List.map (expand_this_decl cenv) ds

(*****************************************************************************)

let rec expand_overload_exp (senv:senv) (cenv:cenv) (e:bexp):bexp =
  fst (expand_overload_exp_typ senv cenv e)
and expand_overload_exp_typ (senv:senv) (cenv:cenv) (e:bexp):(bexp * btyp option) =
  let fe = expand_overload_exp senv cenv in
  let ft = expand_overload_exp_typ senv cenv in
  match e with
  | BLoc (l, e1) -> let (e1, t) = ft e1 in (BLoc (l, e1), t)
  | BVar x -> (e, Map.tryFind x senv)
  | BIntConst _ -> (e, None)
  | BRealConst _ -> (e, None)
  | BBv32 _ -> (e, None)
  | BBoolConst _ -> (e, None)
//  | BBitVectorConst _ -> (e, None)
  | BUop (BOld, e1) -> let (e1, t) = ft e1 in (BUop (BOld, e1), t)
  | BUop (BField (xf, _), e1) ->
    (
      match ft e1 with
      | (e1, Some (BNamedType xt)) ->
        (
          let app () =
            (
              match (Map.tryFind ("##" + xt + "__" + xf) senv, Map.tryFind ("##." + xf) senv) with
              | (None, None) -> (BUop (BField (xf, None), e1), None) // unknown
              | (Some tr, None) -> (BUop (BField (xf, Some (xt, xt, BFieldFun)), e1), Some tr)
              | (_, Some tr) -> (BUop (BField (xf, Some (xt, xt, BFieldDotFun)), e1), Some tr)
            ) in
          match Map.tryFind xt cenv with
          | None -> app ()
          | Some cases ->
            (
              // record selector
              let fields = List.map (fun (xc, fs) -> List.map (fun xf -> (xc, xf)) fs) cases in
              let fields = List.flatten fields in
              match List.filter (fun (xc, _xf) -> xf = _xf) fields with
              | [(xc, _)] -> 
                  let selector = xf + "#" + xc in
                  (BUop (BField (xf, Some (xt, xc, BFieldNative)), e1), Map.tryFind selector senv)
              | _ -> app ()
            )
        )
//      | (BVar x1, None) -> ft (BVar (x1 + "#" + xf)) // module component
      | (e1, t) -> (BUop (BField (xf, None), e1), None)
    )
  | BUop (op, e1) -> (BUop (op, fe e1), None)
  | BBop (BFieldUpdate (xf, _), e1, e2) ->
    (
      match ft e1 with
      | (e1, Some ((BNamedType xt) as t)) ->
        (
          match Map.tryFind xt cenv with
          | None -> err ("no type found for field update " + xf)
          | Some cases ->
            (
              let fields = List.map (fun (xc, fs) -> List.map (fun xf -> (xc, xf)) fs) cases in
              let fields = List.flatten fields in
              match List.filter (fun (xc, _xf) -> xf = _xf) fields with
              | [(xc, _)] -> (BBop (BFieldUpdate (xf, Some xc), e1, fe e2), Some t)
              | _ -> err ("field " + xf + " not found in type " + xt)
            )
        )
      | _ -> err ("no type found for field update " + xf)
    )
  | BBop (op, e1, e2) -> (BBop (op, fe e1, fe e2), None)
  | BCond (e1, e2, e3) -> let (e2, t) = ft e2 in (BCond (fe e1, e2, fe e3), t)
  | BQuant (q, xs, ts, ev) ->
    (
      let senv = List.fold (fun senv (x, t) -> Map.add x t senv) senv xs in
      let fe = expand_overload_exp senv cenv in
      (BQuant (q, xs, List.map (List.map fe) ts, fe ev), None)
    )
  | BSubscript (ea, es) ->
    (
      match ft ea with
      | (ea, Some (BArray (_, t))) -> (BSubscript (ea, List.map fe es), Some t)
      | (ea, Some (BNamedType xt)) ->
          let (bf, t) =
            match (Map.tryFind ("map#" + xt) senv, Map.tryFind ("##" + xt + "__map") senv) with
            | (Some (BArray (_, t)), _) -> (BFieldNative, Some t)
            | (_, Some (BArray (_, t))) -> (BFieldFun, Some t)
            | _ -> (BFieldNative, None) in
          (BSubscript (BUop (BField ("map", Some (xt, xt, bf)), ea), List.map fe es), t)
      | (ea, _) -> (BSubscript (ea, List.map fe es), None)
    )
  | BUpdate (ea, es, ev) ->
    (
      match ft ea with
      | (ea, ((Some (BNamedType xt)) as t)) -> (BApply (xt + "_update", [ea] @ (List.map fe es) @ [fe ev]), t)
      | (ea, t) -> (BUpdate (ea, List.map fe es, fe ev), t)
    )
  | BApply ("sizeof", [e1]) ->
    (
      let (e1, t1_opt) = ft e1 in
      match t1_opt with
      | Some (BNamedType xt1) ->
          (BApply ("sizeof##" + xt1, [fe e1]), Some BInt)
      | _ -> err ("in sizeof, no datatype found for expression")
    )
  | BApply (x, es) -> (BApply (x, List.map fe es), Map.tryFind ("##" + x) senv)

let rec expand_overload_stmt (senv:senv) (cenv:cenv) (s:bstmt):bstmt =
  let fe = expand_overload_exp senv cenv in
  let fb = expand_overload_block senv cenv in
  let ft t = match t with BFormalAlias e -> BFormalAlias (fe e) | _ -> t in
  match s with
  | BLocalDecl (x, t, lin, None) -> BLocalDecl (x, ft t, lin, None)
  | BLocalDecl (x, t, lin, Some e) -> BLocalDecl (x, ft t, lin, Some (fe e))
  | BLabel _ -> s
  | BGoto _ -> s
  | BAssign (x, e) -> BAssign (fe x, fe e)
  | BGroup b -> BGroup (fb b)
  | BIf (e, b1, b2_opt) ->
      BIf (fe e, fb b1, match b2_opt with None -> None | Some b2 -> Some (fb b2))
  | BWhile (e, invs, b) ->
      BWhile (fe e, List.map (fun (l, e) -> (l, fe e)) invs, fb b)
  | BForallGhost (fs, ts, e, b) ->
      let senv = List.fold (fun senv (x, t) -> Map.add x t senv) senv fs in
      let fe = expand_overload_exp senv cenv in
      let fb = expand_overload_block senv cenv in
      BForallGhost (fs, List.map (List.map fe) ts, fe e, fb b)
  | BAssume e -> BAssume (fe e)
  | BAssert (e, inv) -> BAssert (fe e, inv)
  | BSplit -> BSplit
  | BYield e -> BYield (fe e)
  | BHavoc e -> BHavoc (fe e)
  | BCall (xs, id, es, pars) ->
      BCall (List.map fe xs, id, List.map fe es, List.map (fun (x, es) -> (x, List.map fe es)) pars)
  | BReturn _ -> s
and expand_overload_block (senv:senv) (cenv:cenv) (b:bblock):bblock =
  let senv =
    List.fold
      (fun senv (l, s) ->
        try
        (
          match s with BLocalDecl (x, BFormalType t, _, _) -> Map.add x t senv | _ -> senv
        ) with e -> raise (LocErr (l, e)))
      senv
      b
    in
  List.map (fun (l, s) -> (l, expand_overload_stmt senv cenv s)) b

let expand_overload_spec (senv:senv) (senv_ret:senv) (cenv:cenv) ((l:loc), (s:bspec)):(loc * bspec) list =
 try
 (
  match s with
  | BRequires e -> [(l, BRequires (expand_overload_exp senv cenv e))]
  | BEnsures e -> [(l, BEnsures (expand_overload_exp senv_ret cenv e))]
  | BModifies es -> []
  | BInOut _ -> []
 ) with e -> raise (LocErr (l, e))

type id_path = id list //- path is a list of ids: x.y.z = [x; y; z]
let expand_overload_specs (proc:id) (env:env) (senv:senv) (senv_ret:senv) (cenv:cenv) (gmap:Map<id,bexp>) (specs:(loc * bspec) list):(loc * bspec) list =
  let rec preserved_paths (get_children:id_path -> id list) (paths:id_path list):id_path list =
    //- given list of paths that do change, compute paths that don't change
    let indexed_paths =
      List.fold (fun m path -> match path with [] -> m | h::t -> multi_add h t m) Map.empty paths in
    let indexed_paths = Map_toList indexed_paths in
    let children = Set_ofList (get_children []) in
    let mod_children = Set_ofList (List.map fst indexed_paths) in
    let preserved_children = Set_toList (Set_difference children mod_children) in
    let preserved_child_paths = List.map (fun x -> [x]) preserved_children in
    let preserved_subpaths ((x:id), (subpaths:id_path list)) =
      if List.exists (fun p -> p = []) subpaths then [] else // "modifies x" ==> preserve nothing from x
      let g (p:id_path):id list = get_children (x::p) in
      List.map (fun p -> x::p) (preserved_paths g subpaths) in
    preserved_child_paths @ (List.collect preserved_subpaths indexed_paths)
  let modified_vars (paths:id_path list):id list =
    List.collect (fun path -> match path with [] -> [] | x::_ -> [x]) paths in
  let rec path_of_exp (e:bexp):id_path =
    match e with
    | BVar x -> [x]
    | BUop (BField (x, _), e) -> (path_of_exp e) @ [x]
    | BSubscript (e, [BVar x]) when id_is_reg (x.ToLower()) -> (path_of_exp e) @ ["[]" + x]
    | _ -> err ("unexpected modifies: " + (string_of_bexp 0 e))
  let rec add_suffix (p:id_path) (e:bexp):bexp =
    match p with
    | [] -> e
    | x::xs when x.StartsWith("[]") -> add_suffix xs (BSubscript (e, [BVar (x.Substring("[]".Length))]))
    | x::xs -> add_suffix xs (BUop (BField (x, None), e))
    in
  let get_children (p:id_path) =
    match p with
    | [] -> []
    | x::xs ->
      (
        let (_, t) = expand_overload_exp_typ senv cenv (add_suffix xs (BVar x)) in
        match t with
        | (Some (BArray ([BInt], BInt))) -> List.map (fun (r:string) -> "[]" + (r.ToUpper())) all_regs
        | (Some (BNamedType "regs")) -> ["regs"; "efl"] // REVIEW: should this be hard-wired?
        | (Some (BNamedType xt)) ->
          (
            match Map.tryFind xt env.type_decls with
            | Some (Some ([], [(_, _, fs)])) -> List.map (fun (xf, _, _) -> xf) fs
            | Some (Some (fs, _)) -> fs
            | _ -> []
          )
        | _ -> []
      )
    in
  let mods =
    List.collect (fun (l, s) ->
      match s with BModifies es -> List.map (fun e -> (l, subst_exp gmap e)) es | _ -> []) specs in
  let (static_mods, mods) = List.partition (fun e ->
    match e with (_, BApply ("static", _)) -> true | _ -> false) mods in
  //- datatype variables:
  let locs_paths = List.map (fun (l, e) -> (l, path_of_exp e)) mods in
  let paths = List.map snd locs_paths in
  let loc_map = Map_ofList (List.map (fun (l, p) -> (List.hd p, l)) locs_paths) in
  let preserved = preserved_paths get_children paths in
  let mod_vars = Set_toList (Set_ofList (modified_vars paths)) in
  let modified = List.map (fun x -> (loc_map.[x], BModifies [BVar x])) mod_vars in
  let ensures_loc (ls:string, li) e = (ls + " (ensures " + (string_of_bexp 0 e) + "))", li) in
  let ensure p =
    match p with
    | [] -> err "internal error: expand_overload_specs"
    | x::xs ->
        let e = BBop (BEq, add_suffix xs (BVar x), add_suffix xs (BUop (BOld, BVar x))) in
        (ensures_loc (loc_map.[x]) e, expand_overload_exp senv cenv e)
    in
  let preserves = List.map ensure preserved in
  //- static variables:
  let static_mods = List.choose (fun (l, e) ->
    match e with (BApply ("static", [BVar mem; BApply (x, _)])) -> Some (mem, (l, x)) | _ -> None) static_mods in
  let static_mod_xs = Set_toList (Set_ofList (List.map fst static_mods)) in
  let static_mod_ls = List.map (fun mem -> (fst (List.assoc mem static_mods), mem)) static_mod_xs in
  let mod_vars = (List.map (fun (l, mem) -> mem) static_mod_ls) @ mod_vars in
  let modified = (List.map (fun (l, mem) -> (l, BModifies [BVar mem])) static_mod_ls) @ modified in
  let preserves_static =
    List.map (fun (l, mem) ->
        let xs = List.choose (fun (m, (_, x)) -> if m = mem then Some x else None) static_mods in
        let i = "i" in
        let mem_map = BUop (BField ("map", Some ("mem", "mem", BFieldNative)), BVar mem) in
        let mem_i = BSubscript (mem_map, [BVar i]) in
        let disjunct =
          List.fold_left
            (fun disjunct x -> BBop (BOr, disjunct, BBop (BEq, BVar i, BVar (static_addr x))))
            (BBop (BEq, mem_i, BUop (BOld, mem_i)))
            xs in
        (l, BQuant (BForall, [(i, BInt)], [[mem_i]], disjunct)))
      static_mod_ls in
  //- put everything together:
  let preserves = preserves_static @ preserves in
  let ensured = List.map (fun (l, e) -> (l, BEnsures e)) preserves in
  (if List.length preserves > 0 then extra_proc_invariants := Map.add proc preserves !extra_proc_invariants);
  (if List.length mod_vars > 0 then extra_proc_modifies := Map.add proc mod_vars !extra_proc_modifies);
  modified @ ensured @ (List.collect (expand_overload_spec senv senv_ret cenv) specs)

let expand_overload_decl (env:env) (senv:senv) (cenv:cenv) (gmap:Map<id,bexp>) (d:bdecl):bdecl =
  match d with
  | BAxiomDecl e -> BAxiomDecl (expand_overload_exp senv cenv e)
//  | BInvariantDecl e -> BInvariantDecl (expand_overload_exp senv cenv e)
  | BFunDecl (id, ps, ret, Some e, a, ts) ->
    (
      let senv = List.fold (fun senv (x, t, _) -> Map.add x t senv) senv ps in
      let f_ts ts = List.map (fun t -> List.map (expand_overload_exp senv cenv) t) ts in
      let ts = match ts with None -> None | Some ts -> Some (f_ts ts) in
      BFunDecl (id, ps, ret, Some (expand_overload_exp senv cenv e), a, ts)
    )
  | BProcDecl (id, ps, rets, specs, b_opt, proc) ->
    (
      let pspecs =
        match Map.tryFind id env.proc_decls
          with Some (_, (_, _, _, pspecs, _, _)) -> pspecs | None -> specs in
      let inouts = List.collect (fun (_, s) -> match s with BInOut io -> io | _ -> []) pspecs in
      let senv = List.fold (fun senv (x, t, _) -> Map.add x t senv) senv inouts in
      let senv = List.fold (fun senv (x, t, _) -> match t with BFormalType t -> Map.add x t senv | _ -> senv) senv ps in
      let senv_ret = List.fold (fun senv (x, t, _) -> Map.add x t senv) senv rets in
      let specs = expand_overload_specs id env senv senv_ret cenv gmap specs in
      let b_opt =
        match b_opt with None -> None | Some b -> Some (expand_overload_block senv_ret cenv b) in
      BProcDecl (id, ps, rets, specs, b_opt, proc)
    )
  | d -> d

(*****************************************************************************)

let exp_get_smem (e:bexp):bexp option =
  match e with
  | BSubscript (BUop (BField ("map", Some ("mem", "mem", BFieldNative)), e), [eptr]) -> Some e
  | _ -> None

let bcall xs p es = BCall (xs, p, es, [])

let exp_get_mem (e:bexp):(bexp * (loc -> bblock) * (loc -> bexp -> bblock) * (loc -> id -> bblock) * (loc -> bexp -> bblock)) option =
  let stack_ptr eptr =
    let sload = fun l -> [] in
    let sstore = fun l e -> [] in
    let sLoad = fun l dest -> [(l, bcall [BVar dest] "SLoad" [eptr])] in
    let sStore = fun l e -> [(l, bcall [] "SStore" [eptr; e])] in
    Some (eptr, sload, sstore, sLoad, sStore) in
  let rec _datatype_ptr is_shared arr eptr =
    match arr with
    | BVar x ->
      (
        let sload = fun l -> [] in
        let sstore = fun l e -> [] in
        let sLoad = fun l dest -> [(l, bcall [BVar dest] "Load" [arr; eptr])] in
        let sStore = fun l e -> [(l, bcall [] "Store" [BUop (BInOutOp, arr); eptr; e])] in
        (None, Some (eptr, sload, sstore, sLoad, sStore))
      )
    | _ -> (None, None)
    in
  let rec datatype_ptr is_shared arr eptr =
    let part_map_of e id =
      BSubscript (BUop (BField ("vars", Some ("partition", "partition", BFieldNative)), e), [id]) in
    let rec assign_rhs yt path eRead =
      match path with
      | [] -> BBop (BFieldUpdate ("part", Some yt), eRead, BVar "BEAT__partition")
      | (None, xf, xt, bf)::t ->
          let rhs = assign_rhs yt t (BUop (BField (xf, Some (xt, xt, bf)), eRead)) in
          BBop (BFieldUpdate (xf, Some xt), eRead, rhs)
      | (Some ei, xf, xt, bf)::t ->
          let ef = BUop (BField (xf, Some (xt, xt, bf)), eRead) in
          let rhs = assign_rhs yt t (BSubscript (ef, [ei])) in
          BBop (BFieldUpdate (xf, Some xt), eRead, BUpdate (ef, [ei], rhs))
      in
    match arr with
    // REVIEW: should we automatically treat any global var x as shared?
    | BApply ("Shared", [edata]) -> datatype_ptr true edata eptr
    | BVar x when is_shared ->
      (
        // call part_load(x__id, eptr);
        let id = BVar (x + "__id") in
        let lin = BVar "BEAT__linear" in
        let sload = fun l -> [(l, bcall [] "part_load" [id; eptr])] in
        let sstore = fun l e ->
          [ (l, BAssign (lin, id));
            (l, bcall [lin] "part_store_shared" [lin; eptr; e]);
            (l, BAssign (id, lin))] in
        let sLoad = fun l dest -> (sload l) @ [(l, bcall [BVar dest] "Load" [eptr])] in
        let sStore = fun l e -> (sstore l e) @ [(l, bcall [] "Store" [eptr; e])] in
        (Some (part_map_of (BVar "$part") id, [(None, x, "", BFieldFun)]), Some (eptr, sload, sstore, sLoad, sStore))
      )
    | BVar x ->
      (
        // call partition_load(x__id, my_part, $part.vars[me], eptr);
        // call part_load(me, eptr);
        let id = BVar (x + "__id") in
        let part = BVar "my_part" in
        let part_map = part_map_of (BVar "$part") (BVar "me") in
        let sload = fun l ->
          [ (l, bcall [] "partition_load" [id; part; part_map; eptr]);
            (l, bcall [] "part_load" [BVar "me"; eptr])] in
        let sstore = fun l e -> [(l, bcall [part] "partition_store" [id; part; part_map; eptr; e])] in
        let sLoad = fun l dest -> (sload l) @ [(l, bcall [BVar dest] "Load" [eptr])] in
        let sStore = fun l e -> (sstore l e) @ [(l, bcall [] "Store" [eptr; e])] in
        (Some (part_map_of part id, [(None, x, "", BFieldFun)]), Some (eptr, sload, sstore, sLoad, sStore))
      )
    | BUop (BField (xf, Some (xt, _, bf)), edata) ->
      (
        match datatype_ptr is_shared edata eptr with
        | (Some (parent_map, path), Some (_, sload, sstore, sLoad, sStore)) ->
            // call partition_load(xt__xf__id, edata.part, parent_map, eptr);
            let id = BVar (xt + "__" + xf + "__id") in
            let part = BUop (BField ("part", Some (xt, xt, bf)), edata) in
            let root = let (_, x, _, _) = List.hd path in BVar x in
            let sload = fun l -> (l, bcall [] "partition_load" [id; part; parent_map; eptr])::(sload l) in
            let sstore = (fun l e ->
              (l, bcall [BVar "BEAT__partition"] "partition_store" [id; part; parent_map; eptr; e])::
                (l, BAssign (root, assign_rhs xt (List.tl path) root))::
                  (sstore l e)) in
            let sLoad = fun l dest -> (sload l) @ [(l, bcall [BVar dest] "Load" [eptr])] in
            let sStore = fun l e -> (sstore l e) @ [(l, bcall [] "Store" [eptr; e])] in
            (Some (part_map_of part id, path @ [(None, xf, xt, bf)]), Some (eptr, sload, sstore, sLoad, sStore))
        | _ -> (None, None)
      )
    | BSubscript (BUop (BField ("map", Some (xt, _, bf)), edata), [ei]) ->
      (
        match datatype_ptr is_shared edata eptr with
        | (Some (parent_map, path), Some (_, sload, sstore, sLoad, sStore)) ->
            // call partition_load(ei, edata.part, parent_map, eptr);
            let part = BUop (BField ("part", Some (xt, xt, bf)), edata) in
            let root = let (_, x, _, _) = List.hd path in BVar x in
            let sload = fun l -> (l, bcall [] "partition_load" [ei; part; parent_map; eptr])::(sload l) in
            let sstore = (fun l e ->
              (l, bcall [BVar "BEAT__partition"] "partition_store" [ei; part; parent_map; eptr; e])::
                (l, BAssign (root, assign_rhs xt (List.tl path) root))::
                  (sstore l e)) in
            let sLoad = fun l dest -> (sload l) @ [(l, bcall [BVar dest] "Load" [eptr])] in
            let sStore = fun l e -> (sstore l e) @ [(l, bcall [] "Store" [eptr; e])] in
            (Some (part_map_of part ei, path @ [(Some ei, "map", xt, bf)]), Some (eptr, sload, sstore, sLoad, sStore))
        | _ -> (None, None)
      )
    | _ -> (None, None)
    in
  match e with
  | BSubscript (BUop (BField ("map", Some ("mem", _, BFieldNative)), edata), [eptr]) ->
      snd (_datatype_ptr false edata eptr)
  | BSubscript (BUop (BField ("map", Some ("finite_map", _, BFieldNative)), BUop (BField ("stk", Some ("mems", _, _)), BVar _)), [eptr]) ->
      stack_ptr eptr
  | BSubscript (BUop (BField ("map", Some ("finite_map", _, BFieldNative)), edata), [eptr]) ->
      snd (datatype_ptr false edata eptr)
  | BVar x when x.StartsWith("$beat__stackvar__") ->
      let x2 = x.Substring("$beat__stackvar__".Length) in
      let xi = x2.Substring(0, x2.IndexOf("_esp__")) in
      stack_ptr (BBop (BAdd, BVar "esp", BIntConst (big_int_of_string xi)))
      //correct, but slower:
      //let edata = BUop (BField ("stk", Some ("mems", BFieldFun)), BVar "$mem") in
      //let eptr = BBop (BAdd, BVar "esp", BIntConst (big_int_of_string xi)) in
      //snd (datatype_ptr false edata eptr)
  | BUop (BField (xf, Some (xt, _, BFieldFun)), e) ->
      let eptr = BVar (static_addr xf) in
      let id = BVar ("?Id" + xf) in
      let sload = fun l -> [(l, bcall [] ("loadInt_" + xt) [id; eptr])] in
      let sstore = fun l e -> [(l, bcall [] ("storeInt_" + xt) [id; eptr; e])] in
      let sLoad = fun l dest -> (sload l) @ [(l, bcall [BVar dest] "Load" [eptr])] in
      let sStore = fun l e -> (sstore l e) @ [(l, bcall [] "Store" [eptr; e])] in
      Some (eptr, sload, sstore, sLoad, sStore)
  | BApply ("static", [emem; BApply (x, _)]) ->
      let eptr = BVar (static_addr x) in
      let sload = fun l -> [] in
      let sstore = fun l e -> [] in
      let sLoad = fun l dest -> [(l, bcall [BVar dest] "Load" [emem; eptr])] in
      let sStore = fun l e -> [(l, bcall [] "Store" [emem; eptr; e])] in
      Some (eptr, sload, sstore, sLoad, sStore)
  | _ -> None

let exp_is_reg (e:bexp) =
  match e with BVar x when id_is_reg x -> true | _ -> false

// REVIEW: this may pull in non-const variables
let exp_is_const (e:bexp) =
  match e with BIntConst _ -> true | BVar x when not (id_is_reg x) -> true | _ -> false

let exp_is_mem (e:bexp) = match exp_get_mem e with Some _ -> true | None -> false

let exp_is_reg_or_const (e:bexp) = (exp_is_reg e) || (exp_is_const e)
let exp_is_reg_mem_or_const (e:bexp) = (exp_is_reg e) || (exp_is_const e) || (exp_is_mem e)

let exps_for_x86_mem (e1:bexp) (e2:bexp):bool =
      ((exp_is_reg e1) && (exp_is_reg_mem_or_const e2))
   || ((exp_is_reg e2) && (exp_is_reg_mem_or_const e1))
   || ((exp_is_const e2) && (exp_is_reg_mem_or_const e1))

//let opn_of_exp (l:loc) (e:bexp):bexp * (loc * bstmt) list =
//  match exp_get_mem e with
//  | Some (eptr, mLoad, _, _, _) -> (BApply ("OpnMem", [eptr]), mLoad l)
//  | None -> (BApply ("OpnReg", [e]), [])

let negate_comparison_op (op:bbop):bbop =
  match op with
  | BEq -> BNe
  | BNe -> BEq
  | BLt -> BGe
  | BGt -> BLe
  | BLe -> BGt
  | BGe -> BLt
  | _ -> err "conditional expression must be a comparison expression"

let flip_comparison_op (op:bbop):bbop =
  match op with
  | BEq -> BEq
  | BNe -> BNe
  | BLt -> BGt
  | BGt -> BLt
  | BLe -> BGe
  | BGe -> BLe
  | _ -> err "conditional expression must be a comparison expression"

let get_comparison_exp (polarity:bool) (e:bexp):(bbop * bexp * bexp) =
  let reorder (op, e1, e2) =
    let may_be_const e = match e with BIntConst _ -> true | BVar x when x.StartsWith("?") -> true | _ -> false in // HACK
    if may_be_const e2 || (exp_is_reg_or_const e2 && not (exp_is_const e1)) then (op, e1, e2)
    else (flip_comparison_op op, e2, e1) // move consts to right, memory ops to left
  in
  match (polarity, e) with
  | (true, BBop (op, e1, e2)) -> reorder (op, e1, e2)
  | (false, BBop (op, e1, e2)) -> reorder (negate_comparison_op op, e1, e2)
  | _ -> err "conditional expression must be a comparison expression"

let new_label:unit->id =
  let nextLabel = ref 0 in
  fun () -> incr nextLabel; "__L" + (string !nextLabel)

let add_local (locals:(id * (bformal_typ * linearity)) list ref) (x:id) (t:bformal_typ) (lin:linearity):unit =
  if not (List.mem_assoc x !locals) then locals := (x, (t, lin))::(!locals);

(*
let tmp_var (i:int):id = "__tmp" + (string i)

let get_tmp_var (locals:(id * bformal_typ) list ref) (i:int):id =
  let x = tmp_var i in
  add_local locals x (BFormalType BInt);
  x
*)

let global_param_name (f:id) (p:id) = "__" + f + "$" + p

let ghost_subst_map (ds:(loc * bdecl) list):Map<id,bexp> =
  List.fold (fun m (l, d) ->
      match d with
      | BGlobalStaticDecl (x, mem) -> m.Add(x, BApply ("static", [BVar mem; BApply (x, [])]))
      | BFunDecl (x, _, _, Some e, _, _) when x.StartsWith("__Beat_") ->
        (
          let x = x.Substring("__Beat_".Length) in
          if x.StartsWith("define_") then m.Add(x.Substring("define_".Length), e)
          else if x.StartsWith("defineD_") then m.Add("$" + x.Substring("defineD_".Length), e)
          else if x.StartsWith("defineQ_") then m.Add("?" + x.Substring("defineQ_".Length), e)
          else err ("unknown Beat definition: " + x)
        )
      | _ -> m)
    (List.fold
      (fun m r -> m.Add(r, BSubscript(regs_arr, [BVar (r.ToUpper())])))
      (Map.add "efl" (reg_efl) Map.empty)
      all_regs)
    ds

let static_subst_map (ds:(loc * bdecl) list):Map<id,bexp> =
  List.fold (fun m (l, d) ->
      match d with
      | BGlobalStaticDecl (x, mem) -> m.Add(x, BApply ("static", [BVar mem; BApply (x, [])]))
      | _ -> m)
    Map.empty
    ds

let rec compile_exp (locals:(id * (bformal_typ * linearity)) list ref) (l:loc) (dest:id) (temp:int) (e:bexp):(loc * bstmt) list =
  let er () = err ("cannot compile assignment " + dest + " := " + (string_of_bexp 0 e) + " at line " + (string l)) in
  match e with
  | BLoc (l, e) -> compile_exp locals l dest temp e
  | BIntConst i -> [(l, BAssign (BVar dest, e))]
  | BBop (op, ((BVar x1) as e1), e2) when dest = x1 && exps_for_x86_mem e1 e2 ->
    ( match op with
      | BAdd        -> [(l, bcall [BVar dest] "Add"        [e1; e2])]
      | BSub        -> [(l, bcall [BVar dest] "Sub"        [e1; e2])]
      | BAddChecked -> [(l, bcall [BVar dest] "AddChecked" [e1; e2])]
      | BSubChecked -> [(l, bcall [BVar dest] "SubChecked" [e1; e2])]
      | _ -> er ()
    )
  | BBop (op, e1, e2) -> er ()
  | _ ->
    (
      match (e, exp_get_mem e) with
      | (_, Some (_, _, _, mLoad, _)) -> mLoad l dest
      | (BVar x, None) -> if dest = x then [] else [(l, BAssign (BVar dest, e))]
      | _ -> er ()
    )

let compile_comparison (polarity:bool) (locals:(id * (bformal_typ * linearity)) list ref) (l:loc) (e:bexp):(bexp * (loc * bstmt) list) =
  let f op e1 e2 ss =
    let jop =
      match op with
      | BEq -> "Je" | BNe -> "Jne" | BLt -> "Jb" | BGt -> "Ja" | BLe -> "Jbe" | BGe -> "Jae"
      | _ -> err ("unsupported comparison at line " + (string l)) in
//    let ((o1, ss1), (o2, ss2)) = (opn_of_exp l e1, opn_of_exp l e2) in
    let is_stack = match e1 with BVar x when x.StartsWith("$beat__stackvar__") -> true | _ -> false in
    let cmp_ins = if exp_is_reg e1 then "Cmp" else if is_stack then "SCmpLoad" else "CmpLoad" in
    (BApply (jop, [BVar "efl"]), ss @ [(l, bcall [] cmp_ins [e1; e2])]) in
  let (op, e1, e2) = get_comparison_exp polarity e in
  if (exps_for_x86_mem e1 e2) then (f op e1 e2 [])
  else err ("unsupported comparison operands at line " + (string l))

let rec compile_stmt (env:env) (pk:proc_kind) (locals:(id * (bformal_typ * linearity)) list ref) (l:loc, s:bstmt):(loc * bstmt) list =
  try compile_stmt_inner env pk locals (l, s)
  with e -> raise (LocErr (l, e))
and compile_stmt_inner (env:env) (pk:proc_kind) (locals:(id * (bformal_typ * linearity)) list ref) (l:loc, s:bstmt):(loc * bstmt) list =
  let is_ghost = match pk with (Procedure (PGhost, _)) -> true | _ -> false in
  let dot_name xdata xf = xdata + "___BEAT_" + xf in
  let unpack unpacks xdata xt xc =
    if List.mem_assoc xdata !unpacks then () else
    let (_, fs) = find_constructor env xt xc in
    let xfs = List.map (fun (xf, _, _) -> BVar (dot_name xdata xf)) fs in
    let s1 = BCall (xfs, "destruct##" + xc, [BVar xdata], []) in
    let s2 = BCall ([BVar xdata], "construct##" + xc, xfs, []) in
    unpacks := (xdata, (s1, s2))::!unpacks;
    List.iter (fun (xf, t, lin) ->
      add_local locals (dot_name xdata xf) (BFormalType t) lin) fs
    in
  let rec inout_exp (unpacks:(id * (bstmt * bstmt)) list ref) (e:bexp):id =
    match e with
    | BVar x -> x
    | BUop (BField (xf, Some (xt, xc, _)), edata) ->
      (
        let xdata = inout_exp unpacks edata in
        unpack unpacks xdata xt xc;
        dot_name xdata xf
      )
    | BUop (BField (xf, None), _) -> err ("cannot determine type of field access " + xf + " in expression " + (string_of_bexp 0 e))
    | _ -> err ("expected variable or field access in 'inout' argument")
    in
  let unpack_stmts unpacks =
    let ss1 = List.map (fun (_, (s1, _)) -> (l, s1)) (List.rev !unpacks) in
    let ss2 = List.map (fun (_, (_, s2)) -> (l, s2)) !unpacks in
    (ss1, ss2)
  match s with
  | BLocalDecl (x, t, lin, None) -> add_local locals x t lin; []
  | BLocalDecl (x, t, lin, Some e) -> add_local locals x t lin; compile_stmt env pk locals (l, BAssign (BVar x, e))
  | BLabel x -> [(l, s)]
  | BGoto x -> [(l, s)]
  | BAssign (BVar x, e) when not (id_is_reg x) -> [(l, s)]
  | BAssign (BVar x, e) ->
    (
      let ss = compile_exp locals l x 0 e
      match ss with [(_, ((BCall _) as s))] -> compile_stmt env pk locals (l, s) | _ -> ss
    )
  | BAssign ((BUop (BField (xf, Some (xt, xc, BFieldNative)), e1)) as lhs, e2) ->
    (
      let (lin, _) = find_constructor env xt xc in
      match lin with
      | Non -> compile_stmt env pk locals (l, BAssign (e1, BBop (BFieldUpdate (xf, Some xt), e1, e2)))
      | Lin _ ->
        (
          let unpacks = ref ([]:(id * (bstmt * bstmt)) list) in
          let xlhs = BVar (inout_exp unpacks lhs) in
          let (ss1, ss2) = unpack_stmts unpacks in
          ss1 @ [(l, BAssign (xlhs, e2))] @ ss2
        )
    )
  | BAssign ((BUop (BField _, _)) as lhs, e) | BAssign ((BApply ("static", _)) as lhs, e) ->
    (
      match exp_get_mem lhs with
      | Some (_, _, _, _, store) -> store l e
      | _ -> [(l, s)]
    )
    | BAssign (BSubscript (x1, x2), e) ->
      compile_stmt env pk locals (l, BAssign (x1, BUpdate (x1, x2, e)))
  | BAssign (x, e) -> [(l, s)]
  | BGroup b -> [(l, BGroup (compile_block env pk locals b))]
  | BIf (BApply (_, [BVar "efl"]), [(lg, BGoto target)], None) -> [(l, s)]
  | BIf (e, [(lg, BGoto target)], None) ->
    (
      let (eb, ss) = compile_comparison true locals l e in
      ( ss @
        [(l, BIf (eb, [(lg, BGoto target)], None))]
      )
    )
  | BIf (e, b1, None) when is_ghost ->
    (
      [(l, BIf (e, compile_block env pk locals b1, None))]
    )
  | BIf (e, b1, Some b2) when is_ghost ->
    (
      [ (l, BIf (e, compile_block env pk locals b1, None));
        (l, BIf (BUop (BNot, e), compile_block env pk locals b2, None))]
    )
  | BIf (e, b1, None) ->
    (
      let (eb, ss) = compile_comparison false locals l e in
      let l1 = new_label () in
      ( ss @
        [(l, BIf (eb, [(l, BGoto l1)], None))] @
        (compile_block env pk locals b1) @
        [(l, BLabel l1)]
      )
    )
  | BIf (e, b1, Some b2) ->
    (
      let (eb, ss) = compile_comparison false locals l e in
      let l1 = new_label () in
      let l2 = new_label () in
      ( ss @
        [(l, BIf (eb, [(l, BGoto l1)], None))] @
        (compile_block env pk locals b1) @
        [(l, BGoto l2)] @
        [(l, BLabel l1)] @
        (compile_block env pk locals b2) @
        [(l, BLabel l2)]
      )
    )
  | BWhile (e, invs, b) ->
    (
      let (eb, ss) = compile_comparison false locals l e in
      let l1 = new_label () in
      let l2 = new_label () in
      ( [(l, BLabel l1)] @
        (List.map (fun (l, e) -> (l, BAssert (e, true))) invs) @
        ss @
        [(l, BIf (eb, [(l, BGoto l2)], None))] @
        (compile_block env pk locals b) @
        [(l, BGoto l1)] @
        [(l, BLabel l2)]
      )
    )
  | BForallGhost (fs, ts, e, b) -> [(l, s)]
  | BAssume e -> [(l, s)]
  | BAssert (e, inv) -> [(l, s)]
  | BSplit -> [(l, s)]
  | BYield _ -> [(l, s)]
  | BHavoc e -> [(l, s)]
(*
  | BCall ([x], p, [e1; (BUop (BField _, _)) as rhs]) when proc_kind p = PIns ->
    (
      match exp_get_mem rhs with
      | Some (eptr, load, _, _, _) ->
        (
          let call = BCall ([x], p + "Load", [e1; BApply ("OpnMem", [eptr])]) in
          (load l) @ [(l, call)]
        )
      | _ -> [(l, s)]
    )
  | BCall ([(BUop (BField _, _)) as lhs], p, [lhs2; e2]) when proc_kind p = PIns && lhs = lhs2 ->
    (
      match exp_get_mem lhs with
      | Some (eptr, load, store, _, _) ->
        (
          let e = BBop (get_op p, lhs, e2) in
          let call = BCall ([], p + "Store", [BApply ("OpnMem", [eptr]); e2]) in
          (load l) @ (store l e) @ [(l, call)]
        )
      | _ -> [(l, s)]
    )
  | BCall (xs, p, es, pars) ->
      // TODO: clean up or eliminate?
      if not (env.proc_decls.ContainsKey p) then [(l, BCall (xs, p, es, pars))] else
      let (_, (_, ps, rets, specs, b, _)) = env.proc_decls.[p] in
      let ps = List.filter (fun (_, t, _) -> match t with BFormalType _ -> true | _ -> false) ps in
      [(l, BCall (xs, p, es, pars))]
*)
  | BCall (xs, p, es, pars) when env.proc_decls.ContainsKey(p) ->
      // call p(inout x.f)
      // ==>
      // linear var tmp_xf:tf
      // let tx(...,tmp_xf,...) := x;
      // call p(inout tmp_xf)
      // let x := tx(...,tmp_xf,...);
      let (_, (_, proc_fs, _, _, _, _)) = env.proc_decls.[p] in
      let unpacks = ref ([]:(id * (bstmt * bstmt)) list) in
      let arg proc_f e =
        match (proc_f, e) with
        | ((_, _, Lin (LinInOut, _)), BUop (BInOutOp, ei)) -> BUop (BInOutOp, BVar (inout_exp unpacks ei))
        | ((x, _, _), BUop (BInOutOp, ei)) -> err ("inout argument passed to non-inout parameter " + x)
        | ((x, _, Lin (LinInOut, _)), _) -> err ("argument to inout parameter " + x + " must be marked inout")
        | ((_, _, Lin (LinConst, _)), _) -> BVar (inout_exp unpacks e)
        | _ -> e in
      let (n_proc_fs, n_es) = (List.length proc_fs, List.length es) in
      if n_proc_fs <> n_es then err ("proc: " + p + " expected " + (string n_proc_fs) + " arguments, found " + (string n_es)) else
      let es = List.map2 arg proc_fs es in
      let (ss1, ss2) = unpack_stmts unpacks in
      ss1 @ [(l, BCall (xs, p, es, pars))] @ ss2
  | BCall (xs, p, es, pars) -> [(l, s)]
  | BReturn _ -> [(l, s)]

and embellish_stmts (env:env) (b:bblock):bblock =
  let embellish = embellish_stmts env in
  let get_instruction p =
    match Map.tryFind p env.proc_decls with
    | Some (_, (_, ps, rets, specs, Some b, Instruction)) -> Some (ps, rets, specs, b)
    | _ -> None
  let build_instruction l xs p args =
    match get_instruction p with
    | Some (ps, rets, specs, b) ->
      (
        if List.length args != List.length ps then err ("wrong number of arguments to " + p) else
        if List.length xs != List.length rets then err ("wrong number of return values from " + p) else
        let resultMap =
          List.collect (fun (_, s) ->
              match s with
              | BEnsures (BApply ("Output", [BVar x; e])) -> [(x, (false, e))]
              | BEnsures (BApply ("InputOutput", [BVar x; e])) -> [(x, (true, e))]
              | _ -> [])
            specs in
        let resultMap = Map_ofList resultMap in
        let substs =
          List.map2 (fun (x, ft, _) e ->
              let app f args = BApply (f, args) in
              let reg (r:string) = BVar (r.ToUpper()) in
              let (ft, e) =
                match (ft, exp_get_mem e) with
                | (BFormalType (BNamedType "opn"), Some (eptr, _, _, _, _))
                | (BFormalType (BNamedType "opn_mem_of_int"), Some (eptr, _, _, _, _)) ->
                    (BFormalType (BNamedType "opn_mem_of_int"), eptr)
                | _ -> (ft, e)
                in
              match (ft, e) with
              | (BFormalType (BNamedType "reg"), BVar r) when id_is_reg r -> (x, reg r)
              | (BFormalType (BNamedType "opn"), BVar r) when id_is_reg r -> (x, app "OReg" [reg r])
              | (BFormalType (BNamedType "opn"), BVar xc) -> (x, app "OConst" [e])
              | (BFormalType (BNamedType "opn"), BIntConst _ ) -> (x, app "OConst" [e])
              | (BFormalType (BNamedType "opn_mem_of_int"), BBop (BAdd, BBop (BAdd, BVar r1, BBop (BMul, scale, BVar r2)), off))
                  when id_is_reg r1 && id_is_reg r2 ->
                  (x, app "OMem" [app "MIndex" [reg r1; scale; reg r2; off]])
              | (BFormalType (BNamedType "opn_mem_of_int"), BBop (BAdd, BVar r1, BBop (BMul, scale, BVar r2)))
                  when id_is_reg r1 && id_is_reg r2 ->
                  (x, app "OMem" [app "MIndex" [reg r1; scale; reg r2; BIntConst zero_big_int]])
              | (BFormalType (BNamedType "opn_mem_of_int"), BBop (BAdd, BVar r1, BVar r2))
                  when id_is_reg r1 && id_is_reg r2 ->
                  (x, app "OMem" [app "MIndex" [reg r1; BIntConst unit_big_int; reg r2; BIntConst zero_big_int]])
              | (BFormalType (BNamedType "opn_mem_of_int"), BBop (BAdd, BVar r, off)) when id_is_reg r ->
                  (x, app "OMem" [app "MReg" [reg r; off]])
              | (BFormalType (BNamedType "opn_mem_of_int"), BVar r) when id_is_reg r ->
                  (x, app "OMem" [app "MReg" [reg r; BIntConst zero_big_int]])
              | (BFormalType (BNamedType "opn_mem_of_int"), BVar xc) ->
                  (x, app "OMem" [app "MConst" [BVar xc]])
              // TODO: more cases
              | _ -> (x, e))
            (ps @ (List.map (fun (x, t, l) -> (x, BFormalType t, l)) rets))
            (args @ xs) in
        let substs = Map_ofList substs in
        let coercions =
          List.map2 (fun (x, _, _) e ->
              match (Map.tryFind x resultMap, exp_get_mem e) with
              | (_, None) -> []
              | (None, Some (_, sLoad, _, _, _)) -> sLoad l
              | (Some (false, ev), Some (_, _, sStore, _, _)) -> sStore l (subst_exp substs ev)
              | (Some (true, ev), Some (_, sLoad, sStore, _, _)) -> (sLoad l) @ (sStore l (subst_exp substs ev)))
            ps
            args in
        (List.flatten coercions) @ (List.map (fun (_, s) -> (l, s)) (subst_block substs b))
      )
    | None -> err ("Could not find instruction declaration for " + p)
    in
  let group_h l ss h t = (l, BGroup (ss @ [h]))::(embellish t) in
  match b with
  | [] -> []
  | (l, BCall (xs, p, args, []))::t when not (get_instruction p = None) ->
      (build_instruction l xs p args) @ (embellish t)
  | ((l, BCall (_, x, _, _)) as h)::t when (proc_kind x = PProc) ->
      group_h l (build_instruction l [] "Call" []) h t
  | (l, BReturn BRet)::t -> group_h l (build_instruction l [] "Ret" []) (l, BReturn BRet) t
  | (l, BReturn BIRet)::t -> group_h l (build_instruction l [] "IRet" []) (l, BReturn BIRet) t
  | (l, BReturn BEmbellishRet)::t ->
      group_h l (build_instruction l [] "Ret" []) (l, BReturn BRet) t
  | (l, BAssign (BVar x, e))::t when (id_is_reg x) -> embellish ((l, bcall [BVar x] "Mov" [e])::t)
  | h::t -> h::(embellish t)

and compile_block (env:env) (pk:proc_kind) (locals:(id * (bformal_typ * linearity)) list ref) (b:bblock):bblock =
  let b = List.flatten (List.map (compile_stmt env pk locals) b) in
  b

let rec aliases_block (m:Map<id,bexp>) (mptr:Map<id,bexp>) (mInvs:(loc * bexp) list) (b:bblock):bblock =
  match b with
  | [] -> []
  | (l, BLocalDecl (x, BFormalAlias (BVar y), _, None))::ss -> aliases_block (m.Add(x, BVar y)) mptr mInvs ss
  | (l, BLocalDecl (x, BFormalAlias (BVar y), _, Some e))::ss ->
      (l, BAssign (BVar y, subst_exp m e))::(aliases_block (m.Add(x, BVar y)) mptr mInvs ss)
  | (l, BLocalDecl (x, BFormalAlias y, lin, e_opt))::ss ->
    (
      match (exp_get_mem y, exp_get_smem y) with
      | (Some ((BBop (BAdd, BVar "esp", BIntConst i)) as eptr, _, _, _, sStore), Some e_smem) ->
        (
          let xx = "$beat__stackvar__" + (string i) + "_esp__" + x in
          let mm = m.Add(x, BVar xx) in
          let mptr = mptr.Add(x, y) in
          let mInvs = (l, BBop (BEq, BVar xx, y))::mInvs in
          let decl e = BLocalDecl (xx, BFormalType BInt, lin, Some e) in
          let ss = aliases_block mm mptr mInvs ss in
          match e_opt with
          | None -> (l, decl (BSubscript (BUop (BField ("map", Some ("mem", "mem", BFieldNative)), e_smem), [eptr])))::ss
          | Some e -> (l, decl e)::(subst_block m (sStore l e)) @ ss
        )
      | _ -> err ("unexpected alias: " + x)
    )
  | ((l, BAssign (BVar x, e)) as s)::ss when m.ContainsKey(x) ->
    (
      match (m.[x], exp_get_mem m.[x]) with
      | (BVar y, Some (eptr, _, _, _, store)) ->
          let assign = (l, BAssign (BVar y, subst_exp m e)) in
          assign::(subst_block m (store l e)) @ (aliases_block m mptr mInvs ss)
      | _ -> (subst_stmt m s)::(aliases_block m mptr mInvs ss)
    )
(*
  | ((l, BCall ([x], f, [e1; BVar x2])) as s)::ss when proc_kind f = PIns && m.ContainsKey(x2) ->
    (
      match (m.[x2], exp_get_mem m.[x2]) with
      | (BVar y, Some (eptr, load, _, _, _)) ->
        (
          let call = BCall ([x], f + "Load", [subst_exp m e1; BApply ("OpnMem", [eptr])]) in
          (load l) @ (l, call)::(aliases_block m mptr mInvs ss)
        )
      | _ -> (subst_stmt m s)::(aliases_block m mptr mInvs ss)
    )
  | ((l, BCall ([BVar x], f, [BVar x1; e2])) as s)::ss when proc_kind f = PIns && m.ContainsKey(x) && x = x1 ->
    (
      match (m.[x], exp_get_mem m.[x]) with
      | (BVar y, Some (eptr, load, store, _, _)) ->
        (
          let e = subst_exp m (BBop (get_op f, BVar x1, e2)) in
          let call = BCall ([], f + "Store", [BApply ("OpnMem", [eptr]); subst_exp m e2]) in
          let assign = BAssign (BVar y, e) in
          (load l) @ (store l e) @ (l, call)::(l, assign)::(aliases_block m mptr mInvs ss)
        )
      | _ -> (subst_stmt m s)::(aliases_block m mptr mInvs ss)
    )
*)
  | ((l, BCall ([BVar x], f, _, _)) as s)::ss when m.ContainsKey(x) ->
    (
      match (m.[x], exp_get_mem m.[x]) with
      | (BVar y, Some (eptr, _, _, _, _)) ->
        (
          let assign = BAssign (BVar y, mptr.[x]) in
          (subst_stmt m s)::(subst_stmt m (l, assign))::(aliases_block m mptr mInvs ss)
        )
      | _ -> (subst_stmt m s)::(aliases_block m mptr mInvs ss)
    )
  | (l, BIf (e, s1, None))::ss ->
      (l, BIf (subst_exp m e, aliases_block m mptr mInvs s1, None))::(aliases_block m mptr mInvs ss)
  | (l, BIf (e, s1, Some s2))::ss ->
      (l, BIf (subst_exp m e, aliases_block m mptr mInvs s1, Some (aliases_block m mptr mInvs s2)))
        ::(aliases_block m mptr mInvs ss)
  | (l, BWhile (e, invs, s))::ss ->
      let invs = List.map (fun (l, e) -> (l, subst_exp m e)) invs in
      (l, BWhile (subst_exp m e, mInvs @ invs, aliases_block m mptr mInvs s))::(aliases_block m mptr mInvs ss)
  | ((_, BLabel _) as s1)::((l, BAssert (_, true)) as s2)::ss ->
      (s1::(List.map (fun (l, e) -> (l, BAssert (e, true))) mInvs)) @ (aliases_block m mptr mInvs (s2::ss))
  | s::ss -> (subst_stmt m s)::(aliases_block m mptr mInvs ss)

//- Replace missing function arguments with defaults
let fun_defaults_exp (env:env) (e:bexp):bexp =
  map_exp
    (fun e ->
      match e with
      | BApply (x, es) when env.fun_decls.ContainsKey(x) ->
        let (_, (_, ps, _, _, _, _)) = env.fun_decls.[x] in
        let arg_err s = err (s + "; expected: " + (sep_list ", " (List.map string_of_bformal_fun ps))  + " found: " + (sep_list ", " (List.map (string_of_bexp (-5)) es))) in
        let rec f ps es =
          match (ps, es) with
          | ([], []) -> []
          | ([], _) -> arg_err ("too many arguments to " + x)
          | ((_, _, None)::_, []) -> arg_err ("missing arguments to " + x)
          | ((_, _, Some e)::ps, []) -> e::(f ps es)
          | (_::ps, e::es) -> e::(f ps es) in
        Some (BApply (x, f ps es))
      | _ -> None)
    e

let compile_decl (env:env) (gmap:Map<id,bexp>) (static_map:Map<id,bexp>) (modify:bexp list ref) (l:loc, d:bdecl):(loc * bdecl) list =
  try
  (
    match d with
    | BGlobalDecl _ -> [(l, d)]
    | BGlobalStaticDecl (x, mem) -> [(l, BStaticDecl x)]
    | BStaticDecl _ -> [(l, d)]
    | BConstDecl (x, t, Some e) -> [(l, BConstDecl (x, t, Some (subst_exp gmap e)))]
    | BConstDecl _ -> [(l, d)]
    | BAxiomDecl e -> [(l, BAxiomDecl (subst_exp gmap e))]
    | BTypeDecl (xt, Some (_, cs)) ->
      (
        let get (_, xc, fs) =
          List.map (fun (xf, tf, _) ->
              let x1 = "___x1" in
              let e = BUop (BField (xf, Some (xt, xc, BFieldNative)), BVar x1) in
              (l, BFunDecl (xc + "__" + xf, [(x1, BNamedType xt, None)], tf, Some e, None, None)))
            fs in
        let update (_, xc, fs) =
          List.map (fun (xf, tf, _) ->
              let x1 = "___x1" in
              let x2 = "___x2" in
              let args =
                List.map (fun (_xf, _, _) ->
                    if xf = _xf then BVar x2 else BUop (BField (_xf, Some (xt, xc, BFieldNative)), BVar x1))
                  fs in
              let e = BApply (xc, args) in
              let t = BNamedType xt in
              (l, BFunDecl (xc + "_update__" + xf, [(x1, t, None); (x2, tf, None)], t, Some e, None, None)))
            fs in
        [(l, d)] @ (List.collect get cs) @ (List.collect update cs)
      )
    | BTypeDecl _ -> [(l, d)]
    | BFunDecl (x, fs, t, e_opt, attrs, ts_opt) ->
        let (fs, gmap) = rename_formal_funs fs gmap in
        let subst e = subst_exp gmap (subst_exp static_map e) in
        let e_opt = match e_opt with None -> None | Some e -> Some (subst e) in
        let ts_opt = match ts_opt with None -> None | Some ts -> Some (List.map (List.map subst) ts) in
        [(l, BFunDecl (x, fs, t, e_opt, attrs, ts_opt))]
    | BProcDecl (x, ps, rets, specs, None, p) ->
        let specs = List.map (map_spec (fun_defaults_exp env)) specs in
        let specs = List.map (subst_spec gmap) specs in
        [(l, BProcDecl (x, ps, rets, specs, None, p))]
    | BProcDecl (x, ps, rets, specs, Some b, p) ->
        let (_, (_, _, _, _, _, pk)) = env.proc_decls.[x] in
        let is_ghost = match pk with (Procedure (PGhost, _)) -> true | _ -> false in
        let b = map_block (fun_defaults_exp env) (fun s -> None) b in
        let specs = List.map (map_spec (fun_defaults_exp env)) specs in
        let (gps_rev, aps_rev) =
          List.fold_left
            (fun (gps, aps) (x, t, lin) ->
              match t with
              | BFormalType _ -> ((x, t, lin)::gps, aps)
              | BFormalAlias (BVar t) -> (gps, (x, t, lin)::aps)
              | _ -> err ("non-register alias not supported: " + x))
            ([], [])
            ps in
        let (gps, aps) = (List.rev gps_rev, List.rev aps_rev) in
        let m = new Map<id,bexp>(List.map (fun (xp, xa, _) -> (xp, BVar xa)) aps) in
        let specs = List.map (subst_spec m) specs in
        let b = subst_block m b in
        let locals = ref ([]:(id * (bformal_typ * linearity)) list) in
        let invs = match Map.tryFind x !extra_proc_invariants with None -> [] | Some invs -> invs in
        let b = subst_block static_map b in
        let b = aliases_block Map.empty Map.empty invs b in
        let b = compile_block env pk locals b in
        let b = if is_ghost then b else embellish_stmts env b in
        let bLocals = !locals in
        let bLocals = List.map (fun (x, (t, lin)) -> (l, BLocalDecl (x, t, lin, None))) bLocals in
        let mSpec = (l, BModifies (!modify)) in
        let specs = List.map (subst_spec gmap) specs in
        let b = subst_block gmap b in
        [(l, BProcDecl (x, gps, rets, mSpec::specs, Some (bLocals @ b), p))]
  ) with e -> raise (LocErr (l, e))

let compile_decls (env:env) (gmap:Map<id,bexp>) (static_map:Map<id,bexp>) ds =
  List.collect (compile_decl env gmap static_map (ref ([]:bexp list))) ds

(*****************************************************************************)

// REVIEW: compared to inout parameters, this is a bit of a hack (more like dynamic scope)
let expand_inout_decl (env:env) (l:loc, d:bdecl):(loc * bdecl) =
  //     procedure p() inout x:t; requires r(x); ensures e(x, old(...x...));
  // ==> procedure p(old__x) returns(x); requires r(old__x); ensures e(x, old(...old__x...));
  //     procedure p(inout x:t) requires r(x); ensures e(x, old(...x...));
  // ==> procedure p(old__x) returns(x); requires r(old__x); ensures e(x, old(...old__x...));
  try
  (
    let does_modify xp specs x =
         (match Map.tryFind xp !extra_proc_modifies with None -> false | Some xs -> List.mem x xs)
      || List.exists (fun (_, d) ->
            match d with
            | BModifies es -> List.exists (fun e -> e = BVar x) es
            | _ -> false)
          specs in
    match d with
    | BProcDecl (xp, ps, rets, specs, b_opt, pk) when Map_containsKey xp env.proc_decls ->
      (
        let old m x = if m then x + "__BEAT__old" else x in
        let (_, (_, _, _, pspecs, _, _)) = env.proc_decls.[xp] in
        let inouts = List.collect (fun (l, s) -> match s with BInOut io -> io | _ -> []) pspecs in
        let inouts_mod = List.map (fun (x, t, l) -> ((x, t, l), does_modify xp pspecs x)) inouts in
        let inouts_ret = List.choose (fun (f, m) -> if m then Some f else None) inouts_mod in
        let inouts_ps = List.map (fun ((x, t, lin), m) ->
          let lin = (match (m, lin) with (false, Lin (_, scope)) -> (Lin (LinConst, scope)) | _ -> lin) in
          (old m x, BFormalType t, lin)) inouts_mod in
        let ps_inouts = List.choose (fun (x, ft, l) ->
          match (l, ft) with (Lin (LinInOut, scope), BFormalType t) -> Some (x, t, Lin (LinVar, scope)) | _ -> None) ps in
        let ps_inouts_mod = List.map (fun p -> (p, true)) ps_inouts in
        let ps = List.map (fun (x, t, l) ->
          match l with Lin (LinInOut, scope) -> (old true x, t, Lin (LinVar, scope)) | _ -> (x, t, l)) ps in
        let ps = inouts_ps @ ps in
        let rets = inouts_ret @ ps_inouts @ rets in
        let oldMap = Map_ofList (List.map (fun ((x, _, _), m) -> (x, BVar (old m x))) (inouts_mod @ ps_inouts_mod)) in
        let fe = fun e ->
          match e with BUop (BOld, ee) -> Some (BUop (BOld, subst_exp oldMap ee)) | _ -> None in
        let fs = fun s ->
          match s with
          | BCall (rs, xc, args, pars) ->
              let io_rets = List.choose (fun ea -> match ea with BUop (BInOutOp, e) -> Some e | _ -> None) args in
              let rec fe_arg e = map_exp (fun ea -> match ea with BUop (BInOutOp, e) -> Some (fe_arg e) | _ -> None) e in
              let args = List.map fe_arg args in
              let rs = List.map fe_arg (io_rets @ rs) in
              let (rs, args) =
                if Map_containsKey xc env.proc_decls then
                  let (_, (_, _, _, c_specs, _, _)) = env.proc_decls.[xc] in
                  let c_inouts = List.collect (fun (_, s) -> match s with BInOut io -> io | _ -> []) c_specs in
                  let xs = List.map (fun (x, _, _) -> x) c_inouts in
                  let xs_ret = List.choose (fun (x, _, l) ->
                    if does_modify xc c_specs x then Some x else None) c_inouts in
                  let x2es = List.map (fun x -> BVar x) in
                  (((x2es xs_ret) @ rs), ((x2es xs) @ args))
                else
                  (rs, args)
                in
              Some
                (BCall
                  (List.map (map_exp fe) rs,
                  xc,
                  List.map (map_exp fe) args,
                  List.map (fun (x, es) -> (x, List.map (map_exp fe) es)) pars))
          | _ -> None
        let specs =
          List.collect (fun (l, d) ->
              match d with
              | BRequires e -> [(l, BRequires (subst_exp oldMap e))]
              | BEnsures e -> [(l, BEnsures (map_exp fe e))]
              | BModifies _ -> [(l, d)]
              | BInOut _ -> []
              )
            specs in
        let xinouts = List.map (fun (x, _, _) -> x) inouts in
        let fmod = List.filter (fun e -> match e with BVar x -> not (List.mem x xinouts) | _ -> true) in
        let specs = List.map (fun (l, d) ->
          (l, match d with BModifies xs -> BModifies (fmod xs) | _ -> d)) specs in
        let b_opt =
          match b_opt with
          | None -> None
          | Some b ->
              let rec f b =
                match b with
                | (l, ((BLocalDecl _) as s))::t -> (l, s)::(f t)
                | t -> (List.map (fun (x, _, _) -> (l, BAssign (BVar x, BVar (old true x)))) (inouts_ret @ ps_inouts)) @ t
                in
              Some (map_block (map_exp fe) fs (f b)) in
        // TODO: initialize x from old__x
        (l, BProcDecl (xp, ps, rets, specs, b_opt, pk))
      )
    | _ -> (l, d)
  ) with e -> raise (LocErr (l, e))

let expand_inout_decls (env:env) ds = List.map (expand_inout_decl env) ds

(*****************************************************************************)

let is_ghost_proc (env:env) (x:string):bool =
  match Map.tryFind x env.proc_decls with
  | Some (_, (_, _, _, _, _, Procedure (g, _))) -> g = PGhost
  | Some (_, (_, _, _, _, _, Instruction)) -> false
  | None when x.StartsWith("reveal_") -> true
  | _ -> err ("could not find declaration of procedure " + x)

let rec remove_ghost_stmt (env:env) (xs:id list ref) (l:loc, s) =
  let rs = remove_ghost_stmt env xs in
  let rb = remove_ghost_block env xs in
  match s with
  | BLocalDecl (x, BFormalType _, lin, _) -> []
  | BLocalDecl (x, BFormalAlias _, lin, _) -> xs := x::!xs; [(l, s)]
  | BLabel x -> [(l, s)]
  | BGoto x -> [(l, s)]
  | BAssign (BVar x, _) when List.mem x !xs -> [(l, s)]
  | BAssign (_, _) -> []
  | BGroup b -> rb b
  | BIf (e, b1, None) -> [(l, BIf (e, rb b1, None))]
  | BIf (e, b1, Some b2) -> [(l, BIf (e, rb b1, Some (rb b2)))]
  | BWhile (e, invs, b) -> [(l, BWhile (e, [], rb b))]
  | BForallGhost (fs, ts, e, b) -> []
  | BAssume e -> []
  | BAssert (e, inv) -> []
  | BSplit -> []
  | BYield e -> []
  | BHavoc e -> []
  | BCall (_, f, _, []) when f.StartsWith("construct##") -> []
  | BCall (_, f, _, []) when f.StartsWith("destruct##") -> []
  | BCall (_, f, _, _) -> if is_ghost_proc env f then [] else [(l, s)]
  | BReturn _ -> [(l, s)]
and remove_ghost_block (env:env) (xs:id list ref) b = List.collect (remove_ghost_stmt env xs) b

let remove_ghost_decl (env:env) (l:loc, d:bdecl):(loc * bdecl) list =
  try
  (
    match d with
    | BGlobalDecl _ -> []
    | BGlobalStaticDecl _ -> [(l, d)]
    | BStaticDecl _ -> [(l, d)]
    | BConstDecl _ -> []
    | BAxiomDecl _ -> []
    | BTypeDecl _ -> [(l, d)]
    | BFunDecl _ -> []
    | BProcDecl (x, fs, rs, _, b_opt, pk) ->
        if is_ghost_proc env x then [] else
        let xs = ref [] in
        let b_opt = match b_opt with None -> None | Some b -> Some (remove_ghost_block env xs b) in
        [(l, BProcDecl (x, fs, rs, [], b_opt, pk))]
  ) with e -> raise (LocErr (l, e))

let remove_ghost_decls (env:env) ds = List.collect (remove_ghost_decl env) ds

(*****************************************************************************)

let expand_depth = ref 0
let in_file = ref (None:string option)
let include_files = ref ([]:string list)

(* Each command-line argument is the name of a lemma *)
let args =
  [ 
    ("-expand"  , Arg.Int    (fun i -> expand_depth := i)  , "Expand formula definitions (for better error messages)")
    ("-i"       , Arg.String (fun s -> include_files := s::(!include_files)), "Include file")
    ("-in"      , Arg.String (fun s -> in_file := Some s), "Input file")
    ("-def"     , Arg.String (fun s -> Lex.macros := Map.add s [] !Lex.macros), "Define a macro (as an empty string) for use by ifdef/ifndef")
    ("-printAndExit", Arg.Set print_and_exit, "Pretty-print the input file and then exit")
    ("-printNonghostAndExit", Arg.Set print_nonghost_and_exit, "Pretty-print the input file, omitting ghost code, and then exit")
  ]

let main (argv) =
  let print_error_loc (file, line) = print_endline ("error near line " + (string line) + " of file " + file) in
  let print_error_prefix () = print_error_loc (!file, !line) in
  let rec print_error e =
    match e with
    | LocErr (l, e) -> print_error_loc l; print_error e
    | Err s -> (print_endline "error:"; print_endline s; exit 1)
    | ParseErr x -> (print_error_prefix (); print_endline x; exit 1)
    | :? System.ArgumentException as x -> (print_error_prefix (); print_endline (x.ToString ()); exit 1)
    | Failure x -> (print_error_prefix (); print_endline x; exit 1)
    | x -> (print_endline (x.ToString ()); exit 1)
  try
  (
    let cmd_args = System.Environment.GetCommandLineArgs () in
    Arg.parse_argv (ref 0) cmd_args args (fun _ -> ()) "error parsing arguments";

    let lex_token = Lex.get_token Lex.token in
    let parse_file name =
      file := name;
      line := 1;
      Parse.start lex_token (Lexing.from_channel (open_in name)) in
    let includes = List.map parse_file (List.rev !include_files) in
    let includes = List.map (fun m -> m.mDecls) includes in

    let {mName = mName; mIsImpl = isImpl; mImports = imports; mModifies = modifies; mYields = yields; mDecls = p} =
      match !in_file with
      | None ->
        (
          file := "";
          line := 1;
          Parse.start lex_token (Lexing.from_channel stdin)
        )
      | Some name ->
        (
          file := name;
          line := 1;
          Parse.start lex_token (Lexing.from_channel (open_in name))
        ) in

    let includes2 = List.flatten includes in

    if (!print_and_exit || !print_nonghost_and_exit) then
        let env = build_env (includes2 @ p) in
        let p = if !print_nonghost_and_exit then remove_ghost_decls env p else p in
        print_module
          { print_out = System.Console.Out; indent = ""; cur_loc = ref ("", 1); }
          {mName = mName; mIsImpl = isImpl; mImports = imports; mModifies = modifies; mYields = yields; mDecls = p};
      else

    let includes2 = expand_opaque_decls includes2 in
    let env = build_env (includes2 @ p) in
    let gmap = ghost_subst_map (includes2 @ p) in
    let static_map = static_subst_map (includes2 @ p) in
    let (senv, cenv) = summary_env (List.map snd (includes2 @ p)) in
    let p = expand_this_decls cenv p in
    let p = expand_conjuncts_decls env 0 p in
    let _ = List.map (fun (l, d) ->
      try (l, expand_overload_decl env senv cenv gmap d) with e -> raise (LocErr (l, e))) includes2 in
    let p = List.map (fun (l, d) ->
      try (l, expand_overload_decl env senv cenv gmap d) with e -> raise (LocErr (l, e))) p in
    let p = compile_decls env gmap static_map p in
    let p = expand_opaque_decls p in
    let p = expand_inout_decls env p in
    let p = List.filter (fun (_, d) -> match d with BProcDecl (_, _, _, _, _, Instruction) -> false | _ -> true) p in
    print_module
      { print_out = System.Console.Out; indent = ""; cur_loc = ref ("", 1); }
      {mName = mName; mIsImpl = isImpl; mImports = imports; mModifies = modifies; mYields = yields; mDecls = p};
    ()
    (*    print_program inlines p; *)
  )
  with e -> print_error e
;;

let () = main (System.Environment.GetCommandLineArgs ())


