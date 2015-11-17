type id = string
type loc = string * int
type bigint = Microsoft.FSharp.Math.bigint

type btyp =
| BInt | BBool | BReal
| BArray of btyp list * btyp
| BNamedType of id

type field_op = BFieldNative | BFieldFun | BFieldDotFun

type buop = 
| BNot | BNeg | BOld | BInOutOp
| BField of string * (string * string * field_op) option
| BIs of string

type bbop =
| BEquiv | BImply | BAnd | BOr
| BEq | BNe | BLt | BGt | BLe | BGe
| BAdd | BSub | BMul | BDiv | BMod | BRealDiv
| BAddChecked | BSubChecked
| BFieldUpdate of string * string option

type bquant =
| BForall | BExists | BLambda

type lin_const = LinConst | LinVar | LinInOut
type lin_scope = LinMy | LinOur
type linearity = Lin of lin_const * lin_scope | Non
type bformal = id * btyp
type bpformal = id * btyp * linearity

type bexp =
| BLoc of loc * bexp
| BVar of id
| BIntConst of bigint
| BRealConst of string
| BBv32 of bigint
| BBoolConst of bool
| BUop of buop * bexp
| BBop of bbop * bexp * bexp
| BQuant of bquant * bformal list * bexp list list * bexp
| BSubscript of bexp * bexp list
| BUpdate of bexp * bexp list * bexp
| BApply of id * bexp list
| BCond of bexp * bexp * bexp

type bformal_typ =
| BFormalType of btyp
| BFormalAlias of bexp

type bformal_var = id * bformal_typ * linearity
type bformal_fun = id * btyp * bexp option

type ret_kind = BRet | BIRet | BEmbellishRet

type par_call = id * bexp list
type bstmt =
| BLocalDecl of id * bformal_typ * linearity * bexp option
| BLabel of id
| BGoto of id
| BAssign of bexp * bexp
| BGroup of bblock
| BIf of bexp * bblock * bblock option
| BWhile of bexp * (loc * bexp) list * bblock
| BForallGhost of bformal list * bexp list list * bexp * bblock
| BAssume of bexp
| BAssert of bexp * bool
| BSplit
| BYield of bexp
| BHavoc of bexp
| BCall of bexp list * id * bexp list * par_call list
| BReturn of ret_kind
and bblock = (loc * bstmt) list

type bspec =
| BRequires of bexp
| BEnsures of bexp
| BModifies of bexp list
| BInOut of bpformal list

type proc_atomicity = Atomic | Yields | Stable
type proc_ghost = PGhost | PReal
type proc_kind = Procedure of proc_ghost * proc_atomicity | Implementation | Instruction

type battr = string

type fun_decl = id * bformal_fun list * btyp * bexp option * battr option * bexp list list option
type proc_decl = id * bformal_var list * bpformal list * (loc * bspec) list * bblock option * proc_kind

type readwrite = Readonly | ReadWrite
type bdecl =
| BGlobalDecl of id * btyp * linearity * readwrite
| BGlobalStaticDecl of id * id
| BStaticDecl of id
| BConstDecl of id * btyp * bexp option
| BAxiomDecl of bexp
| BTypeDecl of id * (id list * (linearity * id * bpformal list) list) option
| BFunDecl of fun_decl
| BProcDecl of proc_decl

type bdecls = (loc * bdecl) list
type _module = {mName:id; mIsImpl:bool; mImports:id list; mModifies:id list; mYields:id list; mDecls:(loc * bdecl) list}

