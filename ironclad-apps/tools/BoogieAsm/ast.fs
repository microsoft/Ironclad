open Microsoft.FSharp.Math

type loc = string * int

type reg = string
type id = string
type attr = string

type typ =
| TInt
| TBool
| TReal
| TName of id
| TMap of typ * typ

type lin_const = LinConst | LinVar
type lin_scope = LinMy | LinOur
type linearity = Lin of lin_const * lin_scope | Non
type formal = id * typ
type pformal = id * typ * linearity

type op =
| Bop of string
| Uop of string
| Subscript
| Update
| Cond

type quant = Forall | Exists | Lambda

type exp =
| EVar of id
| EInt of bigint
| EReal of string
| EBv32 of bigint
| EBool of bool
| EOp of op * exp list
| EApply of id * exp list
| EQuant of quant * formal list * exp list list * exp

let eAdd (e1:exp) (e2:exp):exp = EOp (Bop "+", [e1; e2])
let eMul (e1:exp) (e2:exp):exp = EOp (Bop "*", [e1; e2])

type is_relation = IsRel | NotRel
type is_invariant = IsInv of is_relation | NotInv
type par_call = id * exp list
type stmt =
| SLabel of id
| SGoto of id
| SReturn
| SIReturn
| SYield of exp
| SAssert of is_invariant * exp
| SSplit
| SAssign of id * exp
| SIfJcc of id * id * id
| SGroup of (loc * stmt) list
| SIfGhost of exp * (loc * stmt) list
| SForallGhost of formal list * exp list list * exp * formal list * (loc * stmt) list
| SExistsGhost of formal list * exp list list * exp
| SInline of id list * id * exp list * par_call list
| SCall of id list * id * exp list

type spec =
| Requires of is_relation * exp
| Ensures of is_relation * exp
| Modifies of id list
type proc_atomicity = Atomic | Yields | Stable
type proc_ghost = PGhost | PReal
type proc_kind = Procedure of proc_ghost * proc_atomicity | Implementation
type inline_kind = Outline | Inline
type fun_decl = id * formal list option * typ option * exp option * attr option * exp list list option
type proc_decl = id * proc_kind * inline_kind * pformal list * pformal list * (loc * spec) list * (pformal list * (loc * stmt) list) option

type readwrite = Readonly | ReadWrite
type decl =
| DType of id * bool * bool * (linearity * id * pformal list) list option
| DStatic of id
| DStaticGhost of id * typ * linearity * readwrite
| DFunDecl of fun_decl
| DProc of proc_decl

type _module = {mName:id; mIsImpl:bool; mModifies:id list; mYields:id list; mDecls:(loc * decl) list}

