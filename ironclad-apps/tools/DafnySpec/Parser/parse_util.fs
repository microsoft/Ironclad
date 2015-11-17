open System.Collections.Generic;
open Microsoft.Boogie
open Microsoft.Dafny

type loc = Token
exception Err of string
exception ParseErr of string
let err (s:string):'a = raise (Err s)
let parse_err (s:string):'a = raise (ParseErr s)
let assrt b = if b then () else err "assert failure"
let line = ref 1;;
let file = ref "";;
let parse_require b = if b then () else parse_err "parse requirement violated"
let toList (l:'a list):List<'a> = Program.MakeList(l :> IEnumerable<'a>)
