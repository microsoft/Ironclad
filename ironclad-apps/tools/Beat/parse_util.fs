open Ast;;

exception Err of string
exception ParseErr of string
let err (s:string):'a = raise (Err s)
let parse_err (s:string):'a = raise (ParseErr s)
let file = ref "";;
let line = ref 1;;
