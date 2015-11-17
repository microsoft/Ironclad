exception Err of string
exception ParseErr of string
let err (s:string):'a = raise (Err s)
let parse_err (s:string):'a = raise (ParseErr s)
let assrt b = if b then () else err "assert failure"
let line = ref 1;;
let file = ref "";;
let count = ref 0;;
let content_on_line = ref false;
let parse_require b = if b then () else parse_err "parse requirement violated"

let end_line () =
  if (!content_on_line) then incr count;
  content_on_line := false

type token = EOF
