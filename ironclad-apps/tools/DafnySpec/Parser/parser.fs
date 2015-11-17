open Parse
open Parse_util
open System.Collections.Generic;
open Microsoft.Dafny

let parse (filename:string):List<TopLevelDecl> =
  let print_error_prefix () = print_endline ("error near line " + (string !line) + " of file " + !file) in
  try
  (
    file := filename;
    line := 1;
    toList (Parse.start Lex.token (Lexing.from_channel (open_in filename)))
  )
  with
     | (Err s) as x -> (print_endline "error:"; print_endline s; print_endline (x.ToString ()); exit 1)
     | ParseErr x -> (print_error_prefix (); print_endline x; exit 1)
     | :? System.ArgumentException as x -> (print_error_prefix (); print_endline (x.ToString ()); exit 1)
     | Failure x -> (print_error_prefix (); print_endline x; exit 1)
     | x -> (print_endline (x.ToString ()); exit 1)
;;


