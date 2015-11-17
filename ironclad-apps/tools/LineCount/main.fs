open Parse_util

let main (argv) =
  let total = ref 0;
  let mods_rev = ref ([]:string list) in
  let add_mod (s:string) = mods_rev := s::(!mods_rev) in 
  Arg.parse_argv (ref 0) argv
    [
    ]
    add_mod
    "error parsing arguments";
  let mods = List.rev (!mods_rev) in
  let parse_file name =
    file := name;
    line := 1;
    count := 0;
    let lexbuf = (Lexing.from_channel (open_in name));
    let _ = Lex.token lexbuf in
    print_endline (string (!count) ^ " " ^ name);
    total := !total + !count
  List.iter parse_file mods;
  print_endline (string (!total));
;;

let () = main (System.Environment.GetCommandLineArgs ())

