#light
module MakeBeat

open Def

let env = Def.env.Cd @"tools\beat"

let obj = Def.obj +/ @"beat"
let bin = Def.bin +/ @"beat"

env.Dep "all" <| [bin+/"beat.exe"] <| fun () -> ()
env.Dep obj <| [] <| fun () -> env.Mkdir obj
env.Dep bin <| [] <| fun () -> env.Mkdir bin

env.Fslex (obj+/"lex.fs") [obj] [] ["lex.fsl"]
env.Fsyacc (obj+/"parse.fs") [obj] [] ["parse.fsy"]
env.Fsc (bin+/"beat.exe") [bin]
  (split "--standalone --mlcompatibility -O -r FSharp.PowerPack.dll")
  ["ast.fs"; "parse_util.fs"; obj+/"parse.fs"; obj+/"lex.fs"; "main.fs"]

