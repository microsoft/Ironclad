#light
module MakeBoogieAsm

open Def

let env = Def.env.Cd @"tools\boogieasm"

let obj = Def.obj +/ @"boogieasm"
let bin = Def.bin +/ @"boogieasm"

env.Dep "all" <| [bin+/"boogieasm.exe"] <| fun () -> ()
env.Dep obj <| [] <| fun () -> env.Mkdir obj
env.Dep bin <| [] <| fun () -> env.Mkdir bin

env.Fslex (obj+/"lex.fs") [obj] [] ["lex.fsl"]
env.Fsyacc (obj+/"parse.fs") [obj] [] ["parse.fsy"]
env.Fsc (bin+/"boogieasm.exe") [bin]
  (split "--standalone --mlcompatibility -O -r FSharp.PowerPack.dll")
  ["ast.fs"; "parse_util.fs"; obj+/"parse.fs"; obj+/"lex.fs"; "main.fs"]

