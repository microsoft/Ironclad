" Vim syntax file
" Language:     Beat
" Maintainer:   Bryan Parno
" Last Change:  April 2, 2013
" Version:      1

" Use the following lines in your .vimrc file to make use of this file:
"  " Syntax coloring for Beat/Boogie
"  au BufRead,BufNewFile *.beat set filetype=beat
"  au BufRead,BufNewFile *.bpl  set filetype=beat
"  "au! Syntax beat source $VIM/beat.vim


if exists("b:current_syntax")  
  finish
endif

syn case match

syn keyword bDecl         function procedure implementation atomic module returns instruction
syn keyword bCond         if then else
syn keyword bRepeat       while 
syn keyword bPreReqs      requires invariant
syn keyword bProof        ensures modifies assert 
syn keyword bCommentTodo  TODO REVIEW contained
syn keyword bConst        const type linear var


syn match   bLineComment      "\/\/.*" contains=@Spell,bCommentTodo
syn region  bComment	       start="/\*"  end="\*/" contains=@Spell,bCommentTodo
syn match   bNumber        "-\=\<\d\+L\=\>\|0[xX][0-9a-fA-F]\+\>"
syn match   bType          ":[a-zA-Z_[\]]\+[0-9a-zA-Z_[\]]\+"
syn match   bTrigger       "::\(\_[\t ]*{.\{-}}\)\+"

hi def link bDecl        PreCondit
hi def link bCond        Conditional
hi def link bRepeat      Repeat
hi def link bProof       Macro
hi def link bType        Type
hi def link bComment     Comment
hi def link bLineComment Comment
hi def link bCommentTodo Todo
hi def link bConst       Keyword
hi def link bNumber      Number
hi def link bTrigger     Debug
hi def link bPreReqs     Underlined

let b:current_syntax = "beat"
