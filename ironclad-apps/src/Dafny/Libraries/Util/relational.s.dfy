//-//////////////////////////////////////////
//-  Relational interface used by SymDiff
//-//////////////////////////////////////////

//- Dummy functions that are translated into BoogieAsm keywords:
static function left<t>(x:t) : t { x }
static function right<t>(x:t) : t { x }
static predicate relation<t>(x:t) { true }
static predicate public<t>(x:t) { true }

//- Imported functions:
static predicate{:imported} declassified(lg:int, rg:int, l:int, r:int)
