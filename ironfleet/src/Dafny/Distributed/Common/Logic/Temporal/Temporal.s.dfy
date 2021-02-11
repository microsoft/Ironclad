include "../../Collections/Maps2.s.dfy"

module Temporal__Temporal_s {
import opened Collections__Maps2_s

// TODO_MODULE: module Logic__Temporal_s {
// TODO_MODULE: import opened Collections__Maps2_s

//// TODO_MODULE: module TemporalLogic
//{

type temporal = imap<int, bool>
type Behavior<S> = imap<int, S>
    
function stepmap(f:imap<int, bool>):temporal
  ensures  forall i:int :: i in f ==> sat(i, stepmap(f)) == f[i]
{
  f
}

predicate sat(s:int, t:temporal)
{
  s in t && t[s]
}

function{:opaque} and(x:temporal, y:temporal):temporal
  ensures  forall i:int {:trigger sat(i, and(x, y))} :: sat(i, and(x, y)) == (sat(i, x) && sat(i, y))
{
  stepmap(imap i :: sat(i, x) && sat(i, y))
}

function{:opaque} or(x:temporal, y:temporal):temporal
  ensures  forall i:int {:trigger sat(i, or(x, y))} :: sat(i, or(x, y)) == (sat(i, x) || sat(i, y))
{
  stepmap(imap i :: sat(i, x) || sat(i, y))
}

function{:opaque} imply(x:temporal, y:temporal):temporal
  ensures  forall i:int {:trigger sat(i, imply(x, y))} :: sat(i, imply(x, y)) == (sat(i, x) ==> sat(i, y))
{
  stepmap(imap i :: sat(i, x) ==> sat(i, y))
}

function{:opaque} equiv(x:temporal, y:temporal):temporal
  ensures  forall i:int {:trigger sat(i, equiv(x, y))} :: sat(i, equiv(x, y)) == (sat(i, x) <==> sat(i, y))
{
  stepmap(imap i :: sat(i, x) <==> sat(i, y))
}

function{:opaque} not(x:temporal):temporal
  ensures  forall i:int {:trigger sat(i, not(x))} :: sat(i, not(x)) == !sat(i, x)
{
  stepmap(imap i :: !sat(i, x))
}

function nextstep(i:int):int
{
  i+1
}

function{:opaque} next(x:temporal):temporal
  ensures  forall i:int {:trigger sat(i, next(x))} :: sat(i, next(x)) == sat(nextstep(i), x)
{
  stepmap(imap i :: sat(nextstep(i), x))
}

function{:opaque} always(x:temporal):temporal
{
  stepmap(imap i {:trigger sat(i, always(x))} :: forall j {:trigger sat(j, x)} :: i <= j ==> sat(j, x))
}

function{:opaque} eventual(x:temporal):temporal
{
  stepmap(imap i {:trigger sat(i, eventual(x))} :: exists j :: i <= j && sat(j, x))
}

//}

// TODO_MODULE: } import opened Logic__Temporal_s_ = Logic__Temporal_s

} 
