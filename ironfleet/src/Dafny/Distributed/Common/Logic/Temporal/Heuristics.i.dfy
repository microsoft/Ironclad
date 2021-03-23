include "Temporal.s.dfy"
include "../../Collections/Maps2.i.dfy"

module Temporal__Heuristics_i {
import opened Temporal__Temporal_s
import opened Collections__Maps2_i

////////////////////
// DEFINITIONS
////////////////////

function TBlast(i:int):bool { true }

////////////////////
// LEMMAS
////////////////////
    
// Conservative heuristics; not complete
// (e.g. won't prove <>[]A ==> []<>A)
lemma TemporalAssist()
  ensures  forall i:int, x:temporal {:trigger sat(i, always(x))} :: sat(i, always(x))
             == (forall j:int :: TLe(i, j) ==> sat(j, x))
  ensures  forall i:int, x:temporal {:trigger sat(i, eventual(x))} :: sat(i, eventual(x))
              == (exists j:int :: TLe(i, j) && sat(j, x))
  ensures  TLe(0, 0)
{
  forall i:int, x:temporal {:trigger sat(i, always(x))}
    ensures sat(i, always(x)) == (forall j:int :: TLe(i, j) ==> sat(j, x))
  {
    reveal always();
    var f := imap ii{:trigger sat(ii, always(x))} :: forall j {:trigger sat(j, x)} :: ii <= j ==> sat(j, x);
    calc {
      sat(i, always(x));
      sat(i, stepmap(f));
      f[i];
    }
  }

  forall i:int, x:temporal {:trigger sat(i, eventual(x))}
    ensures sat(i, eventual(x)) == (exists j:int :: TLe(i, j) && sat(j, x))
  {
    reveal eventual();
  }
}

// Moderately aggressive heuristics
lemma TemporalBlast()
  ensures  forall i:int, x:temporal {:trigger sat(i, always(x))} :: sat(i, always(x))
              == (forall j:int :: TLe(i, j) ==> sat(j, x))
  ensures  forall i:int, x:temporal {:trigger sat(i, eventual(x))} :: sat(i, eventual(x))
              == (exists j:int :: TLe(i, j) && sat(j, x))
  ensures  forall i:int, j1:int, j2:int {:trigger TLe(i, j1), TLe(i, j2)} :: TLe(j1, j2) || TLe(j2, j1)
  ensures  TLe(0, 0)
{
  forall i:int, x:temporal {:trigger sat(i, always(x))}
    ensures sat(i, always(x)) == (forall j:int :: TLe(i, j) ==> sat(j, x))
  {
    reveal always();
    var f := imap ii{:trigger sat(ii, always(x))} :: forall j {:trigger sat(j, x)} :: ii <= j ==> sat(j, x);
    calc {
      sat(i, always(x));
      sat(i, stepmap(f));
      f[i];
    }
  }

  forall i:int, x:temporal {:trigger sat(i, eventual(x))}
    ensures sat(i, eventual(x)) == (exists j:int :: TLe(i, j) && sat(j, x))
  {
    reveal eventual();
  }
}
    
// Most aggressive heuristics; might not terminate
// (e.g. won't terminate on invalid formula <>[](A || B) ==> <>[]A || <>[]B)
lemma TemporalFullBlast()
  ensures  forall i:int, x:temporal {:trigger sat(i, always(x))} :: sat(i, always(x))
              == (forall j:int {:trigger sat(j, x)}{:trigger TBlast(j)} :: TBlast(j) ==> i <= j ==> sat(j, x))
  ensures  forall i:int, x:temporal {:trigger sat(i, eventual(x))} :: sat(i, eventual(x))
              == (exists j:int {:trigger sat(j, x)}{:trigger TBlast(j)} :: TBlast(j) && i <= j && sat(j, x))
  ensures  TBlast(0)
{
  forall i:int, x:temporal {:trigger sat(i, always(x))}
    ensures sat(i, always(x)) == (forall j:int :: TLe(i, j) ==> sat(j, x))
  {
    reveal always();
    var f := imap ii{:trigger sat(ii, always(x))} :: forall j {:trigger sat(j, x)} :: ii <= j ==> sat(j, x);
    calc {
      sat(i, always(x));
      sat(i, stepmap(f));
      f[i];
    }
  }

  forall i:int, x:temporal {:trigger sat(i, eventual(x))}
    ensures sat(i, eventual(x)) == (exists j:int :: TLe(i, j) && sat(j, x))
  {
    reveal eventual();
  }
}

} 
