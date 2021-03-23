include "Heuristics.i.dfy"
include "Rules.i.dfy"
include "Time.s.dfy"
include "LeadsTo.i.dfy"
include "../../Collections/Sets.i.dfy"

module Temporal__Sets_i {
import opened Temporal__Heuristics_i
import opened Temporal__Rules_i
import opened Temporal__Time_s
import opened Temporal__LeadsTo_i
import opened Temporal__Temporal_s
import opened Collections__Maps2_s
import opened Collections__Maps2_i
import opened Collections__Sets_i

/////////////////////////
// DEFINITIONS
/////////////////////////

function{:opaque} andset(xs:set<temporal>):temporal
  ensures  forall i{:trigger sat(i, andset(xs))} :: sat(i, andset(xs)) <==> (forall x :: x in xs ==> sat(i, x))
{
  stepmap(imap i{:trigger sat(i, andset(xs))} :: (forall x :: x in xs ==> sat(i, x)))
}

function{:opaque} orset(xs:set<temporal>):temporal
  ensures  forall i{:trigger sat(i, orset(xs))} :: sat(i, orset(xs)) <==> (exists x :: x in xs && sat(i, x))
{
  stepmap(imap i{:trigger sat(i, orset(xs))} :: (exists x :: x in xs && sat(i, x)))
}

/////////////////////////
// LEMMAS
/////////////////////////

lemma Lemma_EventuallyAlwaysEachImpliesEventuallyAlwaysAll(
  i:int,
  xs:set<temporal>
  )
  requires forall x :: x in xs ==> sat(i, eventual(always(x)))
  ensures  sat(i, eventual(always(andset(xs))))
  decreases |xs|
{
  TemporalAssist();

  if |xs| == 0
  {
    assert sat(i, always(andset(xs)));
  }
  else
  {
    var x :| x in xs;
    var xs' := xs - {x};
    Lemma_EventuallyAlwaysEachImpliesEventuallyAlwaysAll(i, xs');
    var j := eventualStep(i, always(andset(xs')));
    var k := eventualStep(i, always(x));
    var m := if j > k then j else k;
    Lemma_AlwaysImpliesLaterAlways(j, m, andset(xs'));
    Lemma_AlwaysImpliesLaterAlways(k, m, x);
    reveal andset();
    assert sat(m, always(andset(xs)));
  }
}

lemma Lemma_EventuallyAlwaysWithinEachImpliesEventuallyAlwaysWithinAll(
  i:int,
  xs:set<temporal>,
  span:int,
  timefun:imap<int, int>
  )
  requires imaptotal(timefun)
  requires span >= 0 || |xs| > 0
  requires forall x :: x in xs ==> sat(i, eventuallywithin(always(x), span, timefun))
  ensures  sat(i, eventuallywithin(always(andset(xs)), span, timefun))
  decreases |xs|
{
  TemporalAssist();
  
  if |xs| == 0
  {
    assert sat(i, always(andset(xs)));
    assert sat(i, beforeabsolutetime(always(andset(xs)), timefun[i] + span, timefun));
  }
  else
  {
    var x :| x in xs;
    if |xs| == 1
    {
      var j := eventualStep(i, beforeabsolutetime(always(x), timefun[i] + span, timefun));
      assert sat(j, beforeabsolutetime(always(x), timefun[i] + span, timefun));
      forall k | TLe(j, k)
        ensures sat(k, imply(x, andset(xs)))
      {
        forall x' | x' in xs
          ensures x' == x
        {
          ThingsIKnowAboutASingletonSet(xs, x, x');
        }
        reveal andset();
      }
      assert sat(j, beforeabsolutetime(always(andset(xs)), timefun[i] + span, timefun));
    }
    else
    {
      var xs' := xs - {x};
      Lemma_EventuallyAlwaysWithinEachImpliesEventuallyAlwaysWithinAll(i, xs', span, timefun);
      var j := eventualStep(i, beforeabsolutetime(always(andset(xs')), timefun[i] + span, timefun));
      var k := eventualStep(i, beforeabsolutetime(always(x), timefun[i] + span, timefun));
      var m := if j > k then j else k;
      Lemma_AlwaysImpliesLaterAlways(j, m, andset(xs'));
      Lemma_AlwaysImpliesLaterAlways(k, m, x);
      forall ensures sat(m, always(imply(and(andset(xs'), x), andset(xs))))
      {
        assert forall x' :: x' in xs ==> x' in xs' || x' in {x};
        reveal andset();
      }
      assert sat(m, always(andset(xs)));
    }
  }
}

lemma Lemma_LeadsToAlwaysEachWithinImpliesLeadsToAlwaysAllWithin(
  i:int,
  x:temporal,
  ys:set<temporal>,
  span:int,
  timefun:imap<int, int>
  )
  requires imaptotal(timefun)
  requires span >= 0 || |ys| > 0
  requires forall y :: y in ys ==> sat(i, leadstowithin(x, always(y), span, timefun))
  ensures  sat(i, leadstowithin(x, always(andset(ys)), span, timefun))
{
  TemporalAssist();

  forall j | TLe(i, j)
    ensures sat(j, imply(x, eventuallywithin(always(andset(ys)), span, timefun)))
  {
    if sat(j, x)
    {
      Lemma_EventuallyAlwaysWithinEachImpliesEventuallyAlwaysWithinAll(j, ys, span, timefun);
    }
  }
}

lemma Lemma_EventuallyAlwaysWithinEachOrAlternativeImpliesEventuallyAlwaysWithinAllOrAlternative(
  i:int,
  xs:set<temporal>,
  y:temporal,
  span:int,
  timefun:imap<int, int>
  )
  requires imaptotal(timefun)
  requires span >= 0 || |xs| > 0
  requires forall x :: x in xs ==> sat(i, eventuallywithin(or(always(x), y), span, timefun))
  ensures  sat(i, eventuallywithin(or(always(andset(xs)), y), span, timefun))
  decreases |xs|
{
  TemporalAssist();

  if |xs| == 0
  {
    assert sat(i, or(always(andset(xs)), y));
    assert sat(i, beforeabsolutetime(or(always(andset(xs)), y), timefun[i] + span, timefun));
  }
  else
  {
    var x :| x in xs;
    if |xs| == 1
    {
      var j := eventualStep(i, beforeabsolutetime(or(always(x), y), timefun[i] + span, timefun));
      forall k | TLe(j, k)
        ensures sat(k, imply(x, andset(xs)))
      {
        forall x' | x' in xs
          ensures x' == x
        {
          ThingsIKnowAboutASingletonSet(xs, x, x');
        }
        reveal andset();
      }
      assert sat(j, beforeabsolutetime(or(always(andset(xs)), y), timefun[i] + span, timefun));
    }
    else
    {
      var xs' := xs - {x};
      Lemma_EventuallyAlwaysWithinEachOrAlternativeImpliesEventuallyAlwaysWithinAllOrAlternative(i, xs', y, span, timefun);
      var j := eventualStep(i, beforeabsolutetime(or(always(andset(xs')), y), timefun[i] + span, timefun));
      var k := eventualStep(i, beforeabsolutetime(or(always(x), y), timefun[i] + span, timefun));
      if sat(j, y)
      {
        assert sat(j, or(always(andset(xs)), y));
      }
      else if sat(k, y)
      {
        assert sat(k, or(always(andset(xs)), y));
      }
      else
      {
        var m := if j > k then j else k;
        Lemma_AlwaysImpliesLaterAlways(j, m, andset(xs'));
        Lemma_AlwaysImpliesLaterAlways(k, m, x);
        forall ensures sat(m, always(imply(and(andset(xs'), x), andset(xs))))
        {
          assert forall x' :: x' in xs ==> x' in xs' || x' in {x};
          reveal andset();
        }
        assert sat(m, or(always(andset(xs)), y));
      }
    }
  }
}

lemma Lemma_LeadsToAlwaysEachOrAlternativeWithinImpliesLeadsToAlwaysAllOrAlternativeWithin(
  i:int,
  x:temporal,
  ys:set<temporal>,
  z:temporal,
  span:int,
  timefun:imap<int, int>
  )
  requires imaptotal(timefun)
  requires span >= 0 || |ys| > 0
  requires forall y :: y in ys ==> sat(i, leadstowithin(x, or(always(y), z), span, timefun))
  ensures  sat(i, leadstowithin(x, or(always(andset(ys)), z), span, timefun))
{
  TemporalAssist();

  forall j | TLe(i, j)
    ensures sat(j, imply(x, eventuallywithin(or(always(andset(ys)), z), span, timefun)))
  {
    if sat(j, x)
    {
      Lemma_EventuallyAlwaysWithinEachOrAlternativeImpliesEventuallyAlwaysWithinAllOrAlternative(j, ys, z, span, timefun);
    }
  }
}

} 
