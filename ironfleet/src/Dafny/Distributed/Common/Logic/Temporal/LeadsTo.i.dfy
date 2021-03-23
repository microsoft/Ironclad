include "Heuristics.i.dfy"
include "Rules.i.dfy"
include "Time.i.dfy"
include "../../../../Libraries/Math/mul.i.dfy"

module Temporal__LeadsTo_i {
import opened Temporal__Temporal_s
import opened Temporal__Heuristics_i
import opened Temporal__Rules_i
import opened Temporal__Time_s
import opened Temporal__Time_i
import opened Collections__Maps2_s
import opened Collections__Maps2_i
import opened Math__mul_i

//////////////////
// DEFINITIONS
//////////////////

function leadsto(x:temporal, y:temporal):temporal
{
  always(imply(x, eventual(y)))
}

function leadstowithin(x:temporal, y:temporal, t:int, timefun:imap<int, int>):temporal
  requires imaptotal(timefun)
{
  always(imply(x, eventuallywithin(y, t, timefun)))
}

function leadstonextwithin(x:temporal, action:temporal, t:int, timefun:imap<int, int>):temporal
  requires imaptotal(timefun)
{
  always(imply(x, eventuallynextwithin(action, t, timefun)))
}

function leadstonextwithinnext(x:temporal, action:temporal, t:int, timefun:imap<int, int>):temporal
  requires imaptotal(timefun)
{
  always(imply(x, next(eventuallynextwithin(action, t, timefun))))
}

//////////////////
// LEMMAS
//////////////////

lemma TransitivityOfLeadsTo(i:int, x:temporal, y:temporal, z:temporal)
  requires sat(i, leadsto(x, y))
  requires sat(i, leadsto(y, z))
  ensures  sat(i, leadsto(x, z))
{
  forall j | TLe(i, j)
    ensures sat(j, imply(x, eventual(z)))
  {
    if sat(j, x) {
      TemporalDeduceFromAlways(i, j, imply(x, eventual(y)));
      var k := TemporalDeduceFromEventual(j, y);
      TemporalDeduceFromAlways(i, k, imply(y, eventual(z)));
      var m := TemporalDeduceFromEventual(k, z);
      TemporalEventually(j, m, z);
    }
  }
  TemporalAlways(i, imply(x, eventual(z)));
}

lemma TransitivityOfLeadsToGeneral()
  ensures  forall i:int, x:temporal, y:temporal, z:temporal :: sat(i, leadsto(x, y)) && sat(i, leadsto(y, z)) ==> sat(i, leadsto(x, z))
{
  forall i:int, x:temporal, y:temporal, z:temporal | sat(i, leadsto(x, y)) && sat(i, leadsto(y, z))
  {
    TransitivityOfLeadsTo(i, x, y, z);
  }
}

lemma TransitivityOfLeadsToWithin(i:int, x:temporal, y:temporal, z:temporal, t1:int, t2:int, timefun:imap<int, int>)
  requires imaptotal(timefun)
  requires sat(i, leadstowithin(x, y, t1, timefun))
  requires sat(i, leadstowithin(y, z, t2, timefun))
  ensures  sat(i, leadstowithin(x, z, t1 + t2, timefun))
{
  TemporalAssist();

  forall j | TLe(i, j) && sat(j, x)
    ensures sat(j, eventuallywithin(z, t1 + t2, timefun))
  {
    assert sat(j, eventuallywithin(y, t1, timefun));
    assert sat(j, eventual(beforeabsolutetime(y, timefun[j] + t1, timefun)));
    var k :| TLe(j, k) && sat(k, beforeabsolutetime(y, timefun[j] + t1, timefun));
    assert TLe(i, k);
    assert sat(k, eventuallywithin(z, t2, timefun));
    assert sat(k, eventual(beforeabsolutetime(z, timefun[j] + t1 + t2, timefun)));
    var l :| TLe(k, l) && sat(l, beforeabsolutetime(z, timefun[j] + t1 + t2, timefun));
    assert TLe(j, l);
    assert sat(j, eventuallywithin(z, t1 + t2, timefun));
  }
}

lemma LeadsToDistributesOverOr(i:int, x:temporal, y:temporal, z:temporal)
  requires sat(i, leadsto(x, z))
  requires sat(i, leadsto(y, z))
  ensures  sat(i, leadsto(or(x, y), z))
{
  TemporalAssist();
}

lemma Lemma_EventuallyXMeansEventuallyY(i:int, x:temporal, y:temporal)
  requires sat(i, eventual(x))
  requires sat(i, leadsto(x, y))
  ensures  sat(i, eventual(y))
{
  TemporalAssist();
}

lemma Lemma_AlwaysEventuallyXAndXLeadsToYMeansAlwaysEventuallyY(i:int, x:temporal, y:temporal)
  requires sat(i, always(eventual(x)))
  requires sat(i, leadsto(x, y))
  ensures  sat(i, always(eventual(y)))
{
  TemporalAssist();

  forall j | TLe(i, j)
    ensures sat(j, eventual(y))
  {
    Lemma_EventuallyXMeansEventuallyY(j, x, y);
  }
}

lemma Lemma_LeadsToNextWithinImpliesLeadsToOtherNextWithin(
  i:int,
  x:temporal,
  action1:temporal,
  action2:temporal,
  t:int,
  timefun:imap<int, int>
  )
  requires imaptotal(timefun)
  requires sat(i, leadstonextwithin(x, action1, t, timefun))
  requires sat(i, always(imply(action1, action2)))
  ensures  sat(i, leadstonextwithin(x, action2, t, timefun))
{
  TemporalAssist();
  forall j | TLe(i, j) && sat(j, x)
    ensures sat(j, eventuallynextwithin(action2, t, timefun))
  {
    var k :| TLe(j, k) && sat(k, nextbefore(action1, timefun[j] + t, timefun));
    assert TLe(i, k);
  }
}

lemma Lemma_LeadsToNextWithinNextImpliesLeadsToOtherNextWithinNext(
  i:int,
  x:temporal,
  action1:temporal,
  action2:temporal,
  t:int,
  timefun:imap<int, int>
  )
  requires imaptotal(timefun)
  requires sat(i, leadstonextwithinnext(x, action1, t, timefun))
  requires sat(i, always(imply(action1, action2)))
  ensures  sat(i, leadstonextwithinnext(x, action2, t, timefun))
{
  TemporalAssist();
  forall j | TLe(i, j) && sat(j, x)
    ensures sat(j, next(eventuallynextwithin(action2, t, timefun)));
  {
    var k :| TLe(nextstep(j), k) && sat(k, nextbefore(action1, timefun[nextstep(j)] + t, timefun));
    assert TLe(i, k);
  }
}

lemma Lemma_LeadsToTwoWays(i:int, x:temporal, y:temporal, z:temporal)
  requires sat(i, leadsto(x, or(y, z)))
  requires sat(i, leadsto(y, z))
  ensures  sat(i, leadsto(x, z))
{
  TemporalAssist();
  TransitivityOfLeadsTo(i, x, or(y, z), z);
}

lemma Lemma_LeadsToWithinPossiblyImmediate(i:int, x:temporal, y:temporal, t:int, timefun:imap<int, int>)
  requires imaptotal(timefun)
  requires sat(i, leadstowithin(x, y, t, timefun))
  requires t >= 0
  ensures  sat(i, leadstowithin(or(x, y), y, t, timefun))
{
  TemporalAssist();
  forall j | TLe(i, j)
    ensures sat(j, imply(or(x, y), eventuallywithin(y, t, timefun)))
  {
    if sat(j, y)
    {
      TemporalEventually(j, j, beforeabsolutetime(y, timefun[j] + t, timefun));
    }
  }
}

lemma Lemma_LeadsToWithinImpliesLeadsToConsequenceWithin(i:int, x:temporal, y:temporal, z:temporal, t:int, timefun:imap<int, int>)
  requires imaptotal(timefun)
  requires sat(i, leadstowithin(x, y, t, timefun))
  requires sat(i, always(imply(y, z)))
  ensures  sat(i, leadstowithin(x, z, t, timefun))
{
  TemporalAssist();
  forall j | TLe(i, j) && sat(j, x)
    ensures sat(j, eventuallywithin(z, t, timefun))
  {
    var k :| TLe(j, k) && sat(k, beforeabsolutetime(y, timefun[j] + t, timefun));
    assert TLe(i, k);
  }
}

lemma Lemma_LeadsToWithinTwoWays(i:int, x:temporal, y:temporal, z:temporal, t1:int, t2:int, timefun:imap<int, int>)
  requires imaptotal(timefun)
  requires sat(i, leadstowithin(x, or(y, z), t1, timefun))
  requires sat(i, leadstowithin(y, z, t2, timefun))
  requires t2 >= 0
  ensures  sat(i, leadstowithin(x, z, t1+t2, timefun))
{
  Lemma_LeadsToWithinPossiblyImmediate(i, y, z, t2, timefun);
  TransitivityOfLeadsToWithin(i, x, or(y, z), z, t1, t2, timefun);
}

lemma Lemma_LeadsToTwoPossibilitiesWithin(i:int, w:temporal, x:temporal, y:temporal, z:temporal, t1:int, t2:int, timefun:imap<int, int>)
  requires imaptotal(timefun)
  requires sat(i, leadstowithin(w, or(x, z), t1, timefun))
  requires sat(i, leadstowithin(x, or(y, z), t2, timefun))
  requires t2 >= 0
  ensures  sat(i, leadstowithin(w, or(y, z), t1+t2, timefun))
{
  forall j | i <= j
    ensures sat(j, imply(or(x, z), or(x, or(y, z))));
  {
  }
  TemporalAlways(i, imply(or(x, z), or(x, or(y, z))));
  Lemma_LeadsToWithinImpliesLeadsToConsequenceWithin(i, w, or(x, z), or(x, or(y, z)), t1, timefun);
  Lemma_LeadsToWithinPossiblyImmediate(i, x, or(y, z), t2, timefun);
  TransitivityOfLeadsToWithin(i, w, or(x, or(y, z)), or(y, z), t1, t2, timefun);
}

lemma Lemma_LeadsToTwoPossibilitiesWithinWithFirstStepAnAction(i:int, w:temporal, x:temporal, y:temporal, z:temporal, t1:int,
                                                               t2:int, timefun:imap<int, int>)
  requires imaptotal(timefun)
  requires sat(i, always(imply(w, or(eventuallynextwithin(x, t1, timefun), eventuallywithin(z, t1, timefun)))))
  requires sat(i, always(imply(x, next(eventuallywithin(or(y, z), t2, timefun)))))
  requires t2 >= 0
  ensures  sat(i, leadstowithin(w, or(y, z), t1 + t2, timefun))
{
  TemporalAssist();
        
  forall j | TLe(i, j)
    ensures sat(j, imply(w, eventuallywithin(or(y, z), t1 + t2, timefun)))
  {
    if sat(j, w)
    {
      TemporalDeduceFromAlways(i, j, imply(w, or(eventuallynextwithin(x, t1, timefun), eventuallywithin(z, t1, timefun))));
      assert sat(j, imply(w, or(eventuallynextwithin(x, t1, timefun), eventuallywithin(z, t1, timefun))));
      if sat(j, eventuallynextwithin(x, t1, timefun))
      {
        var k :| TLe(j, k) && sat(k, nextbefore(x, timefun[j] + t1, timefun));
        TemporalDeduceFromAlways(i, k, imply(x, next(eventuallywithin(or(y, z), t2, timefun))));
        assert sat(nextstep(k), eventuallywithin(or(y, z), t2, timefun));
        var m :| TLe(nextstep(k), m) && sat(m, beforeabsolutetime(or(y, z), timefun[k+1] + t2, timefun));
        assert TLe(j, m);
        assert sat(j, eventuallywithin(or(y, z), t1 + t2, timefun));
      }
      else
      {
        assert sat(j, eventuallywithin(z, t1, timefun));
        assert sat(j, eventuallywithin(or(y, z), t1, timefun));
        assert sat(j, eventuallywithin(or(y, z), t1 + t2, timefun));
      }
    }
  }
}

lemma Lemma_LeadsToWithinLeadsToTransition(i:int, x:temporal, y:temporal, t:int, timefun:imap<int, int>)
  requires imaptotal(timefun)
  requires sat(i, leadstowithin(x, y, t, timefun))
  requires sat(i, always(imply(x, not(y))))
  requires monotonic_from(i, timefun)
  ensures  sat(i, leadstonextwithin(x, and(not(y), next(y)), t, timefun))
{
  TemporalAssist();

  forall j | i <= j
    ensures sat(j, imply(x, eventuallynextwithin(and(not(y), next(y)), t, timefun)))
  {
    if sat(j, x)
    {
      TemporalDeduceFromAlways(i, j, imply(x, eventuallywithin(y, t, timefun)));
      var k := TemporalDeduceFromEventual(j, beforeabsolutetime(y, timefun[j] + t, timefun));
      var m := earliestStep(j, y);
      TemporalDeduceFromAlways(i, j, imply(x, not(y)));
      assert j != m;
      var prev := m-1;
      assert j <= prev < m;
      assert !sat(prev, y);
      assert sat(prev, and(not(y), next(y)));
      TemporalEventually(j, prev, nextbefore(and(not(y), next(y)), timefun[j] + t, timefun));
    }
  }
}

lemma Lemma_LeadsToWithinOrSomethingLeadsToTransitionOrSomething(i:int, x:temporal, y:temporal, z:temporal, t:int, timefun:imap<int, int>)
  requires imaptotal(timefun)
  requires sat(i, leadstowithin(x, or(y, z), t, timefun))
  requires sat(i, always(imply(x, not(y))))
  requires monotonic_from(i, timefun)
  ensures  sat(i, always(imply(x, or(eventuallynextwithin(and(not(y), next(y)), t, timefun), eventuallywithin(z, t, timefun)))))
{
  TemporalAssist();

  forall j | i <= j
    ensures sat(j, imply(x, or(eventuallynextwithin(and(not(y), next(y)), t, timefun), eventuallywithin(z, t, timefun))))
  {
    if sat(j, x)
    {
      TemporalDeduceFromAlways(i, j, imply(x, eventuallywithin(or(y, z), t, timefun)));
      var k :| j <= k && sat(k, beforeabsolutetime(or(y, z), timefun[j] + t, timefun));
      if sat(k, z)
      {
        assert sat(k, beforeabsolutetime(z, timefun[j] + t, timefun));
        assert sat(j, eventuallywithin(z, t, timefun));
      }
      else
      {
        var m := earliestStep(j, y);
        var prev := m-1;
        TemporalDeduceFromAlways(i, j, imply(x, not(y)));
        assert !sat(prev, y);
        assert sat(prev, and(not(y), next(y)));
        TemporalEventually(j, prev, nextbefore(and(not(y), next(y)), timefun[j] + t, timefun));
        assert sat(j, eventuallynextwithin(and(not(y), next(y)), t, timefun));
      }
    }
  }
}

lemma TemporalDeduceFromLeadsToWithin(i:int, j:int, x:temporal, y:temporal, t:int, timefun:imap<int, int>) returns (step:int)
  requires imaptotal(timefun)
  requires sat(i, leadstowithin(x, y, t, timefun))
  requires i <= j
  requires sat(j, x)
  ensures  j <= step
  ensures  timefun[step] <= timefun[j] + t
  ensures  sat(step, y)
{
  TemporalDeduceFromAlways(i, j, imply(x, eventuallywithin(y, t, timefun)));
  step := TemporalDeduceFromEventuallyWithin(j, y, t, timefun);
}

} 
