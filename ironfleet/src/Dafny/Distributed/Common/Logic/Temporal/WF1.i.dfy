include "Temporal.s.dfy"
include "Heuristics.i.dfy"
include "Rules.i.dfy"
include "LeadsTo.i.dfy"
include "Induction.i.dfy"
include "Time.i.dfy"

module Temporal__WF1_i {
import opened Temporal__Temporal_s
import opened Temporal__Heuristics_i
import opened Temporal__Rules_i
import opened Temporal__LeadsTo_i
import opened Temporal__Induction_i
import opened Temporal__Time_s
import opened Temporal__Time_i
import opened Collections__Maps2_s
import opened Collections__Maps2_i

/////////////////////
// DEFINITIONS
/////////////////////

function TemporalWF1Req1(P:temporal, Q:temporal):temporal
{
  imply(P, or(Q, next(or(P, Q))))
}

function TemporalWF1Req2(P:temporal, Q:temporal, Action:temporal):temporal
{
  imply(and(P, Action), or(Q, next(Q)))
}

function TemporalWF1RealTimeDelayedReq2(P:temporal, Q:temporal, Action:temporal, rt:int, timefun:imap<int, int>):temporal
  requires imaptotal(timefun)
{
  imply(and(P, nextafter(Action, rt, timefun)), or(Q, next(Q)))
}

function TemporalWF1RealTimeDelayedImmediateQReq2(P:temporal, Q:temporal, Action:temporal, rt:int, timefun:imap<int, int>):temporal
  requires imaptotal(timefun)
{
  imply(and(P, nextafter(Action, rt, timefun)), Q)
}

/////////////////////
// LEMMAS
/////////////////////

lemma TemporalWF1(i:int, P:temporal, Q:temporal, Action:temporal)
  requires sat(i, always(imply(P, or(Q, next(or(P, Q))))))
  requires sat(i, always(imply(and(P, Action), or(Q, next(Q)))))
  requires sat(i, always(eventual(Action)))
  ensures  sat(i, leadsto(P, Q))
{
  TemporalAssist();
        
  if !sat(i, leadsto(P, Q)) {
    assert sat(i, eventual(and(P, not(eventual(Q)))));
    var j :| TLe(i, j) && sat(j, and(P, not(eventual(Q))));
    TemporalInductionNext(j, P);
  }
}

lemma TemporalWF1Specific(i:int, action_step:int, P:temporal, Q:temporal) returns (q_step:int)
  requires i <= action_step
  requires forall j :: i <= j ==> sat(j, TemporalWF1Req1(P, Q))
  requires sat(i, P)
  requires sat(action_step, imply(P, or(Q, next(Q))))
  ensures  i <= q_step <= action_step + 1
  ensures  sat(q_step, Q)
{
  if sat(action_step, P)
  {
    q_step := if sat(action_step, Q) then action_step else action_step + 1;
    return;
  }
  
  var transition_step := earliestStepBetween(i, action_step, not(P)) - 1;
  assert i <= transition_step < action_step;
  assert sat(transition_step, TemporalWF1Req1(P, Q));
  q_step := if sat(transition_step, Q) then transition_step else transition_step + 1;
}

lemma TemporalWF1RealTime(i:int, P:temporal, Q:temporal, action:temporal, span:int, timefun:imap<int, int>)
  requires imaptotal(timefun)
  requires monotonic_from(i, timefun)
  requires sat(i, always(imply(P, or(Q, next(or(P, Q))))))
  requires sat(i, always(imply(and(P, action), or(Q, next(Q)))))
  requires sat(i, always(eventuallynextwithin(action, span, timefun)))
  ensures  sat(i, leadstowithin(P, Q, span, timefun))
{
  TemporalAssist();
  forall j | TLe(i, j) && sat(j, P)
    ensures sat(j, eventuallywithin(Q, span, timefun));
  {
    var k :| TLe(j, k) && sat(k, nextbefore(action, timefun[j] + span, timefun));
    if !sat(j, eventuallywithin(Q, span, timefun))
    {
      assert TLe(j, k+1);
      assert !sat(k+1, Q);
      var m := imap b :: b > k;
      var x := or(P, stepmap(m));
      forall a | TLe(j, a)
        ensures sat(a, x) ==> sat(a+1, x);
      {
        if a < k
        {
          assert timefun[a] <= timefun[a+1] <= timefun[k] <= timefun[j] + span;
          assert TLe(j, a);
          assert !sat(a, Q);
          assert TLe(j, a+1);
          assert !sat(a+1, Q);
        }
      }
      TemporalInductionNext(j, x);
      assert sat(k, x);
      assert false;
    }
  }
  assert sat(i, leadstowithin(P, Q, span, timefun));
}

lemma TemporalWF1RealTimeDelayed(i:int, P:temporal, Q:temporal, action:temporal, span:int, rt:int, timefun:imap<int, int>)
  returns (step:int)
  requires imaptotal(timefun)
  requires monotonic_from(0, timefun)
  requires forall t :: sat(0, eventual(after(t, timefun)))
  requires 0 <= span
  requires 0 <= i
  requires sat(i, P)
  requires sat(i, always(imply(P, or(Q, next(or(P, Q))))))
  requires sat(i, always(imply(and(P, nextafter(action, rt, timefun)), or(Q, next(Q)))))
  requires sat(i, always(eventuallynextwithin(action, span, timefun)))
  ensures  i <= step
  ensures  sat(step, Q)
  ensures  timefun[step] <= (if rt >= timefun[i] then rt else timefun[i]) + span
{
  var wait := if rt >= timefun[i] then rt - timefun[i] else 0;
  reveal after();
  var j := Lemma_AlwaysEventuallyWithinMeansAlwaysEventuallyWithinAfter(i, action, wait, span, timefun);
  assert timefun[j+1] <= (if rt >= timefun[i] then rt else timefun[i]) + span;
  if sat(i, always(P))
  {
    TemporalDeduceFromAlways(i, j, P);
    TemporalDeduceFromAlways(i, j, imply(and(P, nextafter(action, rt, timefun)), or(Q, next(Q))));
    step := if sat(j, Q) then j else j + 1;
  }
  else
  {
    TemporalNot(i, P);
    var k := earliestStep(i, not(P));
    assert sat(k-1, P);
    assert sat(k, not(P));
    if k > j + 1
    {
      assert i <= j + 1 < k ==> !sat(j, not(P));
      TemporalDeduceFromAlways(i, j, imply(and(P, nextafter(action, rt, timefun)), or(Q, next(Q))));
      step := if sat(j, Q) then j else j + 1;
    }
    else
    {
      assert i < k;
      TemporalDeduceFromAlways(i, k-1, imply(P, or(Q, next(or(P, Q)))));
      if sat(k-1, Q)
      {
        step := k - 1;
      }
      else
      {
        assert sat(k-1, next(or(P, Q)));
        step := k;
      }
    }
  }
}

lemma TemporalWF1RealTimeDelayedImmediateQ(i:int, P:temporal, Q:temporal, action:temporal, span:int, rt:int, timefun:imap<int, int>)
  returns (step:int)
  requires imaptotal(timefun)
  requires monotonic_from(0, timefun)
  requires forall t :: sat(0, eventual(after(t, timefun)))
  requires 0 <= span
  requires 0 <= i
  requires sat(i, P)
  requires sat(i, always(imply(P, or(Q, next(P)))))
  requires sat(i, always(imply(and(P, nextafter(action, rt, timefun)), Q)))
  requires sat(i, always(eventuallynextwithin(action, span, timefun)))
  ensures  i <= step
  ensures  sat(step, Q)
  ensures  timefun[step+1] <= (if rt >= timefun[i] then rt else timefun[i]) + span
{
  var wait := if rt >= timefun[i] then rt - timefun[i] else 0;
  reveal after();
  var j := Lemma_AlwaysEventuallyWithinMeansAlwaysEventuallyWithinAfter(i, action, wait, span, timefun);
  assert timefun[j+1] <= (if rt >= timefun[i] then rt else timefun[i]) + span;
  if sat(i, always(P))
  {
    TemporalDeduceFromAlways(i, j, P);
    TemporalDeduceFromAlways(i, j, imply(and(P, nextafter(action, rt, timefun)), Q));
    step := j;
  }
  else
  {
    TemporalNot(i, P);
    var k := earliestStep(i, not(P));
    assert sat(k-1, P);
    assert sat(k, not(P));
    if k > j + 1
    {
      assert i <= j + 1 < k ==> !sat(j, not(P));
      TemporalDeduceFromAlways(i, j, imply(and(P, nextafter(action, rt, timefun)), Q));
      step := j;
    }
    else
    {
      assert i < k;
      TemporalDeduceFromAlways(i, k-1, imply(P, or(Q, next(P))));
      assert !sat(k-1, next(P));
      assert sat(k-1, Q);
      step := k - 1;
    }
  }
}

} 
