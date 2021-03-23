include "../../../Common/Collections/Maps2.i.dfy"
include "../../../Common/Logic/Temporal/Temporal.s.dfy"
include "../../../Common/Logic/Temporal/Heuristics.i.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"
include "../../../Common/Logic/Temporal/Time.i.dfy"
include "../../../Common/Logic/Temporal/Induction.i.dfy"
include "../../../Common/Logic/Temporal/WF1.i.dfy"
include "../../../../Libraries/Math/mul_auto.i.dfy"
include "../../../../Libraries/Math/mod_auto.i.dfy"

module Liveness__RTSchedule_i {
import opened Collections__Maps2_i
import opened Temporal__Temporal_s
import opened Temporal__Heuristics_i
import opened Temporal__Monotonicity_i
import opened Temporal__Rules_i
import opened Temporal__Time_s
import opened Temporal__Time_i
import opened Temporal__Induction_i
import opened Temporal__WF1_i
import opened Math__mul_auto_i
import opened Math__mod_auto_i
import opened Collections__Maps2_s

// NOTE:  This round-robin scheduler assumes that all actions in the schedule are always enabled.
//        This assumption can make the spec be not machine-closed, in Lamport's terminology.
//        In other words, it can make the actions impossible to implement.  So, unless you
//        want your spec to be unimplementable, make sure that every action is always enabled,
//        e.g., by letting it stutter if there's nothing to do.  An action A is enabled if
//        forall s :: exists s' :: apply(A, (s, s')).

lemma Lemma_RoundRobinSchedulerTimelyForAllActionsTemporal<S>(
  behavior:Behavior<S>,                   // The behavior we'll prove it for
  next_action_type_fun:imap<int, int>,    // A function that takes a step and computes which action type has priority
  real_time_fun:imap<int, int>,           // A function that takes a step and computes at what real time it happened
  scheduler_action:temporal,              // The subaction of 'next' that executes the scheduler
  schedule:seq<temporal>,                 // The schedule the scheduler follows
  start_step:int,                         // The step at which the scheduler starts executing regularly
  interval:int                            // The maximum interval between scheduler actions during the regular-execution period
  )
  requires imaptotal(behavior)
  requires imaptotal(next_action_type_fun)
  requires imaptotal(real_time_fun)

  // The priority starts as a valid value.  Note that this also implies the schedule has at least one action.
  requires 0 <= next_action_type_fun[0] < |schedule|

  // The regular-execution period is sensible.
  requires 0 <= start_step
  requires interval > 0

  // Every step either invokes the scheduler or leaves the action priority unchanged.
  requires sat(0, always(SchedulerActsOrNextActionTypeUnchangedTemporal(behavior, next_action_type_fun, scheduler_action)))

  // If the scheduler takes a step, it takes an action of the prioritized type, then gives
  // priority to the next action type in round-robin order.
  requires forall i {:trigger sat(i, scheduler_action)} :: 0 <= i && sat(i, scheduler_action) ==>
                 var action_type_index := next_action_type_fun[i];
                 && (0 <= action_type_index < |schedule| ==> sat(i, schedule[action_type_index]))
                 && next_action_type_fun[i+1] == (action_type_index + 1) % |schedule|

  // Time moves forward.
  requires monotonic_from(0, real_time_fun)

  // The scheduler takes at least one step every interval during the epoch during which it's regularly scheduled.
  requires sat(start_step, always(eventuallynextwithin(scheduler_action, interval, real_time_fun)))

  // For each action type, an action of that type will happen in any period of duration (schedule-size * interval)
  // that is within the regular-execution period.
  ensures forall action_type_index ::
            0 <= action_type_index < |schedule| ==>
            sat(start_step, always(eventuallynextwithin(schedule[action_type_index], interval * |schedule|, real_time_fun)))
{
  var b := behavior;
  var span := interval;
  var i0 := start_step;
  var naf := next_action_type_fun;
  var n := |schedule|;
  var timefun := real_time_fun;
  var next_action := SchedulerActsOrNextActionTypeUnchangedTemporal(behavior, next_action_type_fun, scheduler_action);
  assert sat(0, always(next_action));

  forall ensures forall i {:trigger naf[i]} :: TLe(i0, i) ==> 0 <= naf[i] < n
  {
    TemporalAssist();
    var x := stepmap(imap i :: 0 <= naf[i] < n);
    assert sat(0, x);
    forall i | TLe(0, i)
      ensures sat(i, imply(x, next(x)))
    {
    }
    TemporalInductionNext(0, x);
    assert sat(i0, always(stepmap(imap i :: 0 <= naf[i] < n)));
  }

  forall a0 | 0 <= a0 < n
    ensures sat(i0, always(eventuallynextwithin(schedule[a0], span * n, timefun)))
  {
    var d := imap i :: 1 + ((a0 - naf[i]) % n);
    var goal := schedule[a0];

    forall ensures sat(i0, always(nextOrDecreaseWithin(goal, d, span, timefun)))
    {
      TemporalAssist();
      forall i1 {:trigger TLe(i0, i1)} | TLe(i0, i1)
        ensures sat(i1, nextOrDecreaseWithin(goal, d, span, timefun))
      {
        var i2 := earliestActionWithin(i1, scheduler_action, span, timefun);
        assert TLe(i1, i2);
        assert forall i :: TLe(i1, i) && TLe(i, i2 - 1) ==> sat(i, not(scheduler_action));
        var a2 := naf[i2];
        if (a2 != a0)
        {
          forall ensures d[i2 + 1] < d[i1]
          {
            forall ensures naf[i1] == a2
            {
              var indF := imap i :: naf[i1] == naf[i];
              forall i | TLe(i1, i) && TLe(i + 1, i2) && indF[i]
                ensures indF[i + 1]
              {
                assert sat(i, next_action);
              }
              Lemma_imapInductionRange(i1, i2, indF);
            }
            Lemma_mod_incr_decreases(a0, a2, n);
          }
        }
        assert sat(i1, eventuallynextwithin(or(goal, nextDecrease(i1, d)), span, timefun));
      }
      assert sat(i0, always(nextOrDecreaseWithin(goal, d, span, timefun)));
    }

    Lemma_EventuallynextWithinSpans(i0, d, goal, span, timefun);
    Lemma_EventuallynextWithinBound(i0, d, n, goal, span, timefun);
    assert sat(i0, always(eventuallynextwithin(schedule[a0], span * n, timefun)));
  }
}

lemma Lemma_mod_incr_decreases(x:int, y:int, n:int)
  requires 0 <= x < n
  requires 0 <= y < n
  requires x != y
  ensures (x - ((y + 1) % n)) % n < (x - y) % n
{
  lemma_mod_auto(n);
}

function{:opaque} SchedulerActsOrNextActionTypeUnchangedTemporal<S>(
  behavior:Behavior<S>,
  next_action_type_fun:imap<int, int>,
  scheduler_action:temporal
  ):temporal
  requires forall i :: i in behavior // TODO: Replace with imaptotal
  requires imaptotal(next_action_type_fun)
  ensures  forall i {:trigger sat(i, SchedulerActsOrNextActionTypeUnchangedTemporal(behavior, next_action_type_fun, scheduler_action))} ::
               sat(i, SchedulerActsOrNextActionTypeUnchangedTemporal(behavior, next_action_type_fun, scheduler_action)) <==>
               (sat(i, scheduler_action) || next_action_type_fun[i] == next_action_type_fun[i+1])
{
  stepmap(imap i :: sat(i, scheduler_action) || next_action_type_fun[i] == next_action_type_fun[i+1])
}

lemma Lemma_RoundRobinSchedulerEventuallyPerformsNextAction<S>(
  behavior:Behavior<S>,
  next_action_type_fun:imap<int, int>,
  scheduler_action:temporal,
  schedule:seq<temporal>,
  start_step:int,
  earliest_step:int,
  action_type:int
  ) returns
  (action_step:int)
  requires imaptotal(behavior)
  requires imaptotal(next_action_type_fun)
  requires 0 <= start_step <= earliest_step
  requires 0 <= action_type < |schedule|
  requires next_action_type_fun[earliest_step] == action_type
  requires sat(0, always(SchedulerActsOrNextActionTypeUnchangedTemporal(behavior, next_action_type_fun, scheduler_action)))
  requires forall i {:trigger sat(i, scheduler_action)} :: 0 <= i && sat(i, scheduler_action) ==>
                 var action_type_index := next_action_type_fun[i];
                 && (0 <= action_type_index < |schedule| ==> sat(i, schedule[action_type_index]))
                 && next_action_type_fun[i+1] == (action_type_index + 1) % |schedule|
  requires sat(start_step, always(eventual(scheduler_action)))
  ensures  earliest_step <= action_step
  ensures  sat(action_step, schedule[action_type])
  ensures  next_action_type_fun[action_step+1] == (action_type + 1) % |schedule|
{
  TemporalDeduceFromAlways(start_step, earliest_step, eventual(scheduler_action));
  var later_action_step := TemporalDeduceFromEventual(earliest_step, scheduler_action);

  var P := stepmap(imap i :: next_action_type_fun[i] == action_type);
  var Q := and(schedule[action_type], next(stepmap(imap i :: next_action_type_fun[i] == (action_type + 1) % |schedule|)));

  forall j | earliest_step <= j
    ensures sat(j, TemporalWF1Req1(P, Q))
  {
    TemporalDeduceFromAlways(0, j, SchedulerActsOrNextActionTypeUnchangedTemporal(behavior, next_action_type_fun, scheduler_action));
  }

  action_step := TemporalWF1Specific(earliest_step, later_action_step, P, Q);
}

lemma Lemma_RoundRobinSchedulerEventuallyPerformsCertainNextAction<S>(
  behavior:Behavior<S>,
  next_action_type_fun:imap<int, int>,
  scheduler_action:temporal,
  schedule:seq<temporal>,
  start_step:int,
  earliest_step:int,
  next_action_type:int,
  action_type:int
  ) returns
  (action_step:int)
  requires imaptotal(behavior)
  requires imaptotal(next_action_type_fun)
  requires 0 <= start_step <= earliest_step
  requires 0 <= next_action_type < |schedule|
  requires 0 <= action_type < |schedule|
  requires next_action_type_fun[earliest_step] == next_action_type
  requires sat(0, always(SchedulerActsOrNextActionTypeUnchangedTemporal(behavior, next_action_type_fun, scheduler_action)))
  requires forall i {:trigger sat(i, scheduler_action)} :: 0 <= i && sat(i, scheduler_action) ==>
                 var action_type_index := next_action_type_fun[i];
                 && (0 <= action_type_index < |schedule| ==> sat(i, schedule[action_type_index]))
                 && next_action_type_fun[i+1] == (action_type_index + 1) % |schedule|
  requires sat(start_step, always(eventual(scheduler_action)))
  ensures  earliest_step <= action_step
  ensures  sat(action_step, schedule[action_type])
  ensures  next_action_type_fun[action_step+1] == (action_type + 1) % |schedule|
  decreases (|schedule| + action_type - next_action_type) % |schedule|
{
  if action_type == next_action_type
  {
    action_step := Lemma_RoundRobinSchedulerEventuallyPerformsNextAction(behavior, next_action_type_fun, scheduler_action,
                                                                         schedule, start_step, earliest_step, action_type);
    return;
  }

  var earlier_action_step := Lemma_RoundRobinSchedulerEventuallyPerformsNextAction(behavior, next_action_type_fun,
                                                                                  scheduler_action, schedule, start_step,
                                                                                  earliest_step, next_action_type);

  lemma_mod_auto(|schedule|);

  action_step := Lemma_RoundRobinSchedulerEventuallyPerformsCertainNextAction(behavior, next_action_type_fun, scheduler_action,
                                                                             schedule, start_step, earlier_action_step + 1,
                                                                             (next_action_type + 1) % |schedule|, action_type);
}

lemma Lemma_RoundRobinSchedulerEventuallyPerformsSpecificAction<S>(
  behavior:Behavior<S>,                   // The behavior we'll prove it for
  next_action_type_fun:imap<int, int>,    // A function that takes a step and computes which action type has priority
  scheduler_action:temporal,              // The subaction of 'next' that executes the scheduler
  schedule:seq<temporal>,                 // The schedule the scheduler follows
  start_step:int,                         // The step at which the scheduler starts executing regularly
  earliest_step:int,                      // The step from which we need to find a subsequent step that takes the action
  action_type:int                         // The action type to find an action for
  ) returns
  (action_step:int)
  requires imaptotal(behavior)
  requires imaptotal(next_action_type_fun)

  // The priority starts as a valid value.  Note that this also implies the schedule has at least one action.
  requires 0 <= next_action_type_fun[0] < |schedule|

  // The regular-execution period is sensible.
  requires 0 <= start_step

  // The requested parameters are sensible.
  requires start_step <= earliest_step
  requires 0 <= action_type < |schedule|

  // Every step either invokes the scheduler or leaves the action priority unchanged.
  requires sat(0, always(SchedulerActsOrNextActionTypeUnchangedTemporal(behavior, next_action_type_fun, scheduler_action)))

  // If the scheduler takes a step, it takes an action of the prioritized type, then gives
  // priority to the next action type in round-robin order.
  requires forall i {:trigger sat(i, scheduler_action)} :: 0 <= i && sat(i, scheduler_action) ==>
                 var action_type_index := next_action_type_fun[i];
                 && (0 <= action_type_index < |schedule| ==> sat(i, schedule[action_type_index]))
                 && next_action_type_fun[i+1] == (action_type_index + 1) % |schedule|

  // The scheduler takes at least one step every interval during the epoch during which it's regularly scheduled.
  requires sat(start_step, always(eventual(scheduler_action)))

  ensures  earliest_step <= action_step
  ensures  sat(action_step, schedule[action_type])
{
  var x := stepmap(imap i :: 0 <= next_action_type_fun[i] < |schedule|);
  forall i | 0 <= i
    ensures sat(i, imply(x, next(x)))
  {
    reveal imply();
    reveal next();
    TemporalDeduceFromAlways(0, i, SchedulerActsOrNextActionTypeUnchangedTemporal(behavior, next_action_type_fun, scheduler_action));
  }
  TemporalInductionNext(0, x);
  TemporalDeduceFromAlways(0, earliest_step, x);

  var next_action_type := next_action_type_fun[earliest_step];
  action_step := Lemma_RoundRobinSchedulerEventuallyPerformsCertainNextAction(behavior, next_action_type_fun, scheduler_action,
                                                                              schedule, start_step, earliest_step, next_action_type,
                                                                              action_type);
}

} 
