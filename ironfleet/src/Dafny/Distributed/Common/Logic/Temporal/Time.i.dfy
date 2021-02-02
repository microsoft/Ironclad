include "Time.s.dfy"
include "Heuristics.i.dfy"
include "Rules.i.dfy"
include "Monotonicity.i.dfy"
include "../../../../Libraries/Math/mul.i.dfy"

module Temporal__Time_i {
import opened Temporal__Time_s
import opened Temporal__Heuristics_i
import opened Temporal__Rules_i
import opened Temporal__Monotonicity_i
import opened Math__mul_i
import opened Temporal__Temporal_s
import opened Collections__Maps2_s
import opened Collections__Maps2_i
import opened Math__mul_auto_i

/////////////////////////
// DEFINITIONS
/////////////////////////

    function{:opaque} earliestStepWithin(start:int, x:temporal, span:int, timefun:imap<int, int>):int
        requires imaptotal(timefun);
        requires monotonic_from(start, timefun);
        requires sat(start, eventuallywithin(x, span, timefun));
        ensures  sat(earliestStepWithin(start, x, span, timefun), beforeabsolutetime(x, timefun[start] + span, timefun));
        ensures  start <= earliestStepWithin(start, x, span, timefun);
        ensures  forall i :: start <= i < earliestStepWithin(start, x, span, timefun) ==> !sat(i, x);
    {
        TemporalAssist();
        var i1 := earliestStep(start, x);
        var i2 := earliestStep(start, beforeabsolutetime(x, timefun[start] + span, timefun));
        assert TLe(i1, i2);
        i1
    }

    function{:opaque} earliestActionWithin(start:int, x:temporal, span:int, timefun:imap<int, int>):int
        requires imaptotal(timefun);
        requires monotonic_from(start, timefun);
        requires sat(start, eventuallynextwithin(x, span, timefun));
        ensures  sat(earliestActionWithin(start, x, span, timefun), and(x, next(before(timefun[start] + span, timefun))));
        ensures  start <= earliestActionWithin(start, x, span, timefun);
        ensures  forall i :: start <= i < earliestActionWithin(start, x, span, timefun) ==> !sat(i, x);
    {
        TemporalAssist();
        var i1 := earliestStep(start, x);
        var i2 := earliestStep(start, and(x, next(before(timefun[start] + span, timefun))));
        assert TLe(i1, i2);
        i1
    }

    function{:opaque} goalOrDecrease(goal:temporal, d:imap<int, int>, span:int, timefun:imap<int, int>):temporal
        requires imaptotal(d);
        requires imaptotal(timefun);
        ensures  forall i {:trigger sat(i, goalOrDecrease(goal, d, span, timefun))} :: sat(i, goalOrDecrease(goal, d, span, timefun)) <==>
                    sat(i, eventuallywithin(or(goal, stepDecrease(i, d)), span, timefun));
    {
        TemporalAssist();
        stepmap(imap i :: sat(i, eventuallywithin(or(goal, stepDecrease(i, d)), span, timefun)))
    }

    function{:opaque} nextOrDecreaseWithin(goal:temporal, d:imap<int, int>, span:int, timefun:imap<int, int>):temporal
        requires imaptotal(d);
        requires imaptotal(timefun);
        ensures  forall i {:trigger sat(i, nextOrDecreaseWithin(goal, d, span, timefun))} :: sat(i, nextOrDecreaseWithin(goal, d, span, timefun)) <==>
                    sat(i, eventuallynextwithin(or(goal, nextDecrease(i, d)), span, timefun));
    {
        TemporalAssist();
        stepmap(imap i :: sat(i, eventuallynextwithin(or(goal, nextDecrease(i, d)), span, timefun)))
    }

    function{:opaque} eventuallywithinspans(d:imap<int, int>, goal:temporal, span:int, timefun:imap<int, int>):temporal
        requires imaptotal(d);
        requires imaptotal(timefun);
        ensures  forall i {:trigger sat(i, eventuallywithinspans(d, goal, span, timefun))} ::
                    sat(i, eventuallywithinspans(d, goal, span, timefun)) <==>
                    sat(i, eventuallywithin(goal, span * d[i], timefun));
    {
        TemporalAssist();
        stepmap(imap i :: sat(i, eventuallywithin(goal, span * d[i], timefun)))
    }

    function{:opaque} eventuallynextwithinspans(d:imap<int, int>, goal:temporal, span:int, timefun:imap<int, int>):temporal
        requires imaptotal(d);
        requires imaptotal(timefun);
        ensures  forall i {:trigger sat(i, eventuallynextwithinspans(d, goal, span, timefun))} ::
                    sat(i, eventuallynextwithinspans(d, goal, span, timefun)) <==>
                    sat(i, eventuallynextwithin(goal, span * d[i], timefun));
    {
        TemporalAssist();
        stepmap(imap i :: sat(i, eventuallynextwithin(goal, span * d[i], timefun)))
    }

    function stepattimeboundary(i:int, j:int, t:int, timefun:imap<int, int>):int
        requires imaptotal(timefun);
        requires monotonic_from(i, timefun);
        requires timefun[i] <= t;
        requires timefun[j] >= t;
        requires i <= j;
        ensures  var k := stepattimeboundary(i, j, t, timefun);
                    timefun[k] <= t
                 && i <= k <= j
                 && forall m :: m > k ==> timefun[m] >= t;
        decreases j-i;
    {
        if i == j then i else if timefun[j-1] <= t then j-1 else stepattimeboundary(i, j-1, t, timefun)
    }

/////////////////////////
// LEMMAS
/////////////////////////

    lemma TemporalEventuallyWithin(i:int, j:int, x:temporal, span:int, timefun:imap<int, int>)
        requires imaptotal(timefun);
        requires i <= j;
        requires sat(j, beforeabsolutetime(x, timefun[i] + span, timefun));
        ensures  sat(i, eventuallywithin(x, span, timefun));
    {
        TemporalAssist();
    }

    lemma TemporalEventuallyNextWithin(i:int, j:int, x:temporal, span:int, timefun:imap<int, int>)
        requires imaptotal(timefun);
        requires i <= j;
        requires sat(j, x);
        requires sat(j+1, before(timefun[i] + span, timefun));
        ensures  sat(i, eventuallynextwithin(x, span, timefun));
    {
        TemporalAssist();
    }

    lemma Lemma_EventuallyWithinSpansHelper(start:int, start':int, d:imap<int, int>, goal:temporal, span:int, timefun:imap<int, int>)
        requires imaptotal(d);
        requires imaptotal(timefun);
        requires 1 <= span;
        requires TLe(start, start');
        requires forall i :: start <= i ==> 1 <= d[i];
        requires sat(start, always(goalOrDecrease(goal, d, span, timefun)));
        ensures  sat(start', eventuallywithin(goal, span * d[start'], timefun));
        decreases d[start'];
    {
        TemporalAssist();
        assert sat(start', goalOrDecrease(goal, d, span, timefun));
        var n1 {:trigger TLe(start', n1)} :|
            TLe(start', n1) && sat(n1, beforeabsolutetime(or(goal, stepDecrease(start', d)), timefun[start'] + span, timefun));
        if (sat(n1, goal))
        {
            calc
            {
                1 <= d[start'];
                { lemma_mul_inequality(1, d[start'], span); }
                span * 1 <= span * d[start'];
            }
        }
        else
        {
            Lemma_EventuallyWithinSpansHelper(start, n1, d, goal, span, timefun);
            var n2 {:trigger TLe(n1, n2)} :| TLe(n1, n2)
                && sat(n2, beforeabsolutetime(goal, timefun[n1] + span * d[n1], timefun));
            calc
            {
                d[n1] + 1 <= d[start'];
                { lemma_mul_inequality_forall(); lemma_mul_is_commutative_forall(); }
                span * (d[n1] + 1) <= span * d[start'];
                { lemma_mul_is_distributive_forall(); }
                span * d[n1] + span <= span * d[start'];
            }
            assert sat(n2, beforeabsolutetime(goal, timefun[start'] + span * d[start'], timefun));
        }
    }

    // If   []t :: <span>(goal || d < d[t])
    // and  [](0 <= d)
    // then []<span * d>(goal)
    lemma Lemma_EventuallyWithinSpans(start:int, d:imap<int, int>, goal:temporal, span:int, timefun:imap<int, int>)
        requires imaptotal(d);
        requires imaptotal(timefun);
        requires 1 <= span;
        requires forall i :: start <= i ==> 1 <= d[i];
        requires sat(start, always(goalOrDecrease(goal, d, span, timefun)));
        ensures  sat(start, always(eventuallywithinspans(d, goal, span, timefun)));
    {
        TemporalAssist();
        forall start' | TLe(start, start')
            ensures sat(start', eventuallywithin(goal, span * d[start'], timefun));
        {
            Lemma_EventuallyWithinSpansHelper(start, start', d, goal, span, timefun);
        }
    }

    // If   []<span * d>(goal)
    // and  [](d <= n)
    // then []<span * n>(goal)
    lemma Lemma_EventuallyWithinBound(start:int, d:imap<int, int>, n:int, goal:temporal, span:int, timefun:imap<int, int>)
        requires imaptotal(d);
        requires imaptotal(timefun);
        requires forall i :: d[i] <= n;
        requires 0 <= span;
        requires sat(start, always(eventuallywithinspans(d, goal, span, timefun)));
        ensures  sat(start, always(eventuallywithin(goal, span * n, timefun)));
    {
        TemporalAssist();
        forall i1 | TLe(start, i1)
            ensures sat(i1, eventuallywithin(goal, span * n, timefun));
        {
            lemma_mul_inequality_forall();
            lemma_mul_is_commutative_forall();
            assert span * d[i1] <= span * n;
        }
    }

    lemma Lemma_EventuallynextWithinSpansHelper(start:int, start':int, d:imap<int, int>, goal:temporal, span:int, timefun:imap<int, int>)
        requires imaptotal(d);
        requires imaptotal(timefun);
        requires 1 <= span;
        requires TLe(start, start');
        requires forall i :: start <= i ==> 1 <= d[i];
        requires sat(start, always(nextOrDecreaseWithin(goal, d, span, timefun)));
        ensures  sat(start', eventuallynextwithin(goal, span * d[start'], timefun));
        decreases d[start'];
    {
        TemporalAssist();
        assert sat(start', nextOrDecreaseWithin(goal, d, span, timefun));
        var n1 {:trigger TLe(start', n1)} :|
            TLe(start', n1) && sat(n1, and(or(goal, nextDecrease(start', d)), next(before(timefun[start'] + span, timefun))));
        if (sat(n1, goal))
        {
            calc
            {
                1 <= d[start'];
                { lemma_mul_inequality(1, d[start'], span); }
                span * 1 <= span * d[start'];
            }
        }
        else
        {
            Lemma_EventuallynextWithinSpansHelper(start, n1 + 1, d, goal, span, timefun);
            var n2 {:trigger TLe(n1 + 1, n2)} :| TLe(n1 + 1, n2)
                && sat(n2, and(goal, next(before(timefun[n1 + 1] + span * d[n1 + 1], timefun))));
            calc
            {
                d[n1 + 1] + 1 <= d[start'];
                { lemma_mul_inequality_forall(); lemma_mul_is_commutative_forall(); }
                span * (d[n1 + 1] + 1) <= span * d[start'];
                { lemma_mul_is_distributive_forall(); }
                span * d[n1 + 1] + span <= span * d[start'];
            }
            assert sat(n2, nextbefore(goal, timefun[start'] + span * d[start'], timefun));
            assert sat(n2, and(goal, next(before(timefun[start'] + span * d[start'], timefun))));
        }
    }

    // If   []t :: <span>(goal || d' < d[t]')
    // and  [](1 <= d)
    // then []<span * d>(goal)
    lemma Lemma_EventuallynextWithinSpans(start:int, d:imap<int, int>, goal:temporal, span:int, timefun:imap<int, int>)
        requires imaptotal(d);
        requires imaptotal(timefun);
        requires 1 <= span;
        requires forall i :: start <= i ==> 1 <= d[i];
        requires sat(start, always(nextOrDecreaseWithin(goal, d, span, timefun)));
        ensures  sat(start, always(eventuallynextwithinspans(d, goal, span, timefun)));
    {
        TemporalAssist();
        forall start' | TLe(start, start')
            ensures sat(start', eventuallynextwithin(goal, span * d[start'], timefun));
        {
            Lemma_EventuallynextWithinSpansHelper(start, start', d, goal, span, timefun);
        }
    }

    // If   []<span * d>(goal)
    // and  [](d <= n)
    // then []<span * n>(goal)
    lemma Lemma_EventuallynextWithinBound(start:int, d:imap<int, int>, n:int, goal:temporal, span:int, timefun:imap<int, int>)
        requires imaptotal(d);
        requires imaptotal(timefun);
        requires forall i :: d[i] <= n;
        requires 0 <= span;
        requires sat(start, always(eventuallynextwithinspans(d, goal, span, timefun)));
        ensures  sat(start, always(eventuallynextwithin(goal, span * n, timefun)));
    {
        TemporalAssist();
        forall i1 | TLe(start, i1)
            ensures sat(i1, eventuallynextwithin(goal, span * n, timefun));
        {
            lemma_mul_inequality_forall();
            lemma_mul_is_commutative_forall();
            assert span * d[i1] <= span * n;
        }
    }

    lemma Lemma_EventuallynextWithinImpliesEventuallynext(i:int, x:temporal, span:int, timefun:imap<int, int>)
        requires imaptotal(timefun);
        requires sat(i, eventuallynextwithin(x, span, timefun));
        ensures  sat(i, eventual(x));
    {
        TemporalAssist();
    }

    lemma Lemma_AlwaysEventuallyWithinMeansAlwaysEventuallyWithinAfter(i:int, action:temporal, wait:int, span:int, timefun:imap<int, int>) returns (step:int)
        requires imaptotal(timefun);
        requires monotonic_from(0, timefun);
        requires wait >= 0;
        requires span >= 0;
        requires forall rt :: sat(0, eventual(after(rt, timefun)));
        requires sat(i, always(eventuallynextwithin(action, span, timefun)));
        requires 0 <= i;
        ensures  i <= step;
        ensures  sat(step, and(nextbefore(action, timefun[i] + wait + span, timefun),
                               next(after(timefun[i] + wait, timefun))));
        ensures  sat(i, eventual(and(nextbefore(action, timefun[i] + wait + span, timefun),
                                     next(after(timefun[i] + wait, timefun)))));
    {
        var rt1 := timefun[i] + wait;
        var rt2 := timefun[i] + wait + span;
        var j := eventualStep(0, after(rt1, timefun));
        Lemma_MonotonicFromImpliesMonotonicFromLater(0, i, timefun);
        if (j < i)
        {
            j := i;
        }
        var k := stepattimeboundary(i, j, rt1, timefun);
        TemporalDeduceFromAlways(i, k, eventuallynextwithin(action, span, timefun));
        step := eventualStep(k, nextbefore(action, timefun[k] + span, timefun));
        TemporalEventually(i, step, and(nextbefore(action, rt2, timefun),
                                        next(after(rt1, timefun))));
    }

    lemma Lemma_AlwaysEventuallyWithinImpliesAfter(i:int, j:int, action:temporal, span:int, timefun:imap<int, int>, rt:int) returns (step:int)
        requires imaptotal(timefun);
        requires monotonic_from(0, timefun);
        requires span >= 0;
        requires forall t :: sat(0, eventual(after(t, timefun)));
        requires sat(i, always(eventuallynextwithin(action, span, timefun)));
        requires 0 <= i <= j;
        ensures  j <= step;
        ensures  sat(step, action);
        ensures  rt <= timefun[step+1];
    {
        assert sat(0, eventual(after(rt, timefun)));
        var k := TemporalDeduceFromEventual(0, after(rt, timefun));
        if k < j
        {
            assert rt <= timefun[k] <= timefun[j];
            k := j;
        }
        TemporalDeduceFromAlways(i, k, eventuallynextwithin(action, span, timefun));
        step := TemporalDeduceFromEventual(k, nextbefore(action, timefun[k] + span, timefun));
    }

    lemma Lemma_UntilAbsoluteTimeImpliesUntilEarlierTime(i:int, x:temporal, t1:int, t2:int, timefun:imap<int, int>)
        requires imaptotal(timefun);
        requires monotonic_from(i, timefun);
        requires sat(i, untilabsolutetime(x, t1, timefun));
        requires t2 <= t1;
        ensures  sat(i, untilabsolutetime(x, t2, timefun));
    {
        TemporalAssist();
    }

    lemma Lemma_AlwaysUntilAbsoluteTimeImpliesAlwaysUntilEarlierTime(i:int, x:temporal, t1:int, t2:int, timefun:imap<int, int>)
        requires imaptotal(timefun);
        requires monotonic_from(i, timefun);
        requires sat(i, always(untilabsolutetime(x, t1, timefun)));
        requires t2 <= t1;
        ensures  sat(i, always(untilabsolutetime(x, t2, timefun)));
    {
        TemporalAssist();
    }

    lemma TemporalDeduceFromEventuallyWithin(i:int, x:temporal, span:int, timefun:imap<int, int>) returns (step:int)
        requires imaptotal(timefun);
        requires sat(i, eventuallywithin(x, span, timefun));
        ensures  i <= step;
        ensures  sat(step, beforeabsolutetime(x, timefun[i] + span, timefun));
    {
        step := TemporalDeduceFromEventual(i, beforeabsolutetime(x, timefun[i] + span, timefun));
    }

    lemma TemporalDeduceFromEventuallyNextWithin(i:int, x:temporal, span:int, timefun:imap<int, int>) returns (step:int)
        requires imaptotal(timefun);
        requires sat(i, eventuallynextwithin(x, span, timefun));
        ensures  i <= step;
        ensures  sat(step, nextbefore(x, timefun[i] + span, timefun));
    {
        step := TemporalDeduceFromEventual(i, nextbefore(x, timefun[i] + span, timefun));
    }

    lemma TemporalDeduceFromAlwaysWithin(i:int, j:int, x:temporal, span:int, timefun:imap<int, int>)
        requires imaptotal(timefun);
        requires sat(i, alwayswithin(x, span, timefun));
        requires i <= j;
        requires sat(j, before(timefun[i] + span, timefun));
        ensures  sat(j, x);
    {
        TemporalDeduceFromAlways(i, j, untilabsolutetime(x, timefun[i] + span, timefun));
    }

    predicate{:opaque} monotonic_from_opaque(start:int, f:imap<int, int>)
    {
        forall i1, i2 :: i1 in f && i2 in f && start <= i1 <= i2 ==> f[i1] <= f[i2]
    }

    function{:opaque} actionGoalDecrease(i1:int, goal:temporal, d:imap<int, int>):temporal
        requires imaptotal(d);
        ensures  forall i {:trigger sat(i, actionGoalDecrease(i1, goal, d))} :: sat(i, actionGoalDecrease(i1, goal, d)) <==>
                    (0 < d[i + 1] && d[i + 1] < d[i1]) || sat(i, goal) || (d[i1] == 0);
    {
        TemporalAssist();
        stepmap(imap i :: (0 < d[i + 1] && d[i + 1] < d[i1]) || sat(i, goal) || (d[i1] == 0))
    }

    function{:opaque} actionGoalDecreaseWithin(goal:temporal, d:imap<int, int>, span:int, timefun:imap<int, int>):temporal
        requires imaptotal(d);
        requires imaptotal(timefun);
        ensures  forall i {:trigger sat(i, actionGoalDecreaseWithin(goal, d, span, timefun))} :: sat(i, actionGoalDecreaseWithin(goal, d, span, timefun)) <==>
                    sat(i, eventuallynextwithin(actionGoalDecrease(i, goal, d), span, timefun));
    {
        TemporalAssist();
        stepmap(imap i :: sat(i, eventuallynextwithin(actionGoalDecrease(i, goal, d), span, timefun)))
    }

    // If   []t :: <span>((0 < d' < d[t]') || goal || (d[t]' == 0))
    // and  [](0 <= d)
    // and  1 <= d
    // then <span * d>(goal)
    lemma Lemma_EventuallyNextGoalSpans(start:int, d:imap<int, int>, goal:temporal, span:int, timefun:imap<int, int>)
        requires imaptotal(d);
        requires imaptotal(timefun);
        requires 1 <= span;
        requires 1 <= d[start];
        requires forall i :: start <= i ==> 0 <= d[i];
        requires sat(start, always(actionGoalDecreaseWithin(goal, d, span, timefun)));
        ensures  sat(start, eventuallynextwithinspans(d, goal, span, timefun));
        decreases d[start];
    {
        TemporalAssist();
        assert sat(start, actionGoalDecreaseWithin(goal, d, span, timefun));
        var i1 {:trigger TLe(start, i1)} :|
            TLe(start, i1) && sat(i1, actionGoalDecrease(start, goal, d)) && timefun[i1 + 1] <= timefun[start] + span;
        if (sat(i1, goal))
        {
            calc
            {
                1 <= d[start];
                { lemma_mul_inequality(1, d[start], span); }
                span * 1 <= span * d[start];
            }
            assert sat(start, eventuallynextwithinspans(d, goal, span, timefun));
        }
        else
        {
            Lemma_EventuallyNextGoalSpans(i1 + 1, d, goal, span, timefun);
            var i2 {:trigger TLe(i1 + 1, i2)} :| TLe(i1 + 1, i2)
                && sat(i2, and(goal, next(before(timefun[i1 + 1] + span * d[i1 + 1], timefun))));
            calc
            {
                d[i1 + 1] + 1 <= d[start];
                { lemma_mul_inequality_forall(); lemma_mul_is_commutative_forall(); }
                span * (d[i1 + 1] + 1) <= span * d[start];
                { lemma_mul_is_distributive_forall(); }
                span * d[i1 + 1] + span <= span * d[start];
            }
            assert sat(i2, nextbefore(goal, timefun[start] + span * d[start], timefun));
            assert sat(i2, and(goal, next(before(timefun[start] + span * d[start], timefun))));
        }
    }

    function {:opaque} ActionIsInstantaneousTemporal(x:temporal, timefun:imap<int, int>):temporal
        requires imaptotal(timefun);
        ensures  forall i {:trigger sat(i, ActionIsInstantaneousTemporal(x, timefun))} ::
                 sat(i, ActionIsInstantaneousTemporal(x, timefun)) <==> (sat(i, x) ==> timefun[i] == timefun[i+1]);
    {
        stepmap(imap i :: sat(i, x) ==> timefun[i] == timefun[i+1])
    }

    // "x" happens at most "count" times in all periods no longer than "span"
    function{:opaque} countWithinLe(count:int, x:temporal, span:int, timefun:imap<int, int>):temporal
        requires imaptotal(timefun);
        ensures  forall i1 {:trigger sat(i1, countWithinLe(count, x, span, timefun))} :: sat(i1, countWithinLe(count, x, span, timefun))
                    <==> (forall i2 :: TLe(i1, i2) && timefun[i2] <= timefun[i1] + span ==> countWithin(i1, i2, x) <= count);
    {
        TemporalAssist();
        stepmap(imap i1 :: forall i2 :: TLe(i1, i2) && timefun[i2] <= timefun[i1] + span ==> countWithin(i1, i2, x) <= count)
    }

    // "x" happens at least "count" times in a period no longer than "span"
    function{:opaque} countWithinGe(count:int, x:temporal, span:int, timefun:imap<int, int>):temporal
        requires imaptotal(timefun);
        ensures  forall i1 {:trigger sat(i1, countWithinGe(count, x, span, timefun))} :: sat(i1, countWithinGe(count, x, span, timefun))
                    <==> (exists i2 :: TLe(i1, i2) && timefun[i2] <= timefun[i1] + span && countWithin(i1, i2, x) >= count);
    {
        TemporalAssist();
        stepmap(imap i1 :: exists i2 :: TLe(i1, i2) && timefun[i2] <= timefun[i1] + span && countWithin(i1, i2, x) >= count)
    }

    lemma Lemma_CountWithinLeMultiple(start:int, n:nat, count:int, x:temporal, span:int, timefun:imap<int, int>)
        requires imaptotal(timefun);
        requires monotonic_from_opaque(start, timefun);
        requires 1 <= n;
        requires 0 <= span;
        requires sat(start, always(ActionIsInstantaneousTemporal(x, timefun)));
        requires sat(start, always(countWithinLe(count, x, span, timefun)));
        ensures  sat(start, always(countWithinLe(count * n, x, span * n, timefun)));
        decreases n;
    {
        TemporalAssist();
        reveal_monotonic_from_opaque();
        forall i1 | TLe(start, i1)
            ensures sat(i1, countWithinLe(count * n, x, span * n, timefun));
        {
            if (n > 1)
            {
                forall i3 | TLe(i1, i3) && timefun[i3] <= timefun[i1] + span * n
                    ensures countWithin(i1, i3, x) <= count * n;
                {
                    Lemma_CountWithinLeMultiple(i1, n - 1, count, x, span, timefun);
                    assert sat(i1, countWithinLe(count * (n - 1), x, span * (n - 1), timefun));
                    assert forall i2 :: TLe(i1, i2) && timefun[i2] <= timefun[i1] + span * (n - 1) ==> countWithin(i1, i2, x) <= count * (n - 1);
                    if (exists i2' :: TLe(i1, i2') && TLe(i2', i3) && timefun[i2'] > timefun[i1] + span * (n - 1))
                    {
                        var f := imap i2' :: TLe(i2', i3) && timefun[i2'] > timefun[i1] + span * (n - 1);
                        var i2' := earliestStep(i1, stepmap(f));
                        lemma_mul_nonnegative(span, n-1);
                        var i2 := i2' - 1;
                        assert !sat(i2, stepmap(f));
                        TemporalDeduceFromAlways(i1, i2, ActionIsInstantaneousTemporal(x, timefun));
                        assert !sat(i2, x);
                        forall ensures 0 <= span * (n - 1) { lemma_mul_nonnegative(span, n - 1); }
                        assert TLe(i1, i2');
                        assert TLe(i1, i2);
                        assert TLe(i2, i3);
                        assert forall i :: i1 <= i <= i2 ==> !sat(i, stepmap(f));
                        assert forall i :: sat(i, stepmap(f)) == (TLe(i, i3) && timefun[i] > timefun[i1] + span * (n - 1));
                        assert forall i :: i1 <= i <= i2 ==> !(TLe(i, i3) && timefun[i] > timefun[i1] + span * (n - 1));
                        assert !(TLe(i2, i3) && timefun[i2] > timefun[i1] + span * (n - 1));
                        assert countWithin(i1, i2, x) <= count * (n - 1);

                        assert sat(i2', countWithinLe(count, x, span, timefun));
                        assert TLe(i2', i3) && timefun[i3] <= timefun[i2'] + span ==> countWithin(i2', i3, x) <= count;
                        forall
                            ensures span + span * (n - 1) == span * n;
                            ensures count + count * (n - 1) == count * n;
                        {
                            lemma_mul_auto();
                        }
                        assert countWithin(i2', i3, x) <= count;

                        assert actionsWithin(i1, i3, x) == actionsWithin(i1, i2, x) + actionsWithin(i2', i3, x);
                        assert |actionsWithin(i1, i3, x)| >= |actionsWithin(i1, i2, x)| + |actionsWithin(i2', i3, x)|;
                    }
                    else
                    {
                        assert forall i2' :: TLe(i1, i2') && TLe(i2', i3) ==> timefun[i2'] <= timefun[i1] + span * (n - 1);
                        assert timefun[i3] <= timefun[i1] + span * (n - 1);
                        assert countWithin(i1, i3, x) <= count * (n - 1);
                        forall ensures count * (n - 1) <= count * n; { lemma_mul_auto(); }
                    }
                }
            }
        }
    }

    lemma Lemma_CountWithinGeMultiple(start:int, n:nat, count:int, x:temporal, span:int, timefun:imap<int, int>)
        requires imaptotal(timefun);
        requires monotonic_from_opaque(start, timefun);
        requires 1 <= n;
        requires 0 <= span;
        requires sat(start, always(countWithinGe(count, x, span, timefun)));
        ensures  sat(start, always(countWithinGe(count * n, x, span * n, timefun)));
        decreases n;
    {
        TemporalAssist();
        reveal_monotonic_from_opaque();
        forall i1 | TLe(start, i1)
            ensures sat(i1, countWithinGe(count * n, x, span * n, timefun));
        {
            if (n > 1)
            {
                assert sat(i1, countWithinGe(count, x, span, timefun));
                var i2 :| TLe(i1, i2) && timefun[i2] <= timefun[i1] + span && countWithin(i1, i2, x) >= count;
                Lemma_CountWithinGeMultiple(i2, n - 1, count, x, span, timefun);
                assert sat(i2, always(countWithinGe(count * (n - 1), x, span * (n - 1), timefun)));
                assert sat(i2, countWithinGe(count * (n - 1), x, span * (n - 1), timefun));
                var i3 :| TLe(i2, i3) && timefun[i3] <= timefun[i2] + span * (n - 1) && countWithin(i2, i3, x) >= count * (n - 1);
                assert TLe(i1, i3);
                assert actionsWithin(i1, i3, x) == actionsWithin(i1, i2, x) + actionsWithin(i2, i3, x);
                assert |actionsWithin(i1, i3, x)| >= |actionsWithin(i1, i2, x)| + |actionsWithin(i2, i3, x)|;
                forall
                    ensures span + span * (n - 1) == span * n;
                    ensures count + count * (n - 1) == count * n;
                {
                    lemma_mul_auto();
                }
            }
        }
    }

    lemma Lemma_CountWithinGeOne(start:int, x:temporal, span:int, timefun:imap<int, int>)
        requires imaptotal(timefun);
        requires 0 <= span;
        requires sat(start, always(eventuallynextwithin(x, span, timefun)));
        ensures  sat(start, always(countWithinGe(1, x, span, timefun)));
    {
        TemporalAssist();
        forall i1 | TLe(start, i1)
            ensures sat(i1, countWithinGe(1, x, span, timefun));
        {
            var i2 :| TLe(i1, i2) && sat(i2, nextbefore(x, timefun[i1] + span, timefun));
            var i2' := i2 + 1;
            assert i2 in actionsWithin(i1, i2', x);
            assert countWithin(i1, i2', x) >= 1;
        }
    }

    lemma{:timeLimitMultiplier 2} Lemma_CountIncrDecrHelper(i1:int, i2:int, d:imap<int, int>, nIncr:int, nDecr:int, incr:temporal, decr:temporal)
        requires imaptotal(d);
        requires i1 <= i2;
        requires countWithin(i1, i2, decr) >= nDecr;
        requires countWithin(i1, i2, incr) <= nIncr;
        requires forall i {:trigger TLe(i1, i)}{:trigger sat(i, incr)}{:trigger sat(i, decr)} :: TLe(i1, i) && TLe(i, i2) ==>
                        (sat(i, incr) && !sat(i, decr) && d[i + 1] == d[i] + 1)
                     || (!sat(i, incr) && sat(i, decr) && d[i + 1] < d[i])
                     || (!sat(i, incr) && !sat(i, decr) && d[i + 1] == d[i]);
        ensures  d[i2] <= d[i1] + nIncr - nDecr;
        decreases i2 - i1;
    {
        if (i1 == i2)
        {
            assert forall i :: i !in actionsWithin(i1, i2, decr);
            assert actionsWithin(i1, i2, decr) == {};
            assert countWithin(i1, i2, decr) == 0;
        }
        else
        {
            assert actionsWithin(i1, i2, incr) == actionsWithin(i1, i1 + 1, incr) + actionsWithin(i1 + 1, i2, incr);
            assert actionsWithin(i1, i2, decr) == actionsWithin(i1, i1 + 1, decr) + actionsWithin(i1 + 1, i2, decr);
            if (sat(i1, incr))
            {
                assert i1 in actionsWithin(i1, i2, incr);
                Lemma_CountIncrDecrHelper(i1 + 1, i2, d, nIncr - 1, nDecr, incr, decr);
            }
            else if (sat(i1, decr))
            {
                forall j | i1 <= j < i1 + 1 && sat(j, decr)
                    ensures j == i1;
                {
                }
                assert i1 in actionsWithin(i1, i1 + 1, decr);
                assert actionsWithin(i1, i1 + 1, decr) <= {i1};
                assert actionsWithin(i1, i1 + 1, decr) == {i1};
                Lemma_CountIncrDecrHelper(i1 + 1, i2, d, nIncr, nDecr - 1, incr, decr);
            }
            else
            {
                Lemma_CountIncrDecrHelper(i1 + 1, i2, d, nIncr, nDecr, incr, decr);
            }
        }
    }

    lemma Lemma_CountIncrDecr(i1:int, d:imap<int, int>, nIncr:int, nDecr:int, incr:temporal, decr:temporal, span:int, timefun:imap<int, int>)
        returns (i2:int)
        // |decr| >= nDecr
        // |incr| <= nIncr
        requires imaptotal(d);
        requires imaptotal(timefun);
        requires monotonic_from_opaque(i1, timefun);
        requires 0 <= span;
        requires sat(i1, countWithinLe(nIncr, incr, span, timefun));
        requires sat(i1, countWithinGe(nDecr, decr, span, timefun));
        requires forall i {:trigger TLe(i1, i)} :: TLe(i1, i) && timefun[i] <= timefun[i1] + span ==>
                        (sat(i, incr) && !sat(i, decr) && d[i + 1] == d[i] + 1)
                     || (!sat(i, incr) && sat(i, decr) && d[i + 1] < d[i])
                     || (!sat(i, incr) && !sat(i, decr) && d[i + 1] == d[i]);
        ensures  timefun[i2] <= timefun[i1] + span;
        ensures  sat(i2, stepmap(imap i :: d[i] <= d[i1] + nIncr - nDecr));
        ensures  sat(i1, alwayswithin(stepmap(imap i :: d[i] <= d[i1] + nIncr), span, timefun));
        ensures  nDecr > 0 ==> i2 > i1;
    {
        TemporalAssist();
        reveal_monotonic_from_opaque();
        i2 :| TLe(i1, i2) && timefun[i2] <= timefun[i1] + span && countWithin(i1, i2, decr) >= nDecr;
        assert TLe(i1, i2) && timefun[i2] <= timefun[i1] + span ==> countWithin(i1, i2, incr) <= nIncr;

        assert countWithin(i1, i2, decr) >= nDecr;
        assert countWithin(i1, i2, incr) <= nIncr;
        Lemma_CountIncrDecrHelper(i1, i2, d, nIncr, nDecr, incr, decr);
        assert d[i2] <= d[i1] + nIncr - nDecr;

        var f1 := imap i :: d[i] <= d[i1] + nIncr - nDecr;
        assert sat(i2, stepmap(f1));
        assert sat(i1, eventuallywithin(stepmap(f1), span, timefun));

        var f2 := imap i :: d[i] <= d[i1] + nIncr;
        forall i | TLe(i1, i) && timefun[i] <= timefun[i1] + span
            ensures f2[i];
        {
            Lemma_CountIncrDecrHelper(i1, i, d, nIncr, countWithin(i1, i, decr), incr, decr);
            assert d[i] <= d[i1] + nIncr;
        }
        assert sat(i1, alwayswithin(stepmap(f2), span, timefun));
    }

    lemma Lemma_CountIncrHelper(i1:int, i2:int, d:imap<int, int>, nIncr:int, incr:temporal)
        requires imaptotal(d);
        requires i1 <= i2;
        requires countWithin(i1, i2, incr) <= nIncr;
        requires forall i {:trigger TLe(i1, i)}{:trigger sat(i, incr)} :: TLe(i1, i) && TLe(i, i2) ==>
                        (sat(i, incr) && d[i + 1] == d[i] + 1)
                     || (!sat(i, incr) && d[i + 1] <= d[i])
        ensures  d[i2] <= d[i1] + nIncr;
        decreases i2 - i1;
    {
        if (i1 != i2)
        {
            assert actionsWithin(i1, i2, incr) == actionsWithin(i1, i1 + 1, incr) + actionsWithin(i1 + 1, i2, incr);
            if (sat(i1, incr))
            {
                assert i1 in actionsWithin(i1, i2, incr);
                Lemma_CountIncrHelper(i1 + 1, i2, d, nIncr - 1, incr);
            }
            else
            {
                Lemma_CountIncrHelper(i1 + 1, i2, d, nIncr, incr);
            }
        }
    }

    lemma Lemma_CountIncr(i1:int, d:imap<int, int>, nIncr:int, incr:temporal, span:int, timefun:imap<int, int>)
        // |incr| <= nIncr
        requires imaptotal(d);
        requires imaptotal(timefun);
        requires monotonic_from_opaque(i1, timefun);
        requires 0 <= span;
        requires sat(i1, countWithinLe(nIncr, incr, span, timefun));
        requires forall i {:trigger TLe(i1, i)} :: TLe(i1, i) && timefun[i] <= timefun[i1] + span ==>
                        (sat(i, incr) && d[i + 1] == d[i] + 1)
                     || (!sat(i, incr) && d[i + 1] <= d[i])
        ensures  sat(i1, alwayswithin(stepmap(imap i :: d[i] <= d[i1] + nIncr), span, timefun));
    {
        TemporalAssist();
        reveal_monotonic_from_opaque();

        var f2 := imap i :: d[i] <= d[i1] + nIncr;
        forall i | TLe(i1, i) && timefun[i] <= timefun[i1] + span
            ensures f2[i];
        {
            Lemma_CountIncrHelper(i1, i, d, nIncr, incr);
            assert d[i] <= d[i1] + nIncr;
        }
        assert sat(i1, alwayswithin(stepmap(f2), span, timefun));
    }

} 
