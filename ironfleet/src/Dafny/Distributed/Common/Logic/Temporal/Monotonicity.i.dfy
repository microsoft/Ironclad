include "Heuristics.i.dfy"

module Temporal__Monotonicity_i {
import opened Temporal__Heuristics_i
import opened Temporal__Temporal_s
import opened Collections__Maps2_s
import opened Collections__Maps2_i

//////////////////
// DEFINITIONS
//////////////////

    function{:opaque} stepDecrease(start:int, d:imap<int, int>):temporal
        requires imaptotal(d);
        ensures  forall i {:trigger sat(i, stepDecrease(start, d))} :: sat(i, stepDecrease(start, d)) <==> d[i] < d[start];
    {
        TemporalAssist();
        stepmap(imap i :: d[i] < d[start])
    }

    function nextDecrease(start:int, d:imap<int, int>):temporal
        requires imaptotal(d);
    {
        next(stepDecrease(start, d))
    }

    function{:opaque} nextOrDecrease(goal:temporal, d:imap<int, int>):temporal
        requires imaptotal(d);
        ensures  forall i {:trigger sat(i, nextOrDecrease(goal, d))} :: sat(i, nextOrDecrease(goal, d)) <==>
                    sat(i, eventual(or(goal, nextDecrease(i, d))));
    {
        TemporalAssist();
        stepmap(imap i :: sat(i, eventual(or(goal, nextDecrease(i, d)))))
    }

//////////////////
// LEMMAS
//////////////////

    // If d decreases unless A, then <>A.
    lemma TemporalInductionOfEventuallyFromDecreasingFunction(i:int, x:temporal, d:imap<int, int>)
        requires imaptotal(d);
        requires forall j {:trigger sat(j, x)} :: i <= j ==> sat(j, x) || d[j+1] < d[j];
        requires forall j :: d[j] >= 0;
        ensures  sat(i, eventual(x));
        decreases d[i];
    {
        TemporalAssist();
        if (!sat(i, x))
        {
            TemporalInductionOfEventuallyFromDecreasingFunction(i + 1, x, d);
        }
    }

    lemma Lemma_MonotonicStepsLeadToMonotonicBehaviorPartial(i:int, f:imap<int, int>, j:int, k:int)
        requires imaptotal(f);
        requires sat(i, always(stepmap(imap u :: f[u] <= f[u+1])));
        requires i <= j <= k;
        ensures  f[j] <= f[k];
        decreases k - j;
    {
        TemporalAssist();
        if (k > j)
        {
            Lemma_MonotonicStepsLeadToMonotonicBehaviorPartial(i, f, j, k-1);
            assert TLe(i, k-1);
            assert sat(k-1, stepmap(imap a :: f[a] <= f[a+1]));
        }
    }

    // If f monotonically increases at each step, then it monotonically increases
    // across any pair of steps
    lemma Lemma_MonotonicStepsLeadToMonotonicBehavior(i:int, f:imap<int, int>)
        requires imaptotal(f);
        requires sat(i, always(stepmap(imap j :: f[j] <= f[j+1])));
        ensures  forall j, k :: i <= j <= k ==> f[j] <= f[k];
    {
        forall j, k | i <= j <= k
            ensures f[j] <= f[k];
        {
            Lemma_MonotonicStepsLeadToMonotonicBehaviorPartial(i, f, j, k);
        }
    }

    lemma Lemma_EventuallyNextHelper(start:int, start':int, d:imap<int, int>, goal:temporal)
        requires imaptotal(d);
        requires TLe(start, start');
        requires forall i :: start <= i ==> 0 <= d[i];
        requires sat(start, always(nextOrDecrease(goal, d)));
        ensures  sat(start', eventual(goal));
        decreases d[start'];
    {
        TemporalAssist();
        assert sat(start', nextOrDecrease(goal, d));
        var n1 {:trigger TLe(start', n1)} :|
            TLe(start', n1) && sat(n1, or(goal, nextDecrease(start', d)));
        if (!sat(n1, goal))
        {
            Lemma_EventuallyNextHelper(start, n1 + 1, d, goal);
        }
    }

    // If   []t :: <>(goal || d' < d[t]')
    // and  [](0 <= d)
    // then []<>(goal)
    lemma Lemma_EventuallyNext(start:int, d:imap<int, int>, goal:temporal)
        requires imaptotal(d);
        requires forall i :: start <= i ==> 0 <= d[i];
        requires sat(start, always(nextOrDecrease(goal, d)));
        ensures  sat(start, always(eventual(goal)));
    {
        TemporalAssist();
        forall start' | TLe(start, start')
            ensures sat(start', eventual(goal));
        {
            Lemma_EventuallyNextHelper(start, start', d, goal);
        }
    }

    lemma Lemma_MonotonicFromImpliesMonotonicFromLater(start1:int, start2:int, f:imap<int, int>)
        requires imaptotal(f);
        requires monotonic_from(start1, f);
        requires start1 <= start2;
        ensures  monotonic_from(start2, f);
    {
        forall i1, i2 | start2 <= i1 <= i2
            ensures f[i1] <= f[i2];
        {
            assert start1 <= i1 <= i2;
        }
    }

} 
