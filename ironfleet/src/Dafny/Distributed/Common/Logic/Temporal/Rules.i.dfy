include "Heuristics.i.dfy"

module Temporal__Rules_i {
import opened Temporal__Heuristics_i

///////////////////
// DEFINITIONS
///////////////////
    
    function{:opaque} eventualStep(start:int, x:temporal):int
        requires sat(start, eventual(x));
        ensures  sat(eventualStep(start, x), x);
        ensures  TLe(start, eventualStep(start, x));
    {
        TemporalAssist();
        var end :| TLe(start, end) && sat(end, x);
        end
    }

    function{:opaque} earliestStepBetween(start:int, end:int, x:temporal):int
        requires sat(end, x);
        requires TLe(start, end);
        ensures  sat(earliestStepBetween(start, end, x), x);
        ensures  TLe(start, earliestStepBetween(start, end, x));
        ensures  TLe(earliestStepBetween(start, end, x), end);
        ensures  forall i :: start <= i < earliestStepBetween(start, end, x) ==> !sat(i, x);
        decreases end - start;
    {
        if (sat(start, x)) then start
        else earliestStepBetween(start + 1, end, x)
    }

    function{:opaque} earliestStep(start:int, x:temporal):int
        requires sat(start, eventual(x));
        ensures  sat(earliestStep(start, x), x);
        ensures  TLe(start, earliestStep(start, x));
        ensures  forall i :: start <= i < earliestStep(start, x) ==> !sat(i, x);
    {
        earliestStepBetween(start, eventualStep(start, x), x)
    }

///////////////////
// LEMMAS
///////////////////

    // []A ==> A
    // <>A <== A
    lemma TemporalNow(i:int, x:temporal)
        ensures  sat(i, always(x)) ==> sat(i, x);
        ensures  sat(i, eventual(x)) <== sat(i, x);
    {
        TemporalAssist();
    }
    
    // [][]A = []A
    // <><>A = <>A
    lemma TemporalIdempotent(i:int, x:temporal)
        ensures  sat(i, always(always(x))) == sat(i, always(x));
        ensures  sat(i, eventual(eventual(x))) == sat(i, eventual(x));
    {
        TemporalAssist();
    }
    
    // <>[]A ==> []<>A
    lemma TemporalEventuallyAlwaysImpliesAlwaysEventually(i:int, x:temporal)
        ensures  sat(i, eventual(always(x))) ==> sat(i, always(eventual(x)));
    {
        TemporalBlast();
    }
    
    // <>!A = ![]A
    // []!A = !<>A
    lemma TemporalNot(i:int, x:temporal)
        ensures  sat(i, eventual(not(x))) <==> !sat(i, always(x));
        ensures  sat(i, always(not(x))) <==> !sat(i, eventual(x));
    {
        TemporalAssist();
    }
    
    // [](A&&B) = []A && []B
    // <>(A&&B) ==> <>A && <>B
    // <>(A&&B) <== []A && <>B
    // <>(A&&B) <== <>A && []B
    lemma TemporalAnd(i:int, x:temporal, y:temporal)
        ensures  sat(i, always(and(x, y))) <==> sat(i, always(x)) && sat(i, always(y));
        ensures  sat(i, eventual(and(x, y))) ==> sat(i, eventual(x)) && sat(i, eventual(y));
        ensures  sat(i, eventual(and(x, y))) <== sat(i, always(x)) && sat(i, eventual(y));
        ensures  sat(i, eventual(and(x, y))) <== sat(i, eventual(x)) && sat(i, always(y));
    {
        TemporalAssist();
    }
    
    // [](A||B) <== []A || []B
    // [](A||B) ==> []A || <>B
    // [](A||B) ==> <>A || []B
    // <>(A||B) = <>A || <>B
    lemma TemporalOr(i:int, x:temporal, y:temporal)
        ensures  sat(i, always(or(x, y))) <== sat(i, always(x)) || sat(i, always(y));
        ensures  sat(i, always(or(x, y))) ==> sat(i, always(x)) || sat(i, eventual(y));
        ensures  sat(i, always(or(x, y))) ==> sat(i, eventual(x)) || sat(i, always(y));
        ensures  sat(i, eventual(or(x, y))) <==> sat(i, eventual(x)) || sat(i, eventual(y));
    {
        TemporalAssist();
    }
    
    // [](A==>B) ==> ([]A ==> []B)
    // [](A==>B) ==> (<>A ==> <>B)
    // [](A==>B) <== (<>A ==> []B)
    // <>(A==>B) = ([]A ==> <>B)
    lemma TemporalImply(i:int, x:temporal, y:temporal)
        ensures  sat(i, always(imply(x, y))) ==> (sat(i, always(x)) ==> sat(i, always(y)));
        ensures  sat(i, always(imply(x, y))) ==> (sat(i, eventual(x)) ==> sat(i, eventual(y)));
        ensures  sat(i, always(imply(x, y))) <== (sat(i, eventual(x)) ==> sat(i, always(y)));
        ensures  sat(i, eventual(imply(x, y))) <==> (sat(i, always(x)) ==> sat(i, eventual(y)));
    {
        TemporalAssist();
    }
    
    lemma TemporalAlways(i:int, x:temporal)
        requires forall j :: i <= j ==> sat(j, x);
        ensures  sat(i, always(x));
    {
        TemporalAssist();
        assert forall j :: TLe(i, j) ==> sat(j, x);
    }

    lemma TemporalEventually(i1:int, i2:int, x:temporal)
        requires i1 <= i2;
        requires sat(i2, x);
        ensures  sat(i1, eventual(x));
    {
        TemporalAssist();
    }
    
    lemma ValidAlways(i:int, x:temporal)
        requires (forall j:int :: sat(j, x));
        ensures  sat(i, always(x));
    {
        TemporalAssist();
    }
    
    lemma ValidImply(i:int, x:temporal, y:temporal)
        requires (forall j:int :: sat(j, x) ==> sat(j, y));
        ensures  sat(i, always(x)) ==> sat(i, always(y));
        ensures  sat(i, eventual(x)) ==> sat(i, eventual(y));
    {
        TemporalAssist();
    }
    
    lemma ValidEquiv(i:int, x:temporal, y:temporal)
        requires (forall j:int :: sat(j, x) <==> sat(j, y));
        ensures  sat(i, always(x)) <==> sat(i, always(y));
        ensures  sat(i, eventual(x)) <==> sat(i, eventual(y));
    {
        TemporalAssist();
    }

    lemma TemporalDeduceFromAlways(i:int, j:int, x:temporal)
        requires i <= j;
        requires sat(i, always(x));
        ensures  sat(j, x);
    {
        TemporalAssist();
        assert TLe(i, j);
    }

    lemma TemporalDeduceFromEventual(i:int, x:temporal) returns (j:int)
        requires sat(i, eventual(x));
        ensures  i <= j;
        ensures  sat(j, x);
    {
        TemporalAssist();
        j :| TLe(i, j) && sat(j, x);
    }
    
    lemma Lemma_EventuallyAlwaysImpliesLaterEventuallyAlways(
        i:int,
        j:int,
        x:temporal
        )
        requires i <= j;
        requires sat(i, eventual(always(x)));
        ensures  sat(j, eventual(always(x)));
    {
        TemporalAssist();
        var k :| TLe(i, k) && sat(k, always(x));
        var l := if k > j then k else j;
        assert TLe(k, l) && TLe(j, l);
    }

    lemma Lemma_AlwaysImpliesLaterAlways(
        i:int,
        j:int,
        x:temporal
        )
        requires i <= j;
        ensures  sat(i, always(x)) ==> sat(j, always(x));
    {
        TemporalAssist();
        assert TLe(i, j);
    }

    lemma Lemma_EventuallyNowButNotNextMeansNow(x:temporal, i:int)
        ensures sat(i, eventual(x)) && !sat(i+1, eventual(x)) ==> sat(i, x);
    {
        TemporalAssist();
    }

    lemma Lemma_EventuallyImpliesEarlierEventually(
        i:int,
        j:int,
        x:temporal
        )
        requires i <= j;
        ensures  sat(j, eventual(x)) ==> sat(i, eventual(x));
    {
        TemporalAssist();
        assert TLe(i, j);
    }

    lemma TemporalAlwaysEventualImpliesAlwaysEventualWithDifferentStartPoint(i:int, j:int, x:temporal)
        ensures  sat(i, always(eventual(x))) ==> sat(j, always(eventual(x)));
    {
        TemporalAssist();
        
        if sat(i, always(eventual(x))) && i > j
        {
            assert sat(i, eventual(x));
        }
    }

} 
