include "Temporal.s.dfy"
include "Heuristics.i.dfy"
include "Rules.i.dfy"

module Temporal__Induction_i {
import opened Temporal__Temporal_s
import opened Temporal__Heuristics_i
import opened Temporal__Rules_i

lemma TemporalInductionNextPartial(i1:int, i2:int, x:temporal)
  requires sat(i1, x)
  requires forall j :: i1 <= j ==> sat(j, imply(x, next(x)))
  ensures  forall j :: i1 <= j <= i2 ==> sat(j, x)
  decreases i2 - i1
{
  TemporalAssist();
  if (i1 < i2)
  {
    assert sat(i1, always(imply(x, next(x))));
    assert sat(i1, imply(x, next(x)));
    TemporalInductionNextPartial(nextstep(i1), i2, x);
  }
}

lemma TemporalInductionNext(i:int, x:temporal)
  requires sat(i, x)
  requires forall j :: i <= j ==> sat(j, imply(x, next(x)))
  ensures  sat(i, always(x))
{
  TemporalAssist();
  forall k | i <= k
    ensures sat(k, x)
  {
    reveal imply();
    reveal next();
    TemporalInductionNextPartial(i, k, x);
  }
  assert sat(i, always(x));
}

lemma TemporalInductionPartial(i1:int, i2:int, x:temporal)
  requires sat(i1, x)
  requires sat(i1, always(stepmap(imap j :: sat(j, x) ==> sat(nextstep(j), x))))
  ensures  forall j :: i1 <= j <= i2 ==> sat(j, x)
  decreases i2 - i1
{
  TemporalAssist();
  if (i1 < i2)
  {
    assert sat(i1, stepmap(imap j :: sat(j, x) ==> sat(nextstep(j), x)));
    TemporalInductionPartial(nextstep(i1), i2, x);
  }
}
    
// A && [](A ==> ()A) ==> []A
lemma TemporalInduction(i:int, x:temporal)
  requires sat(i, x)
  requires sat(i, always(stepmap(imap j :: sat(j, x) ==> sat(nextstep(j), x))))
  ensures  sat(i, always(x))
{
  assert sat(i, always(stepmap(imap j :: sat(j, x) ==> sat(nextstep(j), x))));
  TemporalAssist();
  forall j | i <= j
    ensures sat(j, x)
  {
    TemporalInductionPartial(i, j, x);
  }
}

lemma TemporalInductionNextWithInvariantPartial(i1:int, i2:int, x:temporal, inv:temporal)
  requires sat(i1, x)
  requires sat(i1, always(inv))
  requires sat(i1, always(imply(and(x, inv), next(x))))
  ensures  forall j :: i1 <= j <= i2 ==> sat(j, x)
  decreases i2 - i1
{
  TemporalAssist();
  if (i1 < i2)
  {
    assert sat(i1, always(imply(and(x, inv), next(x))));
    assert sat(i1, imply(and(x, inv), next(x)));
    assert sat(i1, imply(x, next(x)));
    TemporalInductionNextWithInvariantPartial(nextstep(i1), i2, x, inv);
  }
}

lemma TemporalInductionNextWithInvariant(i:int, x:temporal, inv:temporal)
  requires sat(i, x)
  requires sat(i, always(inv))
  requires sat(i, always(imply(and(x, inv), next(x))))
  ensures  sat(i, always(x))
{
  assert sat(i, always(imply(and(x, inv), next(x))));
  TemporalAssist();
  forall j | i <= j
    ensures sat(j, x)
  {
    TemporalInductionNextWithInvariantPartial(i, j, x, inv);
  }
  assert sat(i, always(x));
}

} 
