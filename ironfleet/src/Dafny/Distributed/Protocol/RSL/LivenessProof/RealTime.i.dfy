include "../DistributedSystem.i.dfy"
include "Environment.i.dfy"
include "../CommonProof/Constants.i.dfy"
include "../../../Common/Logic/Temporal/Induction.i.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"
include "../../../Common/Logic/Temporal/WF1.i.dfy"

module LivenessProof__RealTime_i {
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Environment_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened Collections__Maps2_s
import opened Collections__Maps2_i
import opened Temporal__Temporal_s
import opened Temporal__Induction_i
import opened Temporal__Rules_i
import opened Temporal__Time_s
import opened Temporal__Time_i
import opened Temporal__WF1_i
import opened EnvironmentSynchrony_s

lemma lemma_TimeAdvancesBetween(b:Behavior<RslState>, asp:AssumptionParameters, i:int, j:int)
  requires LivenessAssumptions(b, asp)
  requires 0 <= i <= j
  ensures  PaxosTimeMap(b)[i] <= PaxosTimeMap(b)[j]
  decreases j - i
{
  if j > i
  {
    lemma_TimeAdvancesBetween(b, asp, i, j-1);
    lemma_AssumptionsMakeValidTransition(b, asp.c, j-1);
  }
}

predicate TimeMonotonicFromInvariant(b:Behavior<RslState>, asp:AssumptionParameters, i:int)
  requires imaptotal(b)
  requires imaptotal(PaxosTimeMap(b))
{
  monotonic_from(i, PaxosTimeMap(b))
}

lemma lemma_TimeMonotonicFromInvariantHolds(b:Behavior<RslState>, asp:AssumptionParameters, i:int)
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  ensures  TimeMonotonicFromInvariant(b, asp, i)
{
  forall j, k | i <= j <= k
  {
    lemma_TimeAdvancesBetween(b, asp, j, k);
  }
}

lemma lemma_AfterForm(b:Behavior<RslState>, asp:AssumptionParameters)
  requires LivenessAssumptions(b, asp)
  ensures  TimeNotZeno(PaxosTimeMap(b))
{
  var timefun := PaxosTimeMap(b);
  var eb := RestrictBehaviorToEnvironment(b);

  reveal eventual();
  reveal after();

  forall t
    ensures sat(0, eventual(after(t, timefun)))
  {
    var x := TimeReachesTemporal(eb, t);
    var i := eventualStep(0, x);
    TemporalEventually(0, i, after(t, timefun));
  }

  assert forall t :: sat(0, eventual(after(t, timefun)));
  assert forall t :: sat(0, eventual(after(t, PaxosTimeMap(b))));
}

lemma lemma_TimeReachesAfter(b:Behavior<RslState>, asp:AssumptionParameters, i:int, rt:int) returns (j:int)
  requires LivenessAssumptions(b, asp)
  ensures  i <= j
  ensures  b[j].environment.time >= rt
{
  var eb := RestrictBehaviorToEnvironment(b);
  var x := TimeReachesTemporal(eb, rt);
  assert sat(0, eventual(x));
  j := TemporalDeduceFromEventual(0, x);
  assert b[j].environment.time >= rt;
  if i > j
  {
    lemma_TimeAdvancesBetween(b, asp, j, i);
    j := i;
  }
}

} 
