include "../DistributedSystem.i.dfy"
include "../../../Common/Framework/HostQueueLemmas.i.dfy"
include "../../../Common/Logic/Temporal/Heuristics.i.dfy"
include "Assumptions.i.dfy"
include "../CommonProof/Constants.i.dfy"

module LivenessProof__Invariants_i {
import opened LiveRSL__DistributedSystem_i
import opened Liveness__HostQueueLemmas_i
import opened Temporal__Temporal_s
import opened Temporal__Heuristics_i
import opened Temporal__Rules_i
import opened LivenessProof__Assumptions_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened EnvironmentSynchrony_s

lemma lemma_HostQueuesNext(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  ensures  HostQueues_Next(b[i].environment, b[i+1].environment)
{
  TemporalDeduceFromAlways(0, i, HostQueuesNextTemporal(RestrictBehaviorToEnvironment(b)));
}

lemma lemma_LEnvironmentInvariantHolds(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  ensures  LEnvironmentInvariant(b[i].environment)
{
  if i == 0
  {
    Lemma_LEnvironmentInitEstablishesInvariant(b[i].environment);
  }
  else
  {
    lemma_LEnvironmentInvariantHolds(b, asp, i-1);
    lemma_AssumptionsMakeValidTransition(b, asp.c, i-1);
    lemma_HostQueuesNext(b, asp, i-1);

    Lemma_LEnvironmentNextPreservesInvariant(b[i-1].environment, b[i].environment);
  }
}

lemma lemma_OverflowProtectionNotUsedForReplica(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  ensures  OverflowProtectionNotUsedForReplica(b[i], idx, asp.c.params, asp.max_clock_ambiguity)
{
  TemporalDeduceFromAlways(0, i, OverflowProtectionNotUsedTemporal(b, asp.c.params, asp.max_clock_ambiguity));
}

} 
