include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "RequestsReceived.i.dfy"
include "ViewSuspicion.i.dfy"
include "WF1.i.dfy"
include "../CommonProof/Actions.i.dfy"

module LivenessProof__EpochLength_i {
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Election_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__PacketHandling_i
import opened LivenessProof__RequestsReceived_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__ViewAdvance_i
import opened LivenessProof__ViewChange_i
import opened LivenessProof__ViewPropagation_i
import opened LivenessProof__ViewSuspicion_i
import opened LivenessProof__WF1_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened Temporal__Temporal_s
import opened Temporal__Rules_i
import opened Temporal__WF1_i
import opened Environment_s
import opened Collections__Maps2_s

predicate HostReadyToIncreaseEpochLength(
  ps:RslState,
  idx:int,
  epoch_length:int,
  epoch_end_time:int
  )
{
  && 0 <= idx < |ps.replicas|
  && var es := ps.replicas[idx].replica.proposer.election_state;
    && es.epoch_length == epoch_length
    && es.epoch_end_time == epoch_end_time
}

function{:opaque} HostReadyToIncreaseEpochLengthTemporal(
  b:Behavior<RslState>,
  idx:int,
  epoch_length:int,
  epoch_end_time:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, HostReadyToIncreaseEpochLengthTemporal(b, idx, epoch_length, epoch_end_time))} ::
               sat(i, HostReadyToIncreaseEpochLengthTemporal(b, idx, epoch_length, epoch_end_time))
               <==> HostReadyToIncreaseEpochLength(b[i], idx, epoch_length, epoch_end_time);
{
  stepmap(imap i :: HostReadyToIncreaseEpochLength(b[i], idx, epoch_length, epoch_end_time))
}

predicate EpochLengthEqualOrGreater(ps:RslState, idx:int, epoch_length:int)
{
  && 0 <= idx < |ps.replicas|
  && ps.replicas[idx].replica.proposer.election_state.epoch_length >= epoch_length
}

function{:opaque} EpochLengthEqualOrGreaterTemporal(b:Behavior<RslState>, idx:int, epoch_length:int):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, EpochLengthEqualOrGreaterTemporal(b, idx, epoch_length))} ::
             sat(i, EpochLengthEqualOrGreaterTemporal(b, idx, epoch_length)) == EpochLengthEqualOrGreater(b[i], idx, epoch_length)
{
  stepmap(imap i :: EpochLengthEqualOrGreater(b[i], idx, epoch_length))
}

lemma lemma_EpochLengthAtLeastInitialValue(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= idx < |asp.c.config.replica_ids|
  requires 0 <= i
  ensures  EpochLengthEqualOrGreater(b[i], idx, asp.c.params.baseline_view_timeout_period)
{
  lemma_ConstantsAllConsistent(b, asp.c, i);
  if i == 0
  {
    assert EpochLengthEqualOrGreater(b[i], idx, asp.c.params.baseline_view_timeout_period);
  }
  else
  {
    lemma_EpochLengthAtLeastInitialValue(b, asp, i-1, idx);
    lemma_ConstantsAllConsistent(b, asp.c, i-1);
    lemma_AssumptionsMakeValidTransition(b, asp.c, i-1);
    assert EpochLengthEqualOrGreater(b[i-1], idx, asp.c.params.baseline_view_timeout_period);
    if !EpochLengthEqualOrGreater(b[i], idx, asp.c.params.baseline_view_timeout_period)
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i-1, idx);
      lemma_OverflowProtectionNotUsedForReplica(b, asp, i-1, idx);
      assert false;
    }
  }
}

lemma lemma_EpochLengthNeverDecreases(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  idx:int,
  start_step:int,
  i:int,
  j:int
  )
  requires LivenessAssumptions(b, asp)
  requires idx in asp.live_quorum
  requires sat(start_step, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx)))
  requires 0 <= start_step <= i <= j
  ensures  0 <= idx < |b[i].replicas|
  ensures  0 <= idx < |b[j].replicas|
  ensures  b[i].replicas[idx].replica.proposer.election_state.epoch_length <= b[j].replicas[idx].replica.proposer.election_state.epoch_length
  decreases j - i
{
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, j);
    
  if j == i + 1
  {
    lemma_AssumptionsMakeValidTransition(b, asp.c, i);
    TemporalDeduceFromAlways(start_step, i, RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx));
    lemma_OverflowProtectionNotUsedForReplica(b, asp, i, idx);
//      assert OverflowProtectionNotUsed(b[i], idx, b[i].replicas[idx].replica.proposer.election_state.constants.all.params);
    lemma_EpochLengthAtLeastInitialValue(b, asp, i, idx);
    if b[i].replicas[idx].replica.proposer.election_state.epoch_length > b[j].replicas[idx].replica.proposer.election_state.epoch_length
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, idx);
      assert false;
    }
  }
  else if j > i + 1
  {
    lemma_EpochLengthNeverDecreases(b, asp, idx, start_step, i, i+1);
    lemma_EpochLengthNeverDecreases(b, asp, idx, start_step, i+1, j);
  }
}

lemma lemma_EpochLengthEventuallyIncreasesWF1Req1(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int,
  epoch_length:int
  )
  requires LivenessAssumptions(b, asp)
  requires idx in asp.live_quorum
  requires sat(i, RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx))
  requires 0 <= i
  ensures  var P := EpochLengthEqualOrGreaterTemporal(b, idx, epoch_length);
           var Q := EpochLengthEqualOrGreaterTemporal(b, idx, epoch_length + 1);
           sat(i, TemporalWF1Req1(P, Q))
{
  var P := EpochLengthEqualOrGreaterTemporal(b, idx, epoch_length);
  var Q := EpochLengthEqualOrGreaterTemporal(b, idx, epoch_length + 1);
  if sat(i, P) && !sat(i, Q) && !sat(i+1, P) && !sat(i+1, Q)
  {
    lemma_ConstantsAllConsistent(b, asp.c, i);
    lemma_ConstantsAllConsistent(b, asp.c, i+1);
    var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, idx);
    lemma_OverflowProtectionNotUsedForReplica(b, asp, i, idx);
    lemma_EpochLengthAtLeastInitialValue(b, asp, i, idx);
    assert false;
  }
}

lemma lemma_EpochLengthEventuallyIncreases(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  idx:int,
  start_step:int,
  i:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires processing_sync_start <= start_step <= i
  requires idx in asp.live_quorum
  requires sat(start_step, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx)))
  ensures  i <= step
  ensures  0 <= idx < |b[i].replicas|
  ensures  0 <= idx < |b[step].replicas|
  ensures  b[step].replicas[idx].replica.proposer.election_state.epoch_length > b[i].replicas[idx].replica.proposer.election_state.epoch_length
{
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_OverflowProtectionNotUsedForReplica(b, asp, i, idx);
  lemma_IsValidBallot(b, asp, i, idx);
  var epoch_length := b[i].replicas[idx].replica.proposer.election_state.epoch_length;
  var current_view := b[i].replicas[idx].replica.proposer.election_state.current_view;
  var nextView := ComputeSuccessorView(current_view, asp.c);
  lemma_IfPacketProcessingSynchronousThenAlways(b, asp, processing_sync_start, i, processing_bound);
  var intermediate_step, replica_index := lemma_SomeReplicaInLiveQuorumReachesView(b, asp, i, processing_bound, nextView);
  var advance_step := lemma_OneLiveReplicaSoonAdvancesAnother(b, asp, processing_sync_start, processing_bound, intermediate_step, replica_index, idx);
  lemma_ConstantsAllConsistent(b, asp.c, advance_step);

  var x := not(HostInViewTemporal(b, idx, current_view));
  var action_step := earliestStepBetween(i, advance_step, x) - 1;
  assert i <= action_step;
  lemma_ConstantsAllConsistent(b, asp.c, action_step);
  lemma_ConstantsAllConsistent(b, asp.c, action_step+1);
  assert !sat(action_step, x);

  var P := EpochLengthEqualOrGreaterTemporal(b, idx, epoch_length);
  var Q := EpochLengthEqualOrGreaterTemporal(b, idx, epoch_length + 1);

  forall j | i <= j
    ensures sat(j, TemporalWF1Req1(P, Q))
  {
    TemporalDeduceFromAlways(start_step, j, RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx));
    lemma_EpochLengthEventuallyIncreasesWF1Req1(b, asp, j, idx, epoch_length);
  }

  if !sat(action_step, imply(P, or(Q, next(Q))))
  {
    assert sat(action_step, P) && !sat(action_step, Q) && !sat(action_step+1, Q);
    var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, action_step, idx);
    lemma_OverflowProtectionNotUsedForReplica(b, asp, action_step, idx);
    lemma_EpochLengthAtLeastInitialValue(b, asp, action_step, idx);
    assert false;
  }

  step := TemporalWF1Specific(i, action_step, P, Q);
}

lemma lemma_EpochLengthEventuallyReaches(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  idx:int,
  start_step:int,
  epoch_length:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires processing_sync_start <= start_step
  requires idx in asp.live_quorum
  requires sat(start_step, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx)))
  ensures  step >= start_step
  ensures  0 <= idx < |b[step].replicas|
  ensures  b[step].replicas[idx].replica.proposer.election_state.epoch_length >= epoch_length
  decreases epoch_length
{
  lemma_ConstantsAllConsistent(b, asp.c, start_step);
  if epoch_length <= asp.c.params.baseline_view_timeout_period
  {
    lemma_EpochLengthAtLeastInitialValue(b, asp, start_step, idx);
    step := start_step;
  }
  else
  {
    var almost_step := lemma_EpochLengthEventuallyReaches(b, asp, processing_sync_start, processing_bound, idx, start_step, epoch_length - 1);
    Lemma_AlwaysImpliesLaterAlways(start_step, almost_step, RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx));
    step := lemma_EpochLengthEventuallyIncreases(b, asp, processing_sync_start, processing_bound, idx, start_step, almost_step);
  }
}

lemma lemma_EpochLengthForSomeEventuallyReaches(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  start_step:int,
  replica_indices:set<int>,
  epoch_length:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires processing_sync_start <= start_step
  requires replica_indices <= asp.live_quorum
  requires forall idx :: idx in replica_indices ==> sat(start_step, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx)))
  ensures  start_step <= step;
  ensures  forall idx :: idx in replica_indices ==> && 0 <= idx < |b[step].replicas|
                                             && b[step].replicas[idx].replica.proposer.election_state.epoch_length >= epoch_length
{
  if |replica_indices| == 0
  {
    step := start_step;
  }
  else
  {
    var some_index :| some_index in replica_indices;
    var other_indices := replica_indices - {some_index};
    var almost_step := lemma_EpochLengthForSomeEventuallyReaches(b, asp, processing_sync_start, processing_bound, start_step, other_indices, epoch_length);
    Lemma_AlwaysImpliesLaterAlways(start_step, almost_step, RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, some_index));
    step := lemma_EpochLengthEventuallyReaches(b, asp, processing_sync_start, processing_bound, some_index, almost_step, epoch_length);
    forall idx | idx in replica_indices
      ensures 0 <= idx < |b[step].replicas|
      ensures b[step].replicas[idx].replica.proposer.election_state.epoch_length >= epoch_length
    {
      lemma_ConstantsAllConsistent(b, asp.c, almost_step);
      lemma_ConstantsAllConsistent(b, asp.c, step);
      if idx != some_index
      {
        assert idx in other_indices;
        lemma_EpochLengthNeverDecreases(b, asp, idx, start_step, almost_step, step);
      }
    }
  }
}

lemma lemma_EpochLengthForAllEventuallyReaches(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  epoch_length:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  ensures  processing_sync_start <= step
  ensures  forall idx :: idx in asp.live_quorum ==> sat(step, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx)))
  ensures  forall idx :: idx in asp.live_quorum ==> sat(step, always(EpochLengthEqualOrGreaterTemporal(b, idx, epoch_length)))
{
  var start_step := lemma_EventuallyForAllPersistentRequestAlwaysInRequestsReceivedPrevEpochs(b, asp, processing_sync_start, processing_bound);
  step := lemma_EpochLengthForSomeEventuallyReaches(b, asp, processing_sync_start, processing_bound, start_step, asp.live_quorum, epoch_length);

  forall idx | idx in asp.live_quorum
    ensures sat(step, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx)))
    ensures sat(step, always(EpochLengthEqualOrGreaterTemporal(b, idx, epoch_length)))
  {
    Lemma_AlwaysImpliesLaterAlways(start_step, step, RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx));
    forall i | step <= i
      ensures sat(i, EpochLengthEqualOrGreaterTemporal(b, idx, epoch_length))
    {
      lemma_EpochLengthNeverDecreases(b, asp, idx, start_step, step, i);
    }
    TemporalAlways(step, EpochLengthEqualOrGreaterTemporal(b, idx, epoch_length));
  }
}

}
