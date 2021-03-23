include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "ViewPropagation.i.dfy"
include "ViewPropagation2.i.dfy"
include "ViewAdvance.i.dfy"
include "../CommonProof/Constants.i.dfy"
include "../../../Common/Collections/Sets.i.dfy"

module LivenessProof__ViewSuspicion_i {

import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Election_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__PacketHandling_i
import opened LivenessProof__RoundRobin_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__ViewPropagation_i
import opened LivenessProof__ViewPropagation2_i
import opened LivenessProof__ViewAdvance_i
import opened LivenessProof__ViewChange_i
import opened CommonProof__CanonicalizeBallot_i
import opened CommonProof__Constants_i
import opened Collections__Maps2_s
import opened Collections__Sets_i
import opened Temporal__Temporal_s
import opened Temporal__Rules_i
import opened Common__UpperBound_s
import opened Environment_s

predicate ReplicaHasCollectedSuspicionFrom(
  ps:RslState,
  collector_idx:int,
  suspector_idx:int,
  view:Ballot
  )
{
  && 0 <= collector_idx < |ps.replicas|
  && (|| BalLt(view, CurrentViewOfHost(ps, collector_idx))
     || (&& CurrentViewOfHost(ps, collector_idx) == view
        && suspector_idx in ps.replicas[collector_idx].replica.proposer.election_state.current_view_suspectors))
}

function{:opaque} ReplicaHasCollectedSuspicionFromTemporal(
  b:Behavior<RslState>,
  collector_idx:int,
  suspector_idx:int,
  view:Ballot
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, ReplicaHasCollectedSuspicionFromTemporal(b, collector_idx, suspector_idx, view))} ::
             sat(i, ReplicaHasCollectedSuspicionFromTemporal(b, collector_idx, suspector_idx, view)) ==
             ReplicaHasCollectedSuspicionFrom(b[i], collector_idx, suspector_idx, view)
{
  stepmap(imap i :: ReplicaHasCollectedSuspicionFrom(b[i], collector_idx, suspector_idx, view))
}

lemma lemma_ReplicaHasCollectedSuspicionFromStableOneStep(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  collector_idx:int,
  suspector_idx:int,
  view:Ballot,
  i:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= collector_idx < |asp.c.config.replica_ids|
  requires 0 <= suspector_idx < |asp.c.config.replica_ids|
  requires 0 <= i
  requires ReplicaHasCollectedSuspicionFrom(b[i], collector_idx, suspector_idx, view)
  ensures  ReplicaHasCollectedSuspicionFrom(b[i+1], collector_idx, suspector_idx, view)
{
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i+1);
  lemma_AssumptionsMakeValidTransition(b, asp.c, i);
  lemma_ViewPlusOfHostMonotonic(b, asp, collector_idx, i, i+1);
}

lemma lemma_ReplicaHasCollectedSuspicionFromStableMultipleSteps(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  collector_idx:int,
  suspector_idx:int,
  view:Ballot,
  i:int,
  j:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= collector_idx < |asp.c.config.replica_ids|
  requires 0 <= suspector_idx < |asp.c.config.replica_ids|
  requires 0 <= i <= j
  requires ReplicaHasCollectedSuspicionFrom(b[i], collector_idx, suspector_idx, view)
  ensures  ReplicaHasCollectedSuspicionFrom(b[j], collector_idx, suspector_idx, view)
  decreases j-i
{
  if j > i + 1
  {
    lemma_ReplicaHasCollectedSuspicionFromStableMultipleSteps(b, asp, collector_idx, suspector_idx, view, i, j-1);
    lemma_ReplicaHasCollectedSuspicionFromStableMultipleSteps(b, asp, collector_idx, suspector_idx, view, j-1, j);
  }
  else if j == i + 1
  {
    lemma_ConstantsAllConsistent(b, asp.c, i);
    lemma_ConstantsAllConsistent(b, asp.c, i+1);
    lemma_AssumptionsMakeValidTransition(b, asp.c, i);
    lemma_ViewPlusOfHostMonotonic(b, asp, collector_idx, i, i+1);
  }
}

lemma lemma_ReplicaHasCollectedSuspicionFromStable(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  collector_idx:int,
  suspector_idx:int,
  view:Ballot,
  i:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= collector_idx < |asp.c.config.replica_ids|
  requires 0 <= suspector_idx < |asp.c.config.replica_ids|
  requires 0 <= i
  requires ReplicaHasCollectedSuspicionFrom(b[i], collector_idx, suspector_idx, view)
  ensures  sat(i, always(ReplicaHasCollectedSuspicionFromTemporal(b, collector_idx, suspector_idx, view)))
{
  forall j | i <= j
    ensures sat(j, ReplicaHasCollectedSuspicionFromTemporal(b, collector_idx, suspector_idx, view))
  {
    lemma_ReplicaHasCollectedSuspicionFromStableMultipleSteps(b, asp, collector_idx, suspector_idx, view, i, j);
  }

  TemporalAlways(i, ReplicaHasCollectedSuspicionFromTemporal(b, collector_idx, suspector_idx, view));
}

lemma lemma_ReplicaEventuallyCollectsSuspicionOrLeavesView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  suspector_idx:int,
  collector_idx:int,
  start_step:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires suspector_idx in asp.live_quorum
  requires collector_idx in asp.live_quorum
  requires processing_sync_start <= start_step
  requires 0 <= suspector_idx < |b[start_step].replicas|
  ensures  start_step <= step
  ensures  0 <= suspector_idx < |b[step].replicas|
  ensures  0 <= collector_idx < |b[step].replicas|
  ensures  var view := CurrentViewOfHost(b[start_step], suspector_idx);
           || BalLt(view, CurrentViewOfHost(b[step], suspector_idx))
           || sat(step, always(ReplicaHasCollectedSuspicionFromTemporal(b, collector_idx, suspector_idx, view)))
{
  var view := CurrentViewOfHost(b[start_step], suspector_idx);
  step := lemma_ReplicaEventuallyPropagatesSuspicionOrLeavesView(b, asp, processing_sync_start, processing_bound,
                                                                suspector_idx, collector_idx, start_step);
  lemma_ConstantsAllConsistent(b, asp.c, step);
  if !BalLt(view, CurrentViewOfHost(b[step], suspector_idx))
  {
    lemma_ReplicaHasCollectedSuspicionFromStable(b, asp, collector_idx, suspector_idx, view, step);
  }
}

lemma lemma_IfReplicaHasCollectedSuspicionsFromLiveQuorumItWillAdvanceView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  collector_idx:int,
  view:Ballot,
  action_step:int,
  ios:seq<RslIo>
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= action_step
  requires IsValidBallot(view, asp.c)
  requires BallotHasSuccessor(view, asp.c)
  requires collector_idx in asp.live_quorum
  requires 0 <= collector_idx < |b[action_step].replicas|
  requires 0 <= collector_idx < |b[action_step+1].replicas|
  requires RslNextOneReplica(b[action_step], b[action_step+1], collector_idx, ios)
  requires SpontaneousIos(ios, 1)
  requires LReplicaNextReadClockCheckForQuorumOfViewSuspicions(b[action_step].replicas[collector_idx].replica, b[action_step+1].replicas[collector_idx].replica, SpontaneousClock(ios), ExtractSentPacketsFromIos(ios))
  requires CurrentViewOfHost(b[action_step], collector_idx) == view
  requires forall suspector_idx :: suspector_idx in asp.live_quorum ==> suspector_idx in b[action_step].replicas[collector_idx].replica.proposer.election_state.current_view_suspectors
  ensures  0 <= collector_idx < |b[action_step+1].replicas|
  ensures  BalLt(view, CurrentViewOfHost(b[action_step+1], collector_idx))
{
  lemma_ConstantsAllConsistent(b, asp.c, action_step);

  var ps := b[action_step];
  var ps' := b[action_step+1];
  var s := ps.replicas[collector_idx].replica;
  var s' := ps'.replicas[collector_idx].replica;
  var es := s.proposer.election_state;
  var es' := s'.proposer.election_state;

  assert LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, s', SpontaneousClock(ios), ExtractSentPacketsFromIos(ios));
  assert LProposerCheckForQuorumOfViewSuspicions(s.proposer, s'.proposer, ios[0].t);
  assert ElectionStateCheckForQuorumOfViewSuspicions(es, es', ios[0].t);
  SubsetCardinality(asp.live_quorum, es.current_view_suspectors);
  lemma_OverflowProtectionNotUsedForReplica(b, asp, action_step, collector_idx);
  assert es'.current_view == ComputeSuccessorView(es.current_view, es.constants.all);
}

lemma lemma_IfAllLiveReplicasInViewOneWillReachSuccessor(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  view:Ballot,
  start_step:int
  ) returns (
  step:int,
  replica_index:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires 0 <= processing_sync_start <= start_step
  requires IsValidBallot(view, asp.c)
  requires BallotHasSuccessor(view, asp.c)
  requires forall idx :: idx in asp.live_quorum ==> 0 <= idx < |b[start_step].replicas| && CurrentViewOfHost(b[start_step], idx) == view
  ensures  processing_sync_start <= step
  ensures  replica_index in asp.live_quorum
  ensures  0 <= replica_index < |b[step].replicas|
  ensures  BalLt(view, CurrentViewOfHost(b[step], replica_index))
{
  lemma_ConstantsAllConsistent(b, asp.c, start_step);
  var collector_idx :| collector_idx in asp.live_quorum;
  var first_step := lemma_SuspicionOfLiveReplicasEventuallyPropagatedToObserverForever(b, asp, processing_sync_start, processing_bound, collector_idx, asp.live_quorum, view, start_step);

  var action_step := lemma_ReplicaNextPerformsSubactionSoon(b, asp, first_step, collector_idx, 8);
  assert SpecificClockReadingRslActionOccurs(b[action_step], b[action_step+1], LReplicaNextReadClockCheckForQuorumOfViewSuspicions, collector_idx);
  var ios :| && RslNextOneReplica(b[action_step], b[action_step+1], collector_idx, ios)
             && SpontaneousIos(ios, 1)
             && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(b[action_step].replicas[collector_idx].replica, b[action_step+1].replicas[collector_idx].replica, SpontaneousClock(ios), ExtractSentPacketsFromIos(ios));

  lemma_ConstantsAllConsistent(b, asp.c, action_step);
  if exists ridx :: ridx in asp.live_quorum && BalLt(view, CurrentViewOfHost(b[action_step], ridx))
  {
    step := action_step;
    replica_index :| replica_index in asp.live_quorum && BalLt(view, CurrentViewOfHost(b[action_step], replica_index));
    return;
  }
  assert !BalLt(view, CurrentViewOfHost(b[action_step], collector_idx));
  lemma_BalLtProperties();
  forall suspector_idx | suspector_idx in asp.live_quorum
    ensures suspector_idx in b[action_step].replicas[collector_idx].replica.proposer.election_state.current_view_suspectors
  {
    TemporalDeduceFromAlways(first_step, action_step, SuspicionPropagatedToObserverTemporal(b, suspector_idx, collector_idx, view));
    lemma_ViewPlusOfHostMonotonic(b, asp, suspector_idx, start_step, action_step);
    assert !BalLt(view, CurrentViewOfHost(b[action_step], suspector_idx));
  }
  lemma_ViewPlusOfHostMonotonic(b, asp, collector_idx, start_step, action_step);
  step := action_step + 1;
  replica_index := collector_idx;
  lemma_IfReplicaHasCollectedSuspicionsFromLiveQuorumItWillAdvanceView(b, asp, collector_idx, view, action_step, ios);
}

lemma lemma_IfOneLiveReplicaReachesViewOneWillReachSuccessor(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  view:Ballot,
  start_step:int,
  cur_index:int
  ) returns (
  step:int,
  replica_index:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires 0 <= processing_sync_start <= start_step
  requires cur_index in asp.live_quorum
  requires IsValidBallot(view, asp.c)
  requires BallotHasSuccessor(view, asp.c)
  requires 0 <= cur_index < |b[start_step].replicas|
  requires BalLeq(view, CurrentViewOfHost(b[start_step], cur_index))
  ensures  processing_sync_start <= step
  ensures  replica_index in asp.live_quorum
  ensures  0 <= replica_index < |b[step].replicas|
  ensures  BalLt(view, CurrentViewOfHost(b[step], replica_index))
{
  if CurrentViewOfHost(b[start_step], cur_index) != view
  {
    step := start_step;
    replica_index := cur_index;
    lemma_BalLtProperties();
    return;
  }
  assert CurrentViewOfHost(b[start_step], cur_index) == view;
  var first_step := lemma_OneLiveReplicaSoonAdvancesAllForever(b, asp, processing_sync_start, processing_bound, start_step, cur_index);
  lemma_ConstantsAllConsistent(b, asp.c, first_step);
  if exists ridx :: ridx in asp.live_quorum && BalLt(view, CurrentViewOfHost(b[first_step], ridx))
  {
    step := first_step;
    replica_index :| replica_index in asp.live_quorum && BalLt(view, CurrentViewOfHost(b[first_step], replica_index));
    return;
  }
  forall ridx | ridx in asp.live_quorum
    ensures CurrentViewOfHost(b[first_step], ridx) == view
  {
    TemporalDeduceFromAlways(first_step, first_step, HostReachedViewTemporal(b, ridx, view));
    assert !BalLt(view, CurrentViewOfHost(b[first_step], ridx));
  }
  step, replica_index := lemma_IfAllLiveReplicasInViewOneWillReachSuccessor(b, asp, processing_sync_start, processing_bound, view, first_step);
}

lemma lemma_SomeReplicaInLiveQuorumReachesView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  view:Ballot
  ) returns (
  step:int,
  replica_index:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires 0 <= processing_sync_start
  requires IsValidBallot(view, asp.c)
  requires LeqUpperBound(view.seqno, asp.c.params.max_integer_val)
  ensures  processing_sync_start <= step
  ensures  replica_index in asp.live_quorum
  ensures  0 <= replica_index < |b[step].replicas|
  ensures  BalLeq(view, CurrentViewOfHost(b[step], replica_index))
  decreases CanonicalizeBallot(view, asp.c)
{
  lemma_CanonicalizeBallotProperties();
    
  var cview := CanonicalizeBallot(view, asp.c);
  if cview <= 1
  {
    replica_index :| replica_index in asp.live_quorum;
    lemma_ConstantsAllConsistent(b, asp.c, 0);
    calc {
      CanonicalizeBallot(CurrentViewOfHost(b[0], replica_index), asp.c);
      CanonicalizeBallot(Ballot(1, 0), asp.c);
        { reveal_CanonicalizeBallot(); }
      |asp.c.config.replica_ids|;
      >= 1;
      >= cview;
    }
    lemma_IsValidBallot(b, asp, 0, replica_index);
    assert BalLeq(view, CurrentViewOfHost(b[0], replica_index));
    step := processing_sync_start;
    lemma_ConstantsAllConsistent(b, asp.c, step);
    lemma_ViewPlusOfHostMonotonic(b, asp, replica_index, 0, step);
  }
  else
  {
    var previousView := ComputePredecessorView(view, asp.c);
    lemma_ComputePredecessorViewProperties(view, asp.c);
    var first_step, cur_index := lemma_SomeReplicaInLiveQuorumReachesView(b, asp, processing_sync_start, processing_bound, previousView);
    lemma_ConstantsAllConsistent(b, asp.c, first_step);
    step, replica_index := lemma_IfOneLiveReplicaReachesViewOneWillReachSuccessor(b, asp, processing_sync_start, processing_bound, previousView, first_step, cur_index);
    lemma_ConstantsAllConsistent(b, asp.c, step);
    lemma_IsValidBallot(b, asp, step, replica_index);
    lemma_NothingBetweenViewAndSuccessor(previousView, CurrentViewOfHost(b[step], replica_index), asp.c);
    lemma_BalLtProperties();
  }
}

}

    
