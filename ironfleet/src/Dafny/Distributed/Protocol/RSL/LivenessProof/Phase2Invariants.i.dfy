include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "StablePeriod.i.dfy"
include "ViewChange.i.dfy"
include "MaxBallot.i.dfy"
include "MaxBallotISent1a.i.dfy"
include "MaxBalReflected.i.dfy"
include "GenericInvariants.i.dfy"
include "../CommonProof/MaxBallotISent1a.i.dfy"
include "../CommonProof/MaxBallot.i.dfy"
include "../CommonProof/Constants.i.dfy"
include "../CommonProof/Actions.i.dfy"
include "../CommonProof/LogTruncationPoint.i.dfy"
include "../CommonProof/Environment.i.dfy"

module LivenessProof__Phase2Invariants_i {

import opened LiveRSL__Configuration_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__ViewChange_i
import opened LivenessProof__MaxBallot_i
import opened LivenessProof__MaxBallotISent1a_i
import opened LivenessProof__MaxBalReflected_i
import opened LivenessProof__GenericInvariants_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened CommonProof__Environment_i
import opened CommonProof__LogTruncationPoint_i
import opened CommonProof__MaxBallot_i
import opened CommonProof__MaxBallotISent1a_i
import opened Temporal__Temporal_s
import opened Environment_s
import opened Collections__Maps2_s
import opened Common__UpperBound_s

predicate ReplicaCaughtUp(
  ps:RslState,
  idx:int,
  opn:OperationNumber
  )
{
  0 <= idx < |ps.replicas| && ps.replicas[idx].replica.executor.ops_complete >= opn
}

function{:opaque} ReplicaCaughtUpTemporal(
  b:Behavior<RslState>,
  idx:int,
  opn:OperationNumber
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, ReplicaCaughtUpTemporal(b, idx, opn))} ::
             sat(i, ReplicaCaughtUpTemporal(b, idx, opn)) == ReplicaCaughtUp(b[i], idx, opn)
{
  stepmap(imap i :: ReplicaCaughtUp(b[i], idx, opn))
}

function{:opaque} AllReplicasCaughtUpTemporalSet(
  b:Behavior<RslState>,
  live_quorum:set<int>,
  opn:OperationNumber
  ):set<temporal>
  requires imaptotal(b)
  ensures  forall idx :: idx in live_quorum ==> ReplicaCaughtUpTemporal(b, idx, opn) in AllReplicasCaughtUpTemporalSet(b, live_quorum, opn)
  ensures  forall t :: t in AllReplicasCaughtUpTemporalSet(b, live_quorum, opn) ==> exists idx :: idx in live_quorum && t == ReplicaCaughtUpTemporal(b, idx, opn)
{
  set idx | idx in live_quorum :: ReplicaCaughtUpTemporal(b, idx, opn)
}

predicate AllLiveReplicasReadyForNextOperation(
  ps:RslState,
  live_quorum:set<int>,
  view:Ballot,
  opn:OperationNumber
  )
{
  && (forall idx :: idx in live_quorum ==> ReplicaCaughtUp(ps, idx, opn))
  && var proposer_idx := view.proposer_id;
    && 0 <= proposer_idx < |ps.replicas|
    && var s := ps.replicas[proposer_idx].replica;
      && s.proposer.next_operation_number_to_propose >= opn
      && s.acceptor.log_truncation_point >= opn
}

function {:opaque} AllLiveReplicasReadyForNextOperationTemporal(
  b:Behavior<RslState>,
  live_quorum:set<int>,
  view:Ballot,
  opn:OperationNumber
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, AllLiveReplicasReadyForNextOperationTemporal(b, live_quorum, view, opn))} ::
             sat(i, AllLiveReplicasReadyForNextOperationTemporal(b, live_quorum, view, opn)) ==
             AllLiveReplicasReadyForNextOperation(b[i], live_quorum, view, opn)
{
  stepmap(imap i :: AllLiveReplicasReadyForNextOperation(b[i], live_quorum, view, opn))
}

lemma lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  j:int,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i <= j
  requires NoReplicaBeyondView(b[j], view)
  ensures  NoReplicaBeyondView(b[i], view)
{
  if !sat(i, NoReplicaBeyondViewTemporal(b, view))
  {
    var idx :| 0 <= idx < |b[i].replicas| && BalLt(view, CurrentViewOfHost(b[i], idx));
    lemma_ConstantsAllConsistent(b, asp.c, i);
    lemma_ConstantsAllConsistent(b, asp.c, j);
    lemma_ViewOfHostMonotonic(b, asp, idx, i, j);
    assert false;
  }
}

lemma lemma_ProposerStaysInState2InPhase2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  i:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires h.start_step + 1 <= i
  requires NoReplicaBeyondView(b[i], h.view)
  ensures  0 <= h.view.proposer_id < |b[i].replicas|
  ensures  var s := b[i].replicas[h.view.proposer_id].replica.proposer;
           && s.max_ballot_i_sent_1a == h.view
           && s.current_state == 2;
  decreases i
{
  lemma_ConstantsAllConsistent(b, asp.c, i);
    
  if i > h.start_step + 1
  {
    lemma_ConstantsAllConsistent(b, asp.c, i-1);
    lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, i-1, i, h.view);
    lemma_ProposerStaysInState2InPhase2(b, asp, h, i-1);

    var s := b[i-1].replicas[h.view.proposer_id].replica.proposer;
    var s' := b[i].replicas[h.view.proposer_id].replica.proposer;
    assert s.max_ballot_i_sent_1a == h.view;
    assert s.current_state == 2;

    assert BalLeq(CurrentViewOfHost(b[i-1], h.view.proposer_id), h.view); // TRIGGER
    lemma_MaxBallotISent1aLeqView(b, asp, i-1, h.view.proposer_id);
    assert s.election_state.current_view == h.view;

    assert BalLeq(CurrentViewOfHost(b[i], h.view.proposer_id), h.view); // TRIGGER
    assert BalLeq(s'.election_state.current_view, h.view);
    lemma_NoReplicaBeyondViewImpliesNoMaxBallotISent1aBeyondView(b, asp, i, h.view);
    assert BalLeq(s'.max_ballot_i_sent_1a, h.view);

    if s'.max_ballot_i_sent_1a != h.view || s'.current_state != 2
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i-1, h.view.proposer_id);
      assert false;
    }
  }
}

lemma lemma_NextOperationNumberToProposeIncreasesInPhase2OneStep(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  i:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires h.start_step + 1 <= i
  requires NoReplicaBeyondView(b[i+1], h.view)
  ensures  0 <= h.view.proposer_id < |b[i].replicas|
  ensures  0 <= h.view.proposer_id < |b[i+1].replicas|
  ensures  b[i+1].replicas[h.view.proposer_id].replica.proposer.next_operation_number_to_propose
           >= b[i].replicas[h.view.proposer_id].replica.proposer.next_operation_number_to_propose
{
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i+1);

  var s := b[i].replicas[h.view.proposer_id].replica.proposer;
  var s' := b[i+1].replicas[h.view.proposer_id].replica.proposer;

  if s'.next_operation_number_to_propose < s.next_operation_number_to_propose
  {
    lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, i, i+1, h.view);
    lemma_ProposerStaysInState2InPhase2(b, asp, h, i);
    assert s.max_ballot_i_sent_1a == h.view;
    assert s.current_state == 2;

    var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, h.view.proposer_id);
    assert false;
  }
}

lemma lemma_NextOperationNumberToProposeIncreasesInPhase2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  i:int,
  j:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires h.start_step + 1 <= i <= j
  requires NoReplicaBeyondView(b[j], h.view)
  ensures  0 <= h.view.proposer_id < |b[i].replicas|
  ensures  0 <= h.view.proposer_id < |b[j].replicas|
  ensures  b[j].replicas[h.view.proposer_id].replica.proposer.next_operation_number_to_propose
           >= b[i].replicas[h.view.proposer_id].replica.proposer.next_operation_number_to_propose
  decreases j-i
{
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, j);

  if j == i
  {
  }
  else if j == i + 1
  {
    lemma_NextOperationNumberToProposeIncreasesInPhase2OneStep(b, asp, h, i);
  }
  else
  {
    lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, j-1, j, h.view);
    lemma_ConstantsAllConsistent(b, asp.c, j-1);
    lemma_NextOperationNumberToProposeIncreasesInPhase2(b, asp, h, i, j-1);
    lemma_NextOperationNumberToProposeIncreasesInPhase2OneStep(b, asp, h, j-1);
  }
}

lemma lemma_Received1bPacketInvariantInPhase2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  i:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires h.start_step + 1 <= i
  requires NoReplicaBeyondView(b[i], h.view)
  ensures  0 <= h.view.proposer_id < |b[i].replicas|
  ensures  var s := b[i].replicas[h.view.proposer_id].replica.proposer;
           && s.received_1b_packets == b[h.start_step + 1].replicas[h.view.proposer_id].replica.proposer.received_1b_packets
           && |s.received_1b_packets| >= LMinQuorumSize(s.constants.all.config)
           && LSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a)
  decreases i;
{
  lemma_ConstantsAllConsistent(b, asp.c, i);
    
  if i > h.start_step + 1
  {
    lemma_ConstantsAllConsistent(b, asp.c, i-1);
    lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, i-1, i, h.view);
    lemma_ProposerStaysInState2InPhase2(b, asp, h, i-1);
    lemma_ProposerStaysInState2InPhase2(b, asp, h, i);

    var idx := h.view.proposer_id;
    var s := b[i-1].replicas[idx].replica.proposer;
    var s' := b[i].replicas[idx].replica.proposer;
    if s'.received_1b_packets != s.received_1b_packets
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i-1, idx);
      assert false;
    }

    lemma_Received1bPacketInvariantInPhase2(b, asp, h, i-1);
  }
}

lemma lemma_ProposerCanNominateInPhase2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  i:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires h.start_step + 1 <= i
  requires NoReplicaBeyondView(b[i], h.view)
  ensures  0 <= h.view.proposer_id < |b[i].replicas|
  ensures  var s := b[i].replicas[h.view.proposer_id].replica;
           s.proposer.next_operation_number_to_propose < s.acceptor.log_truncation_point + asp.c.params.max_log_length
           ==> LProposerCanNominateUsingOperationNumber(s.proposer, s.acceptor.log_truncation_point, s.proposer.next_operation_number_to_propose)
  decreases i
{
  lemma_ConstantsAllConsistent(b, asp.c, i);
  var idx := h.view.proposer_id;

  var s := b[i].replicas[idx].replica;
  var opn := s.proposer.next_operation_number_to_propose;

  if opn < s.acceptor.log_truncation_point + asp.c.params.max_log_length
  {
    lemma_ProposerStaysInState2InPhase2(b, asp, h, i);
    assert s.proposer.max_ballot_i_sent_1a == h.view;
    assert s.proposer.current_state == 2;

    lemma_MaxBallotISent1aLeqView(b, asp, i, idx);
    assert BalLeq(CurrentViewOfHost(b[i], idx), h.view);
    assert s.proposer.election_state.current_view == s.proposer.max_ballot_i_sent_1a;

    lemma_OverflowProtectionNotUsedForReplica(b, asp, i, idx);
    assert opn < UpperBoundedAddition(s.acceptor.log_truncation_point, s.proposer.constants.all.params.max_log_length, s.proposer.constants.all.params.max_integer_val);

    lemma_NextOperationNumberToProposeIncreasesInPhase2(b, asp, h, h.start_step + 1, i);

    calc {
      opn;
      >= b[h.start_step + 1].replicas[idx].replica.proposer.next_operation_number_to_propose;
      == b[h.start_step + 1].replicas[idx].replica.acceptor.log_truncation_point;
      >= { lemma_LogTruncationPointMonotonic(b, asp.c, 0, h.start_step + 1, idx); }
      b[0].replicas[idx].replica.acceptor.log_truncation_point;
      == 0;
    }

    lemma_Received1bPacketInvariantInPhase2(b, asp, h, i);
    assert s.proposer.next_operation_number_to_propose >= h.log_truncation_point;
    lemma_ProposerLogTruncationPointAlwaysBeyondThatOfAllReceived1bs(b, asp.c, h.start_step + 1, idx);
    assert forall p :: p in s.proposer.received_1b_packets && p.msg.RslMessage_1b? ==> p.msg.log_truncation_point <= h.log_truncation_point <= s.proposer.next_operation_number_to_propose;
    assert LProposerCanNominateUsingOperationNumber(s.proposer, s.acceptor.log_truncation_point, opn);
  }
}

lemma lemma_IfAllLiveReplicasReadyForNextOperationThenSoLaterInPhase2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  i:int,
  j:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires h.start_step + 1 <= i <= j
  requires AllLiveReplicasReadyForNextOperation(b[i], asp.live_quorum, h.view, opn)
  requires NoReplicaBeyondView(b[j], h.view)
  ensures  AllLiveReplicasReadyForNextOperation(b[j], asp.live_quorum, h.view, opn)
{
  lemma_LogTruncationPointMonotonic(b, asp.c, i, j, h.view.proposer_id);
  lemma_NextOperationNumberToProposeIncreasesInPhase2(b, asp, h, i, j);
  forall idx | idx in asp.live_quorum
    ensures ReplicaCaughtUp(b[j], idx, opn)
  {
    lemma_OpsCompleteMonotonic(b, asp.c, i, j, idx);
  }
}

lemma lemma_MaxBalNeverExceedsViewDuringPhase2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  i:int,
  idx:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires h.start_step + 1 <= i
  requires 0 <= idx < |b[i].replicas|
  requires NoReplicaBeyondView(b[i], h.view)
  ensures  BalLeq(b[i].replicas[idx].replica.acceptor.max_bal, h.view)
{
  if NoReplicaBeyondView(b[i], h.view)
  {
    lemma_MaxBalLeqMaxBallotPrimarySent1a(b, asp.c, i, idx);
    var max_bal := b[i].replicas[idx].replica.acceptor.max_bal;
    assert BalLeq(max_bal, b[i].replicas[max_bal.proposer_id].replica.proposer.max_ballot_i_sent_1a);
    lemma_NoReplicaBeyondViewImpliesNoMaxBallotISent1aBeyondView(b, asp, i, h.view);
    assert BalLeq(b[i].replicas[max_bal.proposer_id].replica.proposer.max_ballot_i_sent_1a, h.view);
  }
}

lemma lemma_LearnerMaxBallotSeenNeverExceedsViewDuringPhase2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  i:int,
  idx:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires h.start_step + 1 <= i
  requires 0 <= idx < |b[i].replicas|
  requires NoReplicaBeyondView(b[i], h.view)
  ensures  BalLeq(b[i].replicas[idx].replica.learner.max_ballot_seen, h.view)
{
  var max_ballot_seen := b[i].replicas[idx].replica.learner.max_ballot_seen;
  lemma_LearnerMaxBallotSeenShowsPrimaryReachedState2(b, asp.c, i, idx);
  assert BalLeq(max_ballot_seen, b[i].replicas[max_ballot_seen.proposer_id].replica.proposer.max_ballot_i_sent_1a);
  lemma_NoReplicaBeyondViewImpliesNoMaxBallotISent1aBeyondView(b, asp, i, h.view);
  assert BalLeq(b[i].replicas[max_ballot_seen.proposer_id].replica.proposer.max_ballot_i_sent_1a, h.view);
}

lemma lemma_OperationNumberMaxLogLengthAheadHasNoProposal(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  i:int,
  opn:OperationNumber
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires h.start_step + 1 <= i
  requires NoReplicaBeyondView(b[i], h.view)
  requires opn >= h.log_truncation_point + asp.c.params.max_log_length
  ensures  0 <= h.view.proposer_id < |b[i].replicas|
  ensures  LSetOfMessage1b(b[i].replicas[h.view.proposer_id].replica.proposer.received_1b_packets)
  ensures  LAllAcceptorsHadNoProposal(b[i].replicas[h.view.proposer_id].replica.proposer.received_1b_packets, opn)
{
  lemma_Received1bPacketInvariantInPhase2(b, asp, h, i);

  lemma_ConstantsAllConsistent(b, asp.c, h.start_step + 1);
  lemma_ConstantsAllConsistent(b, asp.c, i);
    
  var s := b[h.start_step + 1].replicas[h.view.proposer_id].replica;

  forall p | p in s.proposer.received_1b_packets
    ensures opn !in p.msg.votes
  {
    if opn in p.msg.votes
    {
      lemma_VoteInReceived1bMessageAlwaysWithinLogTruncationPointRange(b, asp.c, h.start_step + 1, h.view.proposer_id, opn, p);
      assert false;
    }
  }
}

}
