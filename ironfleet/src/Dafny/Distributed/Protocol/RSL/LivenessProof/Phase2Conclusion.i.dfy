include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "StablePeriod.i.dfy"
include "Phase2Start.i.dfy"
include "Phase2c.i.dfy"
include "GenericInvariants.i.dfy"
include "StateTransfer.i.dfy"

module LivenessProof__Phase2Conclusion_i {

import opened LiveRSL__Broadcast_i
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Executor_i
import opened LiveRSL__Message_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__MaxBalReflected_i
import opened LivenessProof__NextOp_i
import opened LivenessProof__PacketHandling_i
import opened LivenessProof__Phase2Invariants_i
import opened LivenessProof__Phase2Start_i
import opened LivenessProof__Phase2c_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__StateTransfer_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened CommonProof__Environment_i
import opened Temporal__Rules_i
import opened Temporal__Temporal_s
import opened Temporal__Time_i
import opened Environment_s
import opened EnvironmentSynchrony_s
import opened Collections__Maps2_s
import opened Common__UpperBound_s
import opened Math__mul_i

predicate A2aPacketWithThePersistentClientRequestWasSentInThisViewAndAssignedAnEarlierOperationNumber(
  p:RslPacket,
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  i:int,
  opn:OperationNumber
  )
  requires imaptotal(b)
{
  && h.start_step + 1 <= i
  && p in b[i].environment.sentPackets
  && 0 <= h.view.proposer_id < |asp.c.config.replica_ids|
  && 0 <= h.view.proposer_id < |b[h.start_step + 1].replicas|
  && p.src == asp.c.config.replica_ids[h.view.proposer_id]
  && p.dst == asp.c.config.replica_ids[h.view.proposer_id]
  && p.msg.RslMessage_2a?
  && p.msg.opn_2a < opn
  && p.msg.bal_2a == h.view
  && asp.persistent_request in p.msg.val_2a
  && 0 <= p.msg.opn_2a
  && LSetOfMessage1b(b[h.start_step + 1].replicas[h.view.proposer_id].replica.proposer.received_1b_packets)
  && LIsAfterLogTruncationPoint(p.msg.opn_2a, b[h.start_step + 1].replicas[h.view.proposer_id].replica.proposer.received_1b_packets)
  && LAllAcceptorsHadNoProposal(b[h.start_step + 1].replicas[h.view.proposer_id].replica.proposer.received_1b_packets, p.msg.opn_2a)
}

predicate ProposerReachedCertainNextOp(
  ps:RslState,
  idx:int,
  opn:OperationNumber
  )
{
  && 0 <= idx < |ps.replicas|
  && ps.replicas[idx].replica.proposer.next_operation_number_to_propose >= opn
}

function{:opaque} ProposerReachedCertainNextOpTemporal(
  b:Behavior<RslState>,
  idx:int,
  opn:OperationNumber
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, ProposerReachedCertainNextOpTemporal(b, idx, opn))} ::
             sat(i, ProposerReachedCertainNextOpTemporal(b, idx, opn)) == ProposerReachedCertainNextOp(b[i], idx, opn)
{
  stepmap(imap i :: ProposerReachedCertainNextOp(b[i], idx, opn))
}

lemma lemma_Phase2EventuallyReadyForOperationBeyondClientRequest(
  b:Behavior<RslState>,
  asp:AssumptionParameters
  ) returns (
  h:Phase2Params,
  step:int
  )
  requires LivenessAssumptions(b, asp)
  ensures  Phase2StableWithRequest(b, asp, h)
  ensures  h.start_step + 1 <= step
  ensures  sat(step, NoReplicaBeyondViewTemporal(b, h.view))
  ensures  var opn := h.log_truncation_point + asp.c.params.max_log_length + h.num_requests;
           sat(step, or(AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn),
                        AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn)))
{
  var processing_sync_start, processing_bound := lemma_EventuallyPacketProcessingSynchronous(b, asp);
  var primary_idx :| primary_idx in asp.live_quorum;
  var per_request_duration := TimeToAdvanceOneOperation(asp, processing_bound);
  var base_duration := TimeToBeginPhase2(asp, processing_bound) + asp.c.params.max_log_length * per_request_duration;
  lemma_mul_nonnegative(asp.c.params.max_log_length, per_request_duration);
  h := lemma_EventuallyPhase2StableWithRequest(b, asp, processing_sync_start, processing_bound, primary_idx,
                                               base_duration, per_request_duration);
  var opn := h.log_truncation_point + asp.c.params.max_log_length + h.num_requests;
  step := lemma_EventuallyAllLiveReplicasReadyForCertainOperation(b, asp, h, opn);

  assert h.per_request_duration == per_request_duration;
  assert h.base_duration == base_duration;
  assert h.duration == h.base_duration + h.num_requests * h.per_request_duration;

  calc {
    b[step].environment.time;
    <= b[h.start_step + 1].environment.time + TimeToBeginPhase2(asp, h.processing_bound) + (asp.c.params.max_log_length + h.num_requests) * per_request_duration;
      { lemma_mul_is_distributive_add_other_way(per_request_duration, asp.c.params.max_log_length, h.num_requests); }
    b[h.start_step + 1].environment.time + TimeToBeginPhase2(asp, h.processing_bound) + asp.c.params.max_log_length * per_request_duration + h.num_requests * per_request_duration;
    b[h.start_step + 1].environment.time + h.duration;
  }

  TemporalDeduceFromAlwaysWithin(h.start_step + 1, step, NoReplicaBeyondViewTemporal(b, h.view), h.duration, PaxosTimeMap(b));
}

lemma{:timeLimitMultiplier 2} lemma_RequestMovesUpInPrimaryRequestQueueAsNextOpToProposeIncreases(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  i:int
  ) returns (
  p:RslPacket
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires h.start_step + 1 <= i
  requires NoReplicaBeyondView(b[i], h.view)
  ensures  0 <= h.view.proposer_id < |b[i].replicas|
  ensures  var s := b[i].replicas[h.view.proposer_id].replica.proposer;
           var diff := s.next_operation_number_to_propose - (h.log_truncation_point + asp.c.params.max_log_length);
           var n := if diff >= 0 then h.num_requests - diff else h.num_requests;
           || ObjectInFirstNOfSequence(asp.persistent_request, s.request_queue, n)
           || A2aPacketWithThePersistentClientRequestWasSentInThisViewAndAssignedAnEarlierOperationNumber(p, b, asp, h, i, s.next_operation_number_to_propose)
  decreases i
{
  if i == h.start_step + 1
  {
    return;
  }

  lemma_ConstantsAllConsistent(b, asp.c, i-1);
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_AssumptionsMakeValidTransition(b, asp.c, i-1);
  var s := b[i-1].replicas[h.view.proposer_id].replica.proposer;
  var s' := b[i].replicas[h.view.proposer_id].replica.proposer;

  lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, i-1, i, h.view);
  lemma_ProposerStaysInState2InPhase2(b, asp, h, i-1);
  lemma_ProposerStaysInState2InPhase2(b, asp, h, i);
  p := lemma_RequestMovesUpInPrimaryRequestQueueAsNextOpToProposeIncreases(b, asp, h, i-1);

  var diff := s.next_operation_number_to_propose - (h.log_truncation_point + asp.c.params.max_log_length);
  var diff' := s'.next_operation_number_to_propose - (h.log_truncation_point + asp.c.params.max_log_length);
  var n := if diff >= 0 then h.num_requests - diff else h.num_requests;
  var n' := if diff' >= 0 then h.num_requests - diff' else h.num_requests;

  if !ObjectInFirstNOfSequence(asp.persistent_request, s.request_queue, n)
  {
    lemma_NextOperationNumberToProposeIncreasesInPhase2OneStep(b, asp, h, i-1);
    return;
  }

  if s.next_operation_number_to_propose == s'.next_operation_number_to_propose
  {
    if s.request_queue != s'.request_queue
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i-1, h.view.proposer_id);
      var val :| s'.request_queue == s.request_queue + [val];
      assert s.request_queue <= s'.request_queue;
      assert ObjectInFirstNOfSequence(asp.persistent_request, s'.request_queue, n);
    }
  }
  else
  {
    var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i-1, h.view.proposer_id);
    assert s'.next_operation_number_to_propose == s.next_operation_number_to_propose + 1;
    if && LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
       && LProposerNominateNewValueAndSend2a(s, s', ios[0].t,
                                            b[i-1].replicas[h.view.proposer_id].replica.acceptor.log_truncation_point,
                                            ExtractSentPacketsFromIos(ios))
    {
      var batchSize := if |s.request_queue| <= asp.c.params.max_batch_size then |s.request_queue| else asp.c.params.max_batch_size;
      if asp.persistent_request in s.request_queue[..batchSize]
      {
        assert LBroadcastToEveryone(asp.c.config, h.view.proposer_id, RslMessage_2a(h.view, s.next_operation_number_to_propose, s.request_queue[..batchSize]), ExtractSentPacketsFromIos(ios));
        p := LPacket(asp.c.config.replica_ids[h.view.proposer_id], asp.c.config.replica_ids[h.view.proposer_id], RslMessage_2a(h.view, s.next_operation_number_to_propose, s.request_queue[..batchSize]));
        assert LIoOpSend(p) in ios;
        assert p in b[i].environment.sentPackets;
        assert s'.next_operation_number_to_propose > s.next_operation_number_to_propose;
        lemma_Received1bPacketInvariantInPhase2(b, asp, h, i-1);
        assert A2aPacketWithThePersistentClientRequestWasSentInThisViewAndAssignedAnEarlierOperationNumber(p, b, asp, h, i, s'.next_operation_number_to_propose);
      }
      else
      {
        assert s'.request_queue == s.request_queue[batchSize..];
      }
    }
    else
    {
      if diff >= 0
      {
        lemma_OperationNumberMaxLogLengthAheadHasNoProposal(b, asp, h, i, s.next_operation_number_to_propose);
        var opn :| opn > s.next_operation_number_to_propose && !LAllAcceptorsHadNoProposal(s.received_1b_packets, opn);
        lemma_OperationNumberMaxLogLengthAheadHasNoProposal(b, asp, h, i, opn);
        assert false;
      }

      assert n' == n;
      assert s'.request_queue == s.request_queue;
    }
  }
}

lemma lemma_RequestGetsProposedOnceNextOpIsHighEnough(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  i:int,
  opn:OperationNumber
  ) returns (
  p:RslPacket
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires h.start_step + 1 <= i
  requires NoReplicaBeyondView(b[i], h.view)
  requires 0 <= h.view.proposer_id < |b[i].replicas|
  requires b[i].replicas[h.view.proposer_id].replica.proposer.next_operation_number_to_propose >= opn >= h.log_truncation_point + asp.c.params.max_log_length + h.num_requests
  ensures  0 <= h.view.proposer_id < |b[i].replicas|
  ensures  A2aPacketWithThePersistentClientRequestWasSentInThisViewAndAssignedAnEarlierOperationNumber(p, b, asp, h, i, opn)
{
  var x := ProposerReachedCertainNextOpTemporal(b, h.view.proposer_id, opn);
  assert sat(i, x);
  assert !sat(h.start_step + 1, x);
  var earliest_step_reaching_opn := earliestStepBetween(h.start_step + 1, i, x);
  var prev_step := earliest_step_reaching_opn - 1;
  assert h.start_step + 1 <= prev_step < earliest_step_reaching_opn <= i;
  assert !sat(prev_step, x);

  lemma_ConstantsAllConsistent(b, asp.c, prev_step);
  lemma_ConstantsAllConsistent(b, asp.c, prev_step + 1);
  lemma_AssumptionsMakeValidTransition(b, asp.c, prev_step);
  lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, prev_step, i, h.view);
  lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, prev_step + 1, i, h.view);
  lemma_ProposerStaysInState2InPhase2(b, asp, h, prev_step);
  lemma_ProposerStaysInState2InPhase2(b, asp, h, prev_step + 1);

  var s := b[prev_step].replicas[h.view.proposer_id].replica.proposer;
  var s' := b[prev_step + 1].replicas[h.view.proposer_id].replica.proposer;

  assert s'.next_operation_number_to_propose >= opn > s.next_operation_number_to_propose;
  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, prev_step, h.view.proposer_id);
    
  assert s'.next_operation_number_to_propose == opn;
  p := lemma_RequestMovesUpInPrimaryRequestQueueAsNextOpToProposeIncreases(b, asp, h, prev_step + 1);

  lemma_PacketStaysInSentPackets(b, asp.c, prev_step + 1, i, p);
}

lemma lemma_IfPersistentRequestMissingFromRequestQueueDuringPhase2ThenPersistentRequestIsProposed(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  i:int,
  opn:OperationNumber
  ) returns (
  p:RslPacket
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires h.start_step + 1 <= i
  requires NoReplicaBeyondView(b[i], h.view)
  requires 0 <= h.view.proposer_id < |b[i].replicas|
  requires asp.persistent_request !in b[i].replicas[h.view.proposer_id].replica.proposer.request_queue
  ensures  A2aPacketWithThePersistentClientRequestWasSentInThisViewAndAssignedAnEarlierOperationNumber(p, b, asp, h, i, b[i].replicas[h.view.proposer_id].replica.proposer.next_operation_number_to_propose)
{
  if i == h.start_step + 1
  {
    return;
  }

  lemma_ConstantsAllConsistent(b, asp.c, i-1);
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_AssumptionsMakeValidTransition(b, asp.c, i-1);
  lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, i-1, i, h.view);
  lemma_ProposerStaysInState2InPhase2(b, asp, h, i-1);
  lemma_ProposerStaysInState2InPhase2(b, asp, h, i);

  var s := b[i-1].replicas[h.view.proposer_id].replica.proposer;
  var s' := b[i].replicas[h.view.proposer_id].replica.proposer;

  if asp.persistent_request !in s.request_queue
  {
    p := lemma_IfPersistentRequestMissingFromRequestQueueDuringPhase2ThenPersistentRequestIsProposed(b, asp, h, i-1, opn);
    lemma_NextOperationNumberToProposeIncreasesInPhase2OneStep(b, asp, h, i-1);
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i-1, h.view.proposer_id);
  assert s'.next_operation_number_to_propose == s.next_operation_number_to_propose + 1;
  assert LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose);
  assert LProposerNominateNewValueAndSend2a(s, s', ios[0].t,
                                            b[i-1].replicas[h.view.proposer_id].replica.acceptor.log_truncation_point,
                                            ExtractSentPacketsFromIos(ios));
  var batchSize := if |s.request_queue| <= asp.c.params.max_batch_size then |s.request_queue| else asp.c.params.max_batch_size;
  assert asp.persistent_request in s.request_queue[..batchSize];
  p := LPacket(asp.c.config.replica_ids[h.view.proposer_id], asp.c.config.replica_ids[h.view.proposer_id], RslMessage_2a(h.view, s.next_operation_number_to_propose, s.request_queue[..batchSize]));
  assert LIoOpSend(p) in ios;
  assert p in b[i].environment.sentPackets;
  lemma_Received1bPacketInvariantInPhase2(b, asp, h, i-1);
  assert A2aPacketWithThePersistentClientRequestWasSentInThisViewAndAssignedAnEarlierOperationNumber(p, b, asp, h, i, s'.next_operation_number_to_propose);
}

lemma lemma_Phase2EventuallyReadyForOperationBeyond2aWithClientRequest(
  b:Behavior<RslState>,
  asp:AssumptionParameters
  ) returns (
  h:Phase2Params,
  step:int,
  opn:OperationNumber,
  p:RslPacket
  )
  requires LivenessAssumptions(b, asp)
  ensures  Phase2StableWithRequest(b, asp, h)
  ensures  sat(step, NoReplicaBeyondViewTemporal(b, h.view))
  ensures  ReplicaCaughtUp(b[step], h.king_idx, opn)
  ensures  A2aPacketWithThePersistentClientRequestWasSentInThisViewAndAssignedAnEarlierOperationNumber(p, b, asp, h, step, opn)
{
  h, step := lemma_Phase2EventuallyReadyForOperationBeyondClientRequest(b, asp);
  opn := h.log_truncation_point + asp.c.params.max_log_length + h.num_requests;
  lemma_ConstantsAllConsistent(b, asp.c, step);
  assert sat(step, NoReplicaBeyondViewTemporal(b, h.view));
  if sat(step, AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn))
  {
    p := lemma_RequestGetsProposedOnceNextOpIsHighEnough(b, asp, h, step, opn);
    assert ReplicaCaughtUp(b[step], h.king_idx, opn);
    assert A2aPacketWithThePersistentClientRequestWasSentInThisViewAndAssignedAnEarlierOperationNumber(p, b, asp, h, step, opn);
  }
  else
  {
    p := lemma_IfPersistentRequestMissingFromRequestQueueDuringPhase2ThenPersistentRequestIsProposed(b, asp, h, step, opn);
    opn := b[step].replicas[h.view.proposer_id].replica.proposer.next_operation_number_to_propose;
    assert ReplicaCaughtUp(b[step], h.king_idx, opn);
    assert A2aPacketWithThePersistentClientRequestWasSentInThisViewAndAssignedAnEarlierOperationNumber(p, b, asp, h, step, opn);
  }
}

lemma lemma_EventuallyKingExecutesOperationCorrespondingTo2aWithClientRequest(
  b:Behavior<RslState>,
  asp:AssumptionParameters
  ) returns (
  h:Phase2Params,
  step:int,
  opn:OperationNumber,
  p:RslPacket,
  execute_step:int,
  ios:seq<RslIo>
  )
  requires LivenessAssumptions(b, asp)
  ensures  Phase2StableWithRequest(b, asp, h)
  ensures  A2aPacketWithThePersistentClientRequestWasSentInThisViewAndAssignedAnEarlierOperationNumber(p, b, asp, h, step, opn)
  ensures  0 <= execute_step
  ensures  0 <= h.king_idx < |b[execute_step].replicas|
  ensures  0 <= h.king_idx < |b[execute_step+1].replicas|
  ensures  RslNextOneReplica(b[execute_step], b[execute_step+1], h.king_idx, ios)
  ensures  var s := b[execute_step].replicas[h.king_idx].replica.executor;
           && s.next_op_to_execute.OutstandingOpKnown?
           && BalLeq(s.next_op_to_execute.bal, h.view)
           && s.ops_complete == p.msg.opn_2a
           && LtUpperBound(s.ops_complete, s.constants.all.params.max_integer_val)
           && LReplicaConstantsValid(s.constants)
  ensures  LExecutorExecute(b[execute_step].replicas[h.king_idx].replica.executor, b[execute_step+1].replicas[h.king_idx].replica.executor,
                            ExtractSentPacketsFromIos(ios))
{
  h, step, opn, p := lemma_Phase2EventuallyReadyForOperationBeyond2aWithClientRequest(b, asp);

  var x := stepmap(imap j :: 0 <= h.king_idx < |b[j].replicas| && b[j].replicas[h.king_idx].replica.executor.ops_complete > p.msg.opn_2a);
  var execute_next_step := earliestStepBetween(0, step, x);
  execute_step := execute_next_step - 1;
  assert !sat(0, x);
  assert !sat(execute_step, x);

  lemma_ReplicaConstantsAllConsistent(b, asp.c, execute_step, h.king_idx);
  lemma_ReplicaConstantsAllConsistent(b, asp.c, execute_next_step, h.king_idx);
  lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, execute_step, step, h.view);
  ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, execute_step, h.king_idx);

  var s := b[execute_step].replicas[h.king_idx].replica.executor;
  var s' := b[execute_next_step].replicas[h.king_idx].replica.executor;

  if b[execute_step].replicas[h.king_idx].nextActionIndex == 0
  {
    var p_state_supply := ios[0].r;
    assert IsValidLIoOp(ios[0], asp.c.config.replica_ids[h.king_idx], b[execute_step].environment);
    lemma_StateSupplyToKingDoesNotIncludeOpn(b, asp, h, execute_step, p.msg.opn_2a, p_state_supply);
    assert false;
  }

  lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, execute_next_step, step, h.view);
  lemma_MaxBalReflectedLeqCurrentView(b, asp, execute_next_step, h.view, h.king_idx);
}

}
