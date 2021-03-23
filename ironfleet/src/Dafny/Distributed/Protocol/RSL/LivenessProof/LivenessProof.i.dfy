include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "StablePeriod.i.dfy"
include "Phase2Start.i.dfy"
include "Phase2Conclusion.i.dfy"
include "StateTransfer.i.dfy"

module LivenessProof__LivenessProof_i {

import opened AppStateMachine_i
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Executor_i
import opened LiveRSL__Message_i
import opened LiveRSL__Replica_i
import opened LiveRSL__StateMachine_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Environment_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__Phase2Start_i
import opened LivenessProof__Phase2Conclusion_i
import opened LivenessProof__StateTransfer_i
import opened CommonProof__Chosen_i
import opened CommonProof__Constants_i
import opened CommonProof__Environment_i
import opened CommonProof__MaxBallotISent1a_i
import opened CommonProof__Message2a_i
import opened CommonProof__Message2b_i
import opened Temporal__Rules_i
import opened Temporal__Temporal_s
import opened Environment_s
import opened Concrete_NodeIdentity_i
import opened Common__UpperBound_s

lemma lemma_EventuallyLiveReplicaExecutesClientRequest(
  b:Behavior<RslState>,
  asp:AssumptionParameters
  ) returns (
  execute_step:int,
  executor_idx:int,
  ios:seq<RslIo>
  )
  requires LivenessAssumptions(b, asp)
  ensures  asp.synchrony_start <= execute_step
  ensures  executor_idx in asp.live_quorum
  ensures  0 <= executor_idx < |b[execute_step].replicas|
  ensures  0 <= executor_idx < |b[execute_step+1].replicas|
  ensures  RslNextOneReplica(b[execute_step], b[execute_step+1], executor_idx, ios)
  ensures  var s := b[execute_step].replicas[executor_idx].replica.executor;
           && s.next_op_to_execute.OutstandingOpKnown?
           && asp.persistent_request in s.next_op_to_execute.v
           && LtUpperBound(s.ops_complete, s.constants.all.params.max_integer_val)
           && LReplicaConstantsValid(s.constants);
  ensures  LExecutorExecute(b[execute_step].replicas[executor_idx].replica.executor,
                            b[execute_step+1].replicas[executor_idx].replica.executor, ExtractSentPacketsFromIos(ios));
{
  var h:Phase2Params, step:int, opn_higher:OperationNumber, p:RslPacket;
  h, step, opn_higher, p, execute_step, ios := lemma_EventuallyKingExecutesOperationCorrespondingTo2aWithClientRequest(b, asp);
  executor_idx := h.king_idx;

  var opn := p.msg.opn_2a;
  var bal := p.msg.bal_2a;

  lemma_ConstantsAllConsistent(b, asp.c, execute_step);
    
  var s := b[execute_step].replicas[executor_idx].replica.executor;
  var s' := b[execute_step+1].replicas[executor_idx].replica.executor;

  assert BalLeq(s.next_op_to_execute.bal, h.view);

  var q := lemma_DecidedOperationWasChosen(b, asp.c, execute_step, executor_idx);
  lemma_QuorumOf1bsFromPhase2StartPrecludesQuorumOf2bsFromEarlierView(b, asp, h, execute_step, q);
  assert s.next_op_to_execute.bal == h.view;

  var quorum_idx :| quorum_idx in q.indices;
  var packet_2b_from_quorum := q.packets[quorum_idx];
  var packet_2a_from_quorum := lemma_2bMessageHasCorresponding2aMessage(b, asp.c, execute_step, packet_2b_from_quorum);

  var latest_step := if execute_step > step then execute_step else step;
  lemma_PacketStaysInSentPackets(b, asp.c, execute_step, latest_step, packet_2a_from_quorum);
  lemma_PacketStaysInSentPackets(b, asp.c, step, latest_step, p);
        
  lemma_2aMessagesFromSameBallotAndOperationMatch(b, asp.c, latest_step, packet_2a_from_quorum, p);
  assert asp.persistent_request in s.next_op_to_execute.v;

  var x := stepmap(imap j :: packet_2a_from_quorum in b[j].environment.sentPackets);
  var send_2a_next_step := earliestStepBetween(0, execute_step, x);
  assert sat(send_2a_next_step, x);

  if (send_2a_next_step <= h.start_step)
  {
    var proposer_idx := lemma_2aMessageImplicationsForProposerState(b, asp.c, send_2a_next_step, packet_2a_from_quorum);
    assert proposer_idx == h.view.proposer_id;
    lemma_MaxBallotISent1aMonotonic(b, asp.c, send_2a_next_step, h.start_step, proposer_idx);
    assert false;
  }

  assert asp.synchrony_start <= h.start_step < send_2a_next_step <= execute_step;
}

lemma lemma_ExecutingRequestBatchWithRequestProducesReply(
  app:AppState,
  requestBatch:RequestBatch,
  req:Request,
  replies:seq<Reply>
  ) returns (
  i:int,
  reply:Reply
  )
  requires replies == HandleRequestBatch(app, requestBatch).1
  requires req in requestBatch
  ensures  0 <= i < |requestBatch| == |replies|
  ensures  req == requestBatch[i]
  ensures  reply == replies[i]
  ensures  reply.client == req.client
  ensures  reply.seqno == req.seqno
{
  var states := HandleRequestBatch(app, requestBatch).0;
  lemma_HandleRequestBatchTriggerHappy(app, requestBatch, states, replies);

  i :| 0 <= i < |requestBatch| && req == requestBatch[i];
  reply := replies[i];
}

lemma lemma_ExecutingRequestBatchWithRequestProducesReplyMessage(
  requestBatch:RequestBatch,
  replies:seq<Reply>,
  me:NodeIdentity,
  sent_packets:seq<RslPacket>,
  i:int,
  req:Request,
  reply:Reply
  ) returns (
  p:RslPacket
  )
  requires 0 <= i < |requestBatch| == |replies|
  requires req == requestBatch[i]
  requires reply == replies[i]
  requires sent_packets == GetPacketsFromReplies(me, requestBatch, replies)
  requires reply.client == req.client
  requires reply.seqno == req.seqno
  ensures  p in sent_packets
  ensures  p.src == me
  ensures  p.dst == req.client
  ensures  p.msg.RslMessage_Reply?
  ensures  p.msg.seqno_reply == req.seqno
{
  if req == requestBatch[0]
  {
    p := sent_packets[0];
  }
  else
  {
    p := lemma_ExecutingRequestBatchWithRequestProducesReplyMessage(requestBatch[1..], replies[1..], me, sent_packets[1..], i-1, req, reply);
  }
}

lemma lemma_EventuallyLiveReplicaSendsReplyToClientDuringSynchronyPeriod(
  b:Behavior<RslState>,
  asp:AssumptionParameters
  ) returns (
  execute_step:int,
  executor_idx:int,
  ios:seq<RslIo>,
  p:RslPacket
  )
  requires LivenessAssumptions(b, asp)
  ensures  asp.synchrony_start <= execute_step
  ensures  executor_idx in asp.live_quorum
  ensures  0 <= executor_idx < |b[execute_step].replicas|
  ensures  0 <= executor_idx < |b[execute_step+1].replicas|
  ensures  LIoOpSend(p) in ios
  ensures  p.src == asp.c.config.replica_ids[executor_idx]
  ensures  p.dst == asp.persistent_request.client
  ensures  p.msg.RslMessage_Reply?
  ensures  p.msg.seqno_reply == asp.persistent_request.seqno
  ensures  RslNextOneReplica(b[execute_step], b[execute_step+1], executor_idx, ios)
{
  execute_step, executor_idx, ios := lemma_EventuallyLiveReplicaExecutesClientRequest(b, asp);
  lemma_ReplicaConstantsAllConsistent(b, asp.c, execute_step, executor_idx);
  var s := b[execute_step].replicas[executor_idx].replica.executor;
  var replies := HandleRequestBatch(s.app, s.next_op_to_execute.v).1;
  var i, reply := lemma_ExecutingRequestBatchWithRequestProducesReply(s.app, s.next_op_to_execute.v, asp.persistent_request, replies);
  var me := asp.c.config.replica_ids[executor_idx];
  var sent_packets := ExtractSentPacketsFromIos(ios);
  p := lemma_ExecutingRequestBatchWithRequestProducesReplyMessage(s.next_op_to_execute.v, replies, me, sent_packets, i, asp.persistent_request, reply);
}

lemma lemma_LivenessAssumptionsAssumingClientNeverGetsReplyCannotHold(
  b:Behavior<RslState>,
  asp:AssumptionParameters
  )
  requires LivenessAssumptions(b, asp)
  ensures  false;
{
  var execute_step, executor_idx, ios, p := lemma_EventuallyLiveReplicaSendsReplyToClientDuringSynchronyPeriod(b, asp);
  var delivery_step := lemma_PacketSentEventuallyDelivered(b, asp, execute_step, p);
  lemma_ReplicaConstantsAllConsistent(b, asp.c, delivery_step, executor_idx);
  assert ReplyDeliveredDuringStep(b[delivery_step], asp.persistent_request);
  TemporalDeduceFromAlways(0, delivery_step, not(ReplyDeliveredTemporal(b, asp.persistent_request)));
  assert false;
}

}
