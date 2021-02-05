include "../DistributedSystem.i.dfy"
include "../CommonProof/Assumptions.i.dfy"
include "../CommonProof/Constants.i.dfy"
include "../CommonProof/Actions.i.dfy"
include "../CommonProof/Environment.i.dfy"
include "../CommonProof/PacketSending.i.dfy"
include "../CommonProof/Chosen.i.dfy"
include "Chosen.i.dfy"

module DirectRefinement__Execution_i {

import opened LiveRSL__Configuration_i
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Message_i
import opened LiveRSL__Executor_i
import opened LiveRSL__Replica_i
import opened LiveRSL__StateMachine_i
import opened LiveRSL__Types_i
import opened Concrete_NodeIdentity_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Actions_i
import opened CommonProof__Chosen_i
import opened CommonProof__Constants_i
import opened CommonProof__Environment_i
import opened CommonProof__PacketSending_i
import opened DirectRefinement__Chosen_i
import opened DirectRefinement__HandleRequestBatch_i
import opened Environment_s
import opened Temporal__Temporal_s
import opened Common__UpperBound_s
import opened Collections__Seqs_s

//////////////////////////////
// APP STATE
//////////////////////////////

lemma lemma_AppStateAlwaysValid(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int
  ) returns (
  qs:seq<QuorumOf2bs>
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  ensures  IsValidQuorumOf2bsSequence(b[i], qs)
  ensures  |qs| == b[i].replicas[idx].replica.executor.ops_complete
  ensures  b[i].replicas[idx].replica.executor.app == GetAppStateFromRequestBatches(GetSequenceOfRequestBatches(qs))
  decreases i
{
  if i == 0
  {
    qs := [];
    return;
  }

  lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
  lemma_ReplicaConstantsAllConsistent(b, c, i-1, idx);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);

  var s := b[i-1].replicas[idx].replica.executor;
  var s' := b[i].replicas[idx].replica.executor;

  if s'.ops_complete == s.ops_complete
  {
    qs := lemma_AppStateAlwaysValid(b, c, i-1, idx);
    lemma_IfValidQuorumOf2bsSequenceNowThenNext(b, c, i-1, qs);
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  if b[i-1].replicas[idx].nextActionIndex == 0
  {
    var p := ios[0].r;
    qs := lemma_TransferredStateAlwaysValid(b, c, i-1, p);
    return;
  }

  var prev_qs := lemma_AppStateAlwaysValid(b, c, i-1, idx);
  var q := lemma_DecidedOperationWasChosen(b, c, i-1, idx);
  qs := prev_qs + [q];
  assert GetSequenceOfRequestBatches(qs) == GetSequenceOfRequestBatches(prev_qs) + [q.v];
}

lemma lemma_TransferredStateAlwaysValid(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p:RslPacket
  ) returns (
  qs:seq<QuorumOf2bs>
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_AppStateSupply?
  ensures  IsValidQuorumOf2bsSequence(b[i], qs)
  ensures  |qs| == p.msg.opn_state_supply
  ensures  p.msg.app_state == GetAppStateFromRequestBatches(GetSequenceOfRequestBatches(qs))
  decreases i
{
  if i == 0 { return; }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);

  if p in b[i-1].environment.sentPackets
  {
    qs := lemma_TransferredStateAlwaysValid(b, c, i-1, p);
    lemma_IfValidQuorumOf2bsSequenceNowThenNext(b, c, i-1, qs);
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  var idx, ios := lemma_ActionThatSendsAppStateSupplyIsProcessAppStateRequest(b[i-1], b[i], p);
  qs := lemma_AppStateAlwaysValid(b, c, i-1, idx);
}

//////////////////////////////
// REPLY CACHE
//////////////////////////////

lemma lemma_ReplyInReplyCacheIsAllowed(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  client:NodeIdentity,
  idx:int
  ) returns (
  qs:seq<QuorumOf2bs>,
  batches:seq<RequestBatch>,
  batch_num:int,
  req_num:int
  )
  requires IsValidBehaviorPrefix(b, c, i+1)
  requires 0 <= i
  requires 0 <= idx < |c.config.replica_ids|
  requires 0 <= idx < |b[i].replicas|
  requires client in b[i].replicas[idx].replica.executor.reply_cache
  ensures  IsValidQuorumOf2bsSequence(b[i], qs)
  ensures  batches == GetSequenceOfRequestBatches(qs)
  ensures  0 <= batch_num < |batches|
  ensures  0 <= req_num < |batches[batch_num]|
  ensures  b[i].replicas[idx].replica.executor.reply_cache[client] == GetReplyFromRequestBatches(batches, batch_num, req_num)
  decreases i
{
  if i == 0 { return; }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);

  var s := b[i-1].replicas[idx].replica.executor;
  var s' := b[i].replicas[idx].replica.executor;
  if client in s.reply_cache && s'.reply_cache[client] == s.reply_cache[client]
  {
    qs, batches, batch_num, req_num := lemma_ReplyInReplyCacheIsAllowed(b, c, i-1, client, idx);
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  var nextActionIndex := b[i-1].replicas[idx].nextActionIndex;
  if nextActionIndex == 0
  {
    var p := ios[0].r;
    qs, batches, batch_num, req_num := lemma_ReplyInAppStateSupplyIsAllowed(b, c, i-1, client, p);
    return;
  }

  assert nextActionIndex == 6;

  var qs_prev := lemma_AppStateAlwaysValid(b, c, i-1, idx);
  var q := lemma_DecidedOperationWasChosen(b, c, i-1, idx);
  qs := qs_prev + [q];
  batches := GetSequenceOfRequestBatches(qs);
  batch_num := |qs_prev|;

  assert GetSequenceOfRequestBatches(qs_prev) == batches[..batch_num];

  assert s.app == GetAppStateFromRequestBatches(GetSequenceOfRequestBatches(qs_prev));

  var batch := s.next_op_to_execute.v;
  var replies := HandleRequestBatch(s.app, batch).1;

  req_num :| 0 <= req_num < |batch| && replies[req_num].client == client && s'.reply_cache[client] == replies[req_num];
}

lemma lemma_ReplyInAppStateSupplyIsAllowed(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  client:NodeIdentity,
  p:RslPacket
  ) returns (
  qs:seq<QuorumOf2bs>,
  batches:seq<RequestBatch>,
  batch_num:int,
  req_num:int
  )
  requires IsValidBehaviorPrefix(b, c, i+1)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_AppStateSupply?
  requires client in p.msg.reply_cache
  ensures  IsValidQuorumOf2bsSequence(b[i], qs)
  ensures  batches == GetSequenceOfRequestBatches(qs)
  ensures  0 <= batch_num < |batches|
  ensures  0 <= req_num < |batches[batch_num]|
  ensures  p.msg.reply_cache[client] == GetReplyFromRequestBatches(batches, batch_num, req_num)
  decreases i
{
  if i == 0 { return; }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);

  if p in b[i-1].environment.sentPackets
  {
    qs, batches, batch_num, req_num := lemma_ReplyInAppStateSupplyIsAllowed(b, c, i-1, client, p);
    lemma_IfValidQuorumOf2bsSequenceNowThenNext(b, c, i-1, qs);
    return;
  }

  var idx, ios := lemma_ActionThatSendsAppStateSupplyIsProcessAppStateRequest(b[i-1], b[i], p);
  qs, batches, batch_num, req_num := lemma_ReplyInReplyCacheIsAllowed(b, c, i-1, client, idx);
}

//////////////////////////////
// REPLIES
//////////////////////////////

lemma lemma_GetRequestIndexCorrespondingToPacketInGetPacketsFromReplies(
  p:RslPacket,
  me:NodeIdentity,
  requests:seq<Request>,
  replies:seq<Reply>
  ) returns (
  i:int
  )
  requires |requests| == |replies|
  requires forall r :: r in replies ==> r.Reply?
  requires p in GetPacketsFromReplies(me, requests, replies)
  ensures  0 <= i < |requests|
  ensures  p.src == me
  ensures  p.dst == requests[i].client
  ensures  p.msg.RslMessage_Reply?
  ensures  p.msg.seqno_reply == requests[i].seqno
  ensures  p.msg.reply == replies[i].reply
{
  if |requests| == 0
  {
    assert false;
  }

  if p == LPacket(requests[0].client, me, RslMessage_Reply(requests[0].seqno, replies[0].reply))
  {
    i := 0;
  }
  else
  {
    var i_minus_1 := lemma_GetRequestIndexCorrespondingToPacketInGetPacketsFromReplies(p, me, requests[1..], replies[1..]);
    i := i_minus_1 + 1;
  }
}

lemma lemma_ReplySentViaExecutionIsAllowed(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p:RslPacket,
  idx:int,
  ios:seq<RslIo>
  ) returns (
  qs:seq<QuorumOf2bs>,
  batches:seq<RequestBatch>,
  batch_num:int,
  req_num:int
  )
  requires IsValidBehaviorPrefix(b, c, i+1)
  requires 0 <= i
  requires 0 <= idx < |c.config.replica_ids|
  requires 0 <= idx < |b[i].replicas|
  requires LIoOpSend(p) in ios
  requires RslNext(b[i], b[i+1])
  requires b[i].environment.nextStep == LEnvStepHostIos(c.config.replica_ids[idx], ios)
  requires b[i].replicas[idx].replica.executor.next_op_to_execute.OutstandingOpKnown?
  requires LtUpperBound(b[i].replicas[idx].replica.executor.ops_complete,
                        b[i].replicas[idx].replica.executor.constants.all.params.max_integer_val)
  requires LReplicaConstantsValid(b[i].replicas[idx].replica.executor.constants)
  requires LExecutorExecute(b[i].replicas[idx].replica.executor, b[i+1].replicas[idx].replica.executor, ExtractSentPacketsFromIos(ios))
  ensures  IsValidQuorumOf2bsSequence(b[i], qs)
  ensures  batches == GetSequenceOfRequestBatches(qs)
  ensures  0 <= batch_num < |batches|
  ensures  0 <= req_num < |batches[batch_num]|
  ensures  Reply(p.dst, p.msg.seqno_reply, p.msg.reply) == GetReplyFromRequestBatches(batches, batch_num, req_num)
{
  lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
  lemma_ReplicaConstantsAllConsistent(b, c, i+1, idx);

  var qs_prev := lemma_AppStateAlwaysValid(b, c, i, idx);
  var q := lemma_DecidedOperationWasChosen(b, c, i, idx);
  qs := qs_prev + [q];
  batches := GetSequenceOfRequestBatches(qs);
  batch_num := |qs_prev|;

  assert GetSequenceOfRequestBatches(qs_prev) == batches[..batch_num];

  var s := b[i].replicas[idx].replica.executor;
  assert s.app == GetAppStateFromRequestBatches(GetSequenceOfRequestBatches(qs_prev));

  var batch := s.next_op_to_execute.v;
  var temp := HandleRequestBatch(s.app, batch);
  lemma_HandleRequestBatchTriggerHappy(s.app, batch, temp.0, temp.1);
  var new_state := last(temp.0);
  var replies := temp.1;
  var me := c.config.replica_ids[idx];

  assert p in GetPacketsFromReplies(me, batch, replies);
  assert p.src == c.config.replica_ids[idx];
  req_num := lemma_GetRequestIndexCorrespondingToPacketInGetPacketsFromReplies(p, me, batch, replies);
  var reply := Reply(p.dst, p.msg.seqno_reply, p.msg.reply);
  assert reply == replies[req_num];
}

lemma lemma_ReplySentIsAllowed(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p:RslPacket
  ) returns (
  qs:seq<QuorumOf2bs>,
  batches:seq<RequestBatch>,
  batch_num:int,
  req_num:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_Reply?
  ensures  IsValidQuorumOf2bsSequence(b[i], qs)
  ensures  batches == GetSequenceOfRequestBatches(qs)
  ensures  0 <= batch_num < |batches|
  ensures  0 <= req_num < |batches[batch_num]|
  ensures  Reply(p.dst, p.msg.seqno_reply, p.msg.reply) == GetReplyFromRequestBatches(batches, batch_num, req_num)
  decreases i
{
  if i == 0 { return; }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);

  if p in b[i-1].environment.sentPackets
  {
    qs, batches, batch_num, req_num := lemma_ReplySentIsAllowed(b, c, i-1, p);
    lemma_IfValidQuorumOf2bsSequenceNowThenNext(b, c, i-1, qs);
    return;
  }

  assert b[i-1].environment.nextStep.LEnvStepHostIos?;
  assert LIoOpSend(p) in b[i-1].environment.nextStep.ios;
  var idx := GetReplicaIndex(b[i-1].environment.nextStep.actor, c.config);
  var ios := b[i-1].environment.nextStep.ios;
  var idx_alt :| RslNextOneReplica(b[i-1], b[i], idx_alt, ios);
  assert ReplicasDistinct(c.config.replica_ids, idx, idx_alt);

  var nextActionIndex := b[i-1].replicas[idx].nextActionIndex;
  if nextActionIndex == 0
  {
    qs, batches, batch_num, req_num := lemma_ReplyInReplyCacheIsAllowed(b, c, i-1, ios[0].r.src, idx);
    lemma_IfValidQuorumOf2bsSequenceNowThenNext(b, c, i-1, qs);
  }
  else if nextActionIndex == 6
  {
    qs, batches, batch_num, req_num := lemma_ReplySentViaExecutionIsAllowed(b, c, i-1, p, idx, ios);
    lemma_IfValidQuorumOf2bsSequenceNowThenNext(b, c, i-1, qs);
  }
  else
  {
    assert false;
  }
}
  
}
