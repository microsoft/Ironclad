include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "PacketHandling.i.dfy"
include "../CommonProof/Constants.i.dfy"
include "../CommonProof/Actions.i.dfy"
include "../CommonProof/ReplyCache.i.dfy"
include "../CommonProof/Requests.i.dfy"

module LivenessProof__Seqno_i {
import opened LiveRSL__Acceptor_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Election_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Executor_i
import opened LiveRSL__Learner_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Replica_i
import opened LiveRSL__StateMachine_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Environment_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__PacketHandling_i
import opened Liveness__HostQueueLemmas_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened CommonProof__PacketSending_i
import opened CommonProof__ReplyCache_i
import opened CommonProof__Requests_i
import opened Temporal__Heuristics_i
import opened Temporal__Rules_i
import opened Temporal__Temporal_s
import opened Environment_s
import opened EnvironmentSynchrony_s

/////////////////////
// INVARIANTS
/////////////////////

predicate SequenceNumberRequestInv(req':Request, req:Request)
  requires req.Request?
{
  req'.Request? && req'.client == req.client ==> (req'.seqno < req.seqno) || (req'.seqno == req.seqno && req'.request == req.request)
}

predicate SequenceNumberBatchInv(batch:RequestBatch, req:Request)
  requires req.Request?
{
  forall req' :: req' in batch ==> SequenceNumberRequestInv(req', req)
}

predicate SequenceNumberVotesInv(votes:Votes, req:Request)
  requires req.Request?
{
  forall op :: op in votes ==> SequenceNumberBatchInv(votes[op].max_val, req)
}

predicate SequenceNumberLearnerStateInv(s:LearnerState, req:Request)
  requires req.Request?
{
  forall op :: op in s ==> SequenceNumberBatchInv(s[op].candidate_learned_value, req)
}

predicate SequenceNumberReplyCacheInv(reply_cache:ReplyCache, req:Request)
  requires req.Request?
{
  req.client in reply_cache && reply_cache[req.client].Reply? ==> reply_cache[req.client].seqno <= req.seqno
}

predicate SequenceNumberPacketInv(p:RslPacket, req:Request)
  requires req.Request?
{
  && (p.msg.RslMessage_Request? ==> SequenceNumberRequestInv(Request(p.src, p.msg.seqno_req, p.msg.val), req))
  && (p.msg.RslMessage_1b? ==> SequenceNumberVotesInv(p.msg.votes, req))
  && (p.msg.RslMessage_2a? ==> SequenceNumberBatchInv(p.msg.val_2a, req))
  && (p.msg.RslMessage_2b? ==> SequenceNumberBatchInv(p.msg.val_2b, req))
  && (p.msg.RslMessage_AppStateSupply? ==> SequenceNumberReplyCacheInv(p.msg.reply_cache, req))
}

predicate SequenceNumberReplicaInv(s:LReplica, req:Request)
  requires req.Request?
{
  && (forall r :: r in s.proposer.request_queue ==> SequenceNumberRequestInv(r, req))
  && (forall p :: p in s.proposer.received_1b_packets ==> SequenceNumberPacketInv(p, req))
  && (forall r :: r in s.proposer.election_state.requests_received_this_epoch ==> SequenceNumberRequestInv(r, req))
  && (forall r :: r in s.proposer.election_state.requests_received_prev_epochs ==> SequenceNumberRequestInv(r, req))
  && SequenceNumberVotesInv(s.acceptor.votes, req)
  && SequenceNumberLearnerStateInv(s.learner.unexecuted_learner_state, req)
  && (s.executor.next_op_to_execute.OutstandingOpKnown? ==> SequenceNumberBatchInv(s.executor.next_op_to_execute.v, req))
  && SequenceNumberReplyCacheInv(s.executor.reply_cache, req)
}

predicate SequenceNumberStateInv(ps:RslState, req:Request)
  requires req.Request?
{
  && (forall p :: p in ps.environment.sentPackets && p.src in ps.constants.config.replica_ids ==> SequenceNumberPacketInv(p, req))
  && (forall idx :: 0 <= idx < |ps.replicas| ==> SequenceNumberReplicaInv(ps.replicas[idx].replica, req))
}

////////////////////////
// PACKET INVARIANT
////////////////////////

lemma lemma_SequenceNumberPacketInvHolds(
  ps:RslState,
  ps':RslState,
  idx:int,
  ios:seq<RslIo>,
  p:RslPacket,
  req:Request
  )
  requires RslNextOneReplica(ps, ps', idx, ios)
  requires req.Request?
  requires LIoOpSend(p) in ios
  requires SequenceNumberStateInv(ps, req)
  requires LEnvironmentInvariant(ps.environment)
  requires ConstantsAllConsistentInv(ps)
  ensures  SequenceNumberPacketInv(p, req)
{
  var s := ps.replicas[idx].replica;
  var s' := ps'.replicas[idx].replica;
  var id := ps.constants.config.replica_ids[idx];
  var e := ps.environment;
  var e' := ps'.environment;
    
  var sent_packets := ExtractSentPacketsFromIos(ios);
  if p.msg.RslMessage_2b?
  {
    var inp:RslPacket :| ios[0] == LIoOpReceive(inp) && inp.msg.RslMessage_2a? && LReplicaNextProcess2a(s, s', inp, sent_packets);
    lemma_PacketProcessedImpliesPacketSent(ps, ps', idx, ios, inp);
    if inp.src in ps.constants.config.replica_ids
    {
      assert SequenceNumberPacketInv(inp, req);
      assert SequenceNumberPacketInv(p, req);
    }
  }
}

lemma lemma_ReplicaNextPreservesSequenceNumberRequestQueueInv(
  ps:RslState,
  ps':RslState,
  idx:int,
  ios:seq<RslIo>,
  req:Request
  )
  requires RslNext(ps, ps')
  requires req.Request?
  requires 0 <= idx < |ps.replicas|
  requires RslNextOneReplica(ps, ps', idx, ios)
  requires SequenceNumberStateInv(ps, req)
  requires LEnvironmentInvariant(ps.environment)
  requires ConstantsAllConsistentInv(ps)
  requires |ps.constants.config.replica_ids| == |ps.replicas| == |ps'.constants.config.replica_ids| == |ps'.replicas|
  requires 0 <= idx < |ps'.replicas|
  requires ClientNeverSentHigherSequenceNumberRequest(ps, req)
  ensures  forall r :: r in ps'.replicas[idx].replica.proposer.request_queue ==> SequenceNumberRequestInv(r, req)
{
  var s := ps.replicas[idx].replica;
  var s' := ps'.replicas[idx].replica;
  var votes := s.acceptor.votes;
  var votes' := s'.acceptor.votes;
  var id := ps.constants.config.replica_ids[idx];
  var e := ps.environment;
  var e' := ps'.environment;

  forall r | r in s'.proposer.request_queue
    ensures SequenceNumberRequestInv(r, req)
  {
    if r !in s.proposer.request_queue
    {
      if |ios| > 0 && ios[0].LIoOpReceive? && LProposerProcessRequest(s.proposer, s'.proposer, ios[0].r)
      {
        var inp := ios[0].r;
        lemma_PacketProcessedImpliesPacketSent(ps, ps', idx, ios, inp);
        assert SequenceNumberPacketInv(inp, req);
        assert r == Request(inp.src, inp.msg.seqno_req, inp.msg.val);
        assert SequenceNumberRequestInv(r, req);
      }
      else
      {
        assert SequenceNumberRequestInv(r, req);
      }
    }
  }
}

////////////////////////////////////////////////
// STATE INVARIANTS - SPECIFIC PARTS OF STATE
////////////////////////////////////////////////

lemma lemma_ReplicaNextPreservesSequenceNumberReceived1bPacketsInv(
  ps:RslState,
  ps':RslState,
  idx:int,
  ios:seq<RslIo>,
  req:Request
  )
  requires RslNext(ps, ps')
  requires req.Request?
  requires 0 <= idx < |ps.replicas|
  requires RslNextOneReplica(ps, ps', idx, ios)
  requires SequenceNumberStateInv(ps, req)
  requires LEnvironmentInvariant(ps.environment)
  requires ConstantsAllConsistentInv(ps)
  requires |ps.constants.config.replica_ids| == |ps.replicas| == |ps'.constants.config.replica_ids| == |ps'.replicas|
  requires 0 <= idx < |ps'.replicas|
  ensures  forall p :: p in ps'.replicas[idx].replica.proposer.received_1b_packets ==> SequenceNumberPacketInv(p, req)
{
  var s := ps.replicas[idx].replica;
  var s' := ps'.replicas[idx].replica;
  var votes := s.acceptor.votes;
  var votes' := s'.acceptor.votes;
  var id := ps.constants.config.replica_ids[idx];
  var e := ps.environment;
  var e' := ps'.environment;

  forall p | p in s'.proposer.received_1b_packets
    ensures SequenceNumberPacketInv(p, req)
  {
    if p !in s.proposer.received_1b_packets
    {
      assert |ios| > 0 && ios[0].LIoOpReceive? && LProposerProcess1b(s.proposer, s'.proposer, ios[0].r);
      var inp := ios[0].r;
      lemma_PacketProcessedImpliesPacketSent(ps, ps', idx, ios, inp);
      assert SequenceNumberPacketInv(inp, req);
    }
  }
}

lemma lemma_ReplicaNextPreservesSequenceNumberRequestsReceivedInv(
  ps:RslState,
  ps':RslState,
  idx:int,
  ios:seq<RslIo>,
  req:Request
  )
  requires RslNext(ps, ps')
  requires req.Request?
  requires 0 <= idx < |ps.replicas|
  requires RslNextOneReplica(ps, ps', idx, ios)
  requires SequenceNumberStateInv(ps, req)
  requires LEnvironmentInvariant(ps.environment)
  requires ConstantsAllConsistentInv(ps)
  requires |ps.constants.config.replica_ids| == |ps.replicas| == |ps'.constants.config.replica_ids| == |ps'.replicas|
  requires 0 <= idx < |ps'.replicas|
  requires ClientNeverSentHigherSequenceNumberRequest(ps, req)
  ensures  forall r :: r in ps'.replicas[idx].replica.proposer.election_state.requests_received_this_epoch ==> SequenceNumberRequestInv(r, req)
  ensures  forall r :: r in ps'.replicas[idx].replica.proposer.election_state.requests_received_prev_epochs ==> SequenceNumberRequestInv(r, req)
{
  var s := ps.replicas[idx].replica;
  var s' := ps'.replicas[idx].replica;
  var votes := s.acceptor.votes;
  var votes' := s'.acceptor.votes;
  var id := ps.constants.config.replica_ids[idx];
  var e := ps.environment;
  var e' := ps'.environment;
  var es := s.proposer.election_state;
  var es' := s'.proposer.election_state;

  forall r | r in es'.requests_received_this_epoch
    ensures SequenceNumberRequestInv(r, req)
  {
    if r !in es.requests_received_this_epoch
    {
      if |ios| > 0 && ios[0].LIoOpReceive? && LProposerProcessRequest(s.proposer, s'.proposer, ios[0].r)
      {
        var inp := ios[0].r;
        lemma_PacketProcessedImpliesPacketSent(ps, ps', idx, ios, inp);
        assert SequenceNumberPacketInv(inp, req);
        assert SequenceNumberRequestInv(r, req);
      }
      else if exists batch :: ElectionStateReflectExecutedRequestBatch(es, es', batch)
      {
        var batch :| ElectionStateReflectExecutedRequestBatch(es, es', batch);
        lemma_RemoveExecutedRequestBatchProducesSubsequence(es'.requests_received_this_epoch, es.requests_received_this_epoch, batch);
        assert SequenceNumberRequestInv(r, req);
      }
      else
      {
        assert false;
      }
    }
  }

  forall r | r in es'.requests_received_prev_epochs
    ensures SequenceNumberRequestInv(r, req)
  {
    if r !in es.requests_received_prev_epochs
    {
      if exists batch :: ElectionStateReflectExecutedRequestBatch(es, es', batch)
      {
        var batch :| ElectionStateReflectExecutedRequestBatch(es, es', batch);
        lemma_RemoveExecutedRequestBatchProducesSubsequence(es'.requests_received_prev_epochs, es.requests_received_prev_epochs, batch);
        assert SequenceNumberRequestInv(r, req);
      }
      assert r in es.requests_received_this_epoch;
    }
  }
}

lemma lemma_ReplicaNextPreservesSequenceNumberVotesInv(
  ps:RslState,
  ps':RslState,
  idx:int,
  ios:seq<RslIo>,
  req:Request
  )
  requires RslNext(ps, ps')
  requires req.Request?
  requires 0 <= idx < |ps.replicas|
  requires RslNextOneReplica(ps, ps', idx, ios)
  requires SequenceNumberStateInv(ps, req)
  requires LEnvironmentInvariant(ps.environment)
  requires ConstantsAllConsistentInv(ps)
  requires |ps.constants.config.replica_ids| == |ps.replicas| == |ps'.constants.config.replica_ids| == |ps'.replicas|
  requires 0 <= idx < |ps'.replicas|
  ensures  SequenceNumberVotesInv(ps'.replicas[idx].replica.acceptor.votes, req)
{
  var s := ps.replicas[idx].replica;
  var s' := ps'.replicas[idx].replica;
  var votes := s.acceptor.votes;
  var votes' := s'.acceptor.votes;
  var id := ps.constants.config.replica_ids[idx];

  forall op | op in votes'
    ensures SequenceNumberBatchInv(votes'[op].max_val, req)
  {
    if op in votes && votes'[op] == votes[op]
    {
      assert SequenceNumberBatchInv(votes[op].max_val, req);
    }
    else
    {
      assert |ios| >= 1 && ios[0].LIoOpReceive?;
      var inp := ios[0].r;
      assert LAcceptorProcess2a(s.acceptor, s'.acceptor, inp, ExtractSentPacketsFromIos(ios));
      lemma_PacketProcessedImpliesPacketSent(ps, ps', idx, ios, inp);
      assert SequenceNumberPacketInv(inp, req);
      assert SequenceNumberBatchInv(votes'[op].max_val, req);
    }
  }
}

lemma lemma_ReplicaNextPreservesSequenceNumberLearnerStateInv(
  ps:RslState,
  ps':RslState,
  idx:int,
  ios:seq<RslIo>,
  req:Request
  )
  requires RslNext(ps, ps')
  requires req.Request?
  requires 0 <= idx < |ps.replicas|
  requires RslNextOneReplica(ps, ps', idx, ios)
  requires SequenceNumberStateInv(ps, req)
  requires LEnvironmentInvariant(ps.environment)
  requires ConstantsAllConsistentInv(ps)
  requires |ps.constants.config.replica_ids| == |ps.replicas| == |ps'.constants.config.replica_ids| == |ps'.replicas|
  requires 0 <= idx < |ps'.replicas|
  ensures  SequenceNumberLearnerStateInv(ps'.replicas[idx].replica.learner.unexecuted_learner_state, req)
{
  var s := ps.replicas[idx].replica;
  var s' := ps'.replicas[idx].replica;
  var votes := s.acceptor.votes;
  var votes' := s'.acceptor.votes;
  var id := ps.constants.config.replica_ids[idx];

  forall op | op in s'.learner.unexecuted_learner_state
    ensures SequenceNumberBatchInv(s'.learner.unexecuted_learner_state[op].candidate_learned_value, req)
  {
    if op in s.learner.unexecuted_learner_state && s'.learner.unexecuted_learner_state[op] == s.learner.unexecuted_learner_state[op]
    {
      assert SequenceNumberBatchInv(s.learner.unexecuted_learner_state[op].candidate_learned_value, req);
    }
    else
    {
      assert |ios| >= 1 && ios[0].LIoOpReceive?;
      var inp := ios[0].r;
      assert LLearnerProcess2b(s.learner, s'.learner, inp);
      lemma_PacketProcessedImpliesPacketSent(ps, ps', idx, ios, inp);
      assert SequenceNumberPacketInv(inp, req);
      assert SequenceNumberBatchInv(s'.learner.unexecuted_learner_state[op].candidate_learned_value, req);
    }
  }
}

lemma lemma_ReplicaNextPreservesSequenceNumberReplyCacheInv(
  ps:RslState,
  ps':RslState,
  idx:int,
  ios:seq<RslIo>,
  req:Request
  )
  requires RslNext(ps, ps')
  requires req.Request?
  requires 0 <= idx < |ps.replicas|
  requires RslNextOneReplica(ps, ps', idx, ios)
  requires SequenceNumberStateInv(ps, req)
  requires LEnvironmentInvariant(ps.environment)
  requires ConstantsAllConsistentInv(ps)
  requires |ps.constants.config.replica_ids| == |ps.replicas| == |ps'.constants.config.replica_ids| == |ps'.replicas|
  requires 0 <= idx < |ps'.replicas|
  ensures  SequenceNumberReplyCacheInv(ps'.replicas[idx].replica.executor.reply_cache, req)
{
  var s := ps.replicas[idx].replica;
  var s' := ps'.replicas[idx].replica;
  var votes := s.acceptor.votes;
  var votes' := s'.acceptor.votes;
  var id := ps.constants.config.replica_ids[idx];

  if req.Request? && req.client in s'.executor.reply_cache && s'.executor.reply_cache[req.client].Reply? && s'.executor.reply_cache[req.client].seqno > req.seqno
  {
    if LReplicaNextSpontaneousMaybeExecute(s, s', ExtractSentPacketsFromIos(ios))
    {
      var batch := s.executor.next_op_to_execute.v;
      var states := HandleRequestBatch(s.executor.app, batch).0;
      var replies := HandleRequestBatch(s.executor.app, batch).1;
      lemma_HandleRequestBatchTriggerHappy(s.executor.app, batch, states, replies);

      assert SequenceNumberReplyCacheInv(s.executor.reply_cache, req);
      var req_idx :| 0 <= req_idx < |batch| && replies[req_idx].client == req.client && s'.executor.reply_cache[req.client] == replies[req_idx];
      assert SequenceNumberBatchInv(batch, req);
      assert SequenceNumberRequestInv(batch[req_idx], req);
      assert false;
    }
    else if |ios| > 0 && ios[0].LIoOpReceive? && LExecutorProcessAppStateSupply(s.executor, s'.executor, ios[0].r)
    {
      var inp := ios[0].r;
      lemma_PacketProcessedImpliesPacketSent(ps, ps', idx, ios, inp);
      assert SequenceNumberPacketInv(inp, req);
      assert SequenceNumberReplyCacheInv(s'.executor.reply_cache, req);
    }
    else
    {
      assert SequenceNumberReplyCacheInv(s'.executor.reply_cache, req);
    }
  }
}

lemma lemma_ReplicaNextPreservesSequenceNumberReplicaInv(
  ps:RslState,
  ps':RslState,
  idx:int,
  ios:seq<RslIo>,
  req:Request
  )
  requires RslNext(ps, ps')
  requires req.Request?
  requires 0 <= idx < |ps.replicas|
  requires RslNextOneReplica(ps, ps', idx, ios)
  requires SequenceNumberStateInv(ps, req)
  requires LEnvironmentInvariant(ps.environment)
  requires ConstantsAllConsistentInv(ps)
  requires |ps.constants.config.replica_ids| == |ps.replicas| == |ps'.constants.config.replica_ids| == |ps'.replicas|
  requires 0 <= idx < |ps'.replicas|
  requires ClientNeverSentHigherSequenceNumberRequest(ps, req)
  ensures  SequenceNumberReplicaInv(ps'.replicas[idx].replica, req)
{
  var s := ps.replicas[idx].replica;
  var s' := ps'.replicas[idx].replica;

  lemma_ReplicaNextPreservesSequenceNumberRequestQueueInv(ps, ps', idx, ios, req);
  lemma_ReplicaNextPreservesSequenceNumberReceived1bPacketsInv(ps, ps', idx, ios, req);
  lemma_ReplicaNextPreservesSequenceNumberRequestsReceivedInv(ps, ps', idx, ios, req);
  lemma_ReplicaNextPreservesSequenceNumberVotesInv(ps, ps', idx, ios, req);
  lemma_ReplicaNextPreservesSequenceNumberLearnerStateInv(ps, ps', idx, ios, req);
  assert s'.executor.next_op_to_execute.OutstandingOpKnown? ==> SequenceNumberBatchInv(s'.executor.next_op_to_execute.v, req);
  lemma_ReplicaNextPreservesSequenceNumberReplyCacheInv(ps, ps', idx, ios, req);
}

/////////////////////////////////
// STATE INVARIANT - REPLICA
/////////////////////////////////

lemma lemma_PaxosNextPreservesSequenceNumberReplicaInv(ps:RslState, ps':RslState, idx:int, req:Request)
  requires RslNext(ps, ps')
  requires req.Request?
  requires SequenceNumberStateInv(ps, req)
  requires LEnvironmentInvariant(ps.environment)
  requires ConstantsAllConsistentInv(ps)
  requires |ps.constants.config.replica_ids| == |ps.replicas| == |ps'.constants.config.replica_ids| == |ps'.replicas|
  requires 0 <= idx < |ps'.replicas|
  requires ClientNeverSentHigherSequenceNumberRequest(ps, req)
  ensures  SequenceNumberReplicaInv(ps'.replicas[idx].replica, req)
{
  var id := ps.constants.config.replica_ids[idx];
  if exists other_index, ios :: RslNextOneReplica(ps, ps', other_index, ios)
  {
    var other_index, ios :| RslNextOneReplica(ps, ps', other_index, ios);
    if other_index != idx
    {
      assert SequenceNumberReplicaInv(ps.replicas[idx].replica, req);
      assert ps'.replicas[idx].replica == ps.replicas[idx].replica;
      assert SequenceNumberReplicaInv(ps'.replicas[idx].replica, req);
    }
    else
    {
      lemma_ReplicaNextPreservesSequenceNumberReplicaInv(ps, ps', idx, ios, req);
    }
  }
}

/////////////////////////////////
// STATE INVARIANT - OVERALL
/////////////////////////////////

lemma lemma_SequenceNumberStateInvHolds(b:Behavior<RslState>, asp:AssumptionParameters, i:int)
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  ensures  SequenceNumberStateInv(b[i], asp.persistent_request)
{
  lemma_LEnvironmentInvariantHolds(b, asp, i);
  lemma_ConstantsAllConsistent(b, asp.c, i);

  if i > 0
  {
    lemma_SequenceNumberStateInvHolds(b, asp, i-1);
    lemma_ConstantsAllConsistent(b, asp.c, i-1);
    lemma_LEnvironmentInvariantHolds(b, asp, i-1);
    lemma_AssumptionsMakeValidTransition(b, asp.c, i-1);

    var ps := b[i-1];
    var ps' := b[i];
    assert RslNext(ps, ps');
    forall idx | 0 <= idx < |ps'.replicas|
      ensures SequenceNumberReplicaInv(ps'.replicas[idx].replica, asp.persistent_request)
    {
      TemporalDeduceFromAlways(0, i-1, ClientNeverSentHigherSequenceNumberRequestTemporal(b, asp));
      assert sat(i-1, ClientNeverSentHigherSequenceNumberRequestTemporal(b, asp));
      assert ClientNeverSentHigherSequenceNumberRequest(ps, asp.persistent_request);
      lemma_PaxosNextPreservesSequenceNumberReplicaInv(ps, ps', idx, asp.persistent_request);
    }
    forall p | p in ps'.environment.sentPackets && p.src in ps.constants.config.replica_ids
      ensures SequenceNumberPacketInv(p, asp.persistent_request)
    {
      if p !in ps.environment.sentPackets
      {
        var idx, ios := lemma_ActionThatSendsPacketIsActionOfSource(ps, ps', p);
        lemma_SequenceNumberPacketInvHolds(ps, ps', idx, ios, p, asp.persistent_request);
      }
    }
  }
}

///////////////////////////
// USEFUL COROLLARIES
///////////////////////////

lemma lemma_SequenceNumberReplyCacheInvHolds(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  ensures  SequenceNumberReplyCacheInv(b[i].replicas[idx].replica.executor.reply_cache, asp.persistent_request)
{
  lemma_SequenceNumberStateInvHolds(b, asp, i);
}

lemma lemma_RequestNeverHitsInReplyCache(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  i:int,
  idx:int,
  ios:seq<RslIo>,
  inp:RslPacket
  )
  requires LivenessAssumptions(b, asp)
  requires RslNextOneReplica(b[i], b[i+1], idx, ios)
  requires 0 <= idx < |b[i].replicas|
  requires 0 <= idx < |b[i+1].replicas|
  requires idx in asp.live_quorum
  requires inp.src == asp.persistent_request.client
  requires inp.msg.RslMessage_Request?
  requires inp.msg.seqno_req == asp.persistent_request.seqno
  requires processing_sync_start <= i
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires LReplicaNextProcessRequest(b[i].replicas[idx].replica, b[i+1].replicas[idx].replica, inp, ExtractSentPacketsFromIos(ios))
  ensures  var reply_cache := b[i].replicas[idx].replica.executor.reply_cache;
           inp.src in reply_cache && reply_cache[inp.src].Reply? ==> inp.msg.seqno_req > reply_cache[inp.src].seqno
{
  var executor := b[i].replicas[idx].replica.executor;
  var reply_cache := executor.reply_cache;
  var sent_packets := ExtractSentPacketsFromIos(ios);
  if inp.src in reply_cache && reply_cache[inp.src].Reply? && inp.msg.seqno_req <= reply_cache[inp.src].seqno
  {
    lemma_SequenceNumberReplyCacheInvHolds(b, asp, i, idx);
    lemma_ConstantsAllConsistent(b, asp.c, i);

    assert inp.msg.seqno_req == reply_cache[inp.src].seqno;
    lemma_ReplyCacheStateInv(b, asp.c, i, inp.src);
    assert reply_cache[inp.src].client == inp.src;
    assert |sent_packets| == 1;
    var p := sent_packets[0];
    assert LIoOpSend(p) in ios;

    assert asp.synchrony_start <= i;
    assert p.src in SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids) + { asp.persistent_request.client };
    assert p.dst in SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids) + { asp.persistent_request.client };

    var delivery_step := lemma_PacketSentEventuallyDelivered(b, asp, i, p);
    lemma_ConstantsAllConsistent(b, asp.c, delivery_step);
    assert ReplyDeliveredDuringStep(b[delivery_step], asp.persistent_request);
    TemporalDeduceFromAlways(0, delivery_step, not(ReplyDeliveredTemporal(b, asp.persistent_request)));
    assert false;
  }
}

}
