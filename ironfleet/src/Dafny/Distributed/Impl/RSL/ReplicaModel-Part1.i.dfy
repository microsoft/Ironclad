include "AppInterface.i.dfy"
include "ReplicaState.i.dfy"
include "ProposerModel.i.dfy"
include "AcceptorModel.i.dfy"
include "LearnerModel.i.dfy"
include "ExecutorModel.i.dfy"
include "../Common/Util.i.dfy"

module LiveRSL__ReplicaModel_Part1_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__AcceptorState_i
import opened LiveRSL__AcceptorModel_i
import opened LiveRSL__AppInterface_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__ElectionState_i
import opened LiveRSL__ExecutorModel_i
import opened LiveRSL__LearnerState_i
import opened LiveRSL__LearnerModel_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__ProposerState_i
import opened LiveRSL__ProposerModel_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ReplicaConstantsState_i
import opened LiveRSL__ReplicaState_i
import opened LiveRSL__Types_i

method InitReplicaState(constants:ReplicaConstantsState) returns (replica:ReplicaState, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>, reply_cache_mutable:MutableMap<EndPoint, CReply>)
  requires ReplicaConstantsState_IsValid(constants)
  ensures ReplicaStateIsValid(replica)
  ensures replica.constants == constants
  ensures LReplicaInit(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaConstantsStateToLReplicaConstants(constants))
  ensures MutableSet.SetOf(cur_req_set) == replica.proposer.election_state.cur_req_set
  ensures MutableSet.SetOf(prev_req_set) == replica.proposer.election_state.prev_req_set
  ensures fresh(cur_req_set) && fresh(prev_req_set) && cur_req_set != prev_req_set
  ensures fresh(reply_cache_mutable)
  ensures replica.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
{
  var proposer;
  proposer, cur_req_set, prev_req_set := InitProposerState(constants);
  var acceptor := InitAcceptorState(constants);
  var learner := LearnerState_Init(constants);
  var executor;
  executor, reply_cache_mutable := ExecutorInit(constants);

  replica := ReplicaState(
       constants,
       0,
       proposer,
       acceptor,
       learner,
       executor
       );
  assert AbstractifyReplicaStateToLReplica(replica).constants == AbstractifyReplicaConstantsStateToLReplicaConstants(constants);
}

method ReplicaNextProcessRequestImplCaseUncached(
  replica:ReplicaState,
  inp:CPacket,
  cur_req_set:MutableSet<CRequestHeader>,
  prev_req_set:MutableSet<CRequestHeader>,
  reply_cache_mutable:MutableMap<EndPoint, CReply>
  ) returns (
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_Request_Preconditions(replica, inp)
  requires cur_req_set != prev_req_set
  requires MutableSet.SetOf(cur_req_set) == replica.proposer.election_state.cur_req_set
  requires MutableSet.SetOf(prev_req_set) == replica.proposer.election_state.prev_req_set
  requires replica.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
  requires inp.src !in MutableMap.MapOf(reply_cache_mutable)
  modifies cur_req_set, prev_req_set, reply_cache_mutable
  ensures  Replica_Next_Process_Request_Postconditions(replica, replica', inp, packets_sent)
  ensures  MutableSet.SetOf(cur_req_set) == replica'.proposer.election_state.cur_req_set
  ensures  MutableSet.SetOf(prev_req_set) == replica'.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
{
  //var start_time := Time.GetDebugTimeTicks();
  lemma_AbstractifyCReplyCacheToReplyCache_properties(replica.executor.reply_cache);
  ghost var s := AbstractifyReplicaStateToLReplica(replica);
  ghost var received_packet := AbstractifyCPacketToRslPacket(inp);

  assert received_packet.src !in s.executor.reply_cache;
  var newProposer := ProposerProcessRequest(replica.proposer, inp, cur_req_set, prev_req_set);
  replica' := replica.(proposer := newProposer);
  ghost var s' := AbstractifyReplicaStateToLReplica(replica');
  packets_sent := Broadcast(CBroadcastNop);
  assert OutboundPacketsIsValid(packets_sent);
  var notCachedTime := Time.GetDebugTimeTicks();
  //RecordTimingSeq("Replica_Next_Process_Request_isNotCached_ProposerProcessRequest", start_time, notCachedTime);
  assert LProposerProcessRequest(s.proposer, s'.proposer, received_packet);
  assert Replica_Next_Process_Request_Postconditions(replica, replica', inp, packets_sent);
}

method ReplicaNextProcessRequestImplCaseCachedNonReply(
  replica:ReplicaState,
  inp:CPacket,
  cur_req_set:MutableSet<CRequestHeader>,
  prev_req_set:MutableSet<CRequestHeader>,
  reply_cache_mutable:MutableMap<EndPoint, CReply>,
  cached_reply:CReply
  ) returns (
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_Request_Preconditions(replica, inp)
  requires cur_req_set != prev_req_set
  requires MutableSet.SetOf(cur_req_set) == replica.proposer.election_state.cur_req_set
  requires MutableSet.SetOf(prev_req_set) == replica.proposer.election_state.prev_req_set
  requires replica.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
  requires inp.src in MutableMap.MapOf(reply_cache_mutable)
  requires cached_reply == MutableMap.MapOf(reply_cache_mutable)[inp.src]
  requires !cached_reply.CReply?
  modifies cur_req_set, prev_req_set, reply_cache_mutable
  ensures  Replica_Next_Process_Request_Postconditions(replica, replica', inp, packets_sent)
  ensures  MutableSet.SetOf(cur_req_set) == replica'.proposer.election_state.cur_req_set
  ensures  MutableSet.SetOf(prev_req_set) == replica'.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
{
  //var start_time := Time.GetDebugTimeTicks();
  lemma_AbstractifyCReplyCacheToReplyCache_properties(replica.executor.reply_cache);
  ghost var s := AbstractifyReplicaStateToLReplica(replica);
  ghost var received_packet := AbstractifyCPacketToRslPacket(inp);

  assert !s.executor.reply_cache[received_packet.src].Reply?;
  var newProposer := ProposerProcessRequest(replica.proposer, inp, cur_req_set, prev_req_set);
  replica' := replica.(proposer := newProposer);
  packets_sent := Broadcast(CBroadcastNop);
  assert OutboundPacketsIsValid(packets_sent);
  var notReplyTime := Time.GetDebugTimeTicks();
  //RecordTimingSeq("Replica_Next_Process_Request_isNotReply_ProposerProcessRequest", start_time, notReplyTime);
  assert Replica_Next_Process_Request_Postconditions(replica, replica', inp, packets_sent);
}

method ReplicaNextProcessRequestImplCaseCachedOld(
  replica:ReplicaState,
  inp:CPacket,
  cur_req_set:MutableSet<CRequestHeader>,
  prev_req_set:MutableSet<CRequestHeader>,
  reply_cache_mutable:MutableMap<EndPoint, CReply>,
  cached_reply:CReply
  ) returns (
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_Request_Preconditions(replica, inp)
  requires cur_req_set != prev_req_set
  requires MutableSet.SetOf(cur_req_set) == replica.proposer.election_state.cur_req_set
  requires MutableSet.SetOf(prev_req_set) == replica.proposer.election_state.prev_req_set
  requires replica.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
  requires inp.src in MutableMap.MapOf(reply_cache_mutable)
  requires cached_reply == MutableMap.MapOf(reply_cache_mutable)[inp.src]
  requires cached_reply.CReply?
  requires inp.msg.seqno > cached_reply.seqno
  modifies cur_req_set, prev_req_set, reply_cache_mutable
  ensures  Replica_Next_Process_Request_Postconditions(replica, replica', inp, packets_sent)
  ensures  MutableSet.SetOf(cur_req_set) == replica'.proposer.election_state.cur_req_set
  ensures  MutableSet.SetOf(prev_req_set) == replica'.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
{
  //var start_time := Time.GetDebugTimeTicks();
  lemma_AbstractifyCReplyCacheToReplyCache_properties(replica.executor.reply_cache);
  ghost var s := AbstractifyReplicaStateToLReplica(replica);
  ghost var received_packet := AbstractifyCPacketToRslPacket(inp);

  assert AbstractifyCReplyToReply(replica.executor.reply_cache[inp.src]) == AbstractifyReplicaStateToLReplica(replica).executor.reply_cache[received_packet.src];
  assert received_packet.msg.seqno_req > s.executor.reply_cache[received_packet.src].seqno;
  var newProposer := ProposerProcessRequest(replica.proposer, inp, cur_req_set, prev_req_set);
  replica' := replica.(proposer := newProposer);
  packets_sent := Broadcast(CBroadcastNop);
  assert OutboundPacketsIsValid(packets_sent);
  var seqnoIsBeyondTime := Time.GetDebugTimeTicks();
  //RecordTimingSeq("Replica_Next_Process_Request_seqnoIsBeyond_ProposerProcessRequest", start_time, seqnoIsBeyondTime);
  assert LProposerProcessRequest(AbstractifyReplicaStateToLReplica(replica).proposer, AbstractifyReplicaStateToLReplica(replica').proposer, received_packet);
  assert Replica_Next_Process_Request_Postconditions(replica, replica', inp, packets_sent);
}

method ReplicaNextProcessRequestImplCaseCachedFresh(
  replica:ReplicaState,
  inp:CPacket,
  reply_cache_mutable:MutableMap<EndPoint, CReply>,
  cached_reply:CReply
  ) returns (
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_Request_Preconditions(replica, inp)
  requires replica.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
  requires inp.src in MutableMap.MapOf(reply_cache_mutable)
  requires cached_reply == MutableMap.MapOf(reply_cache_mutable)[inp.src]
  requires cached_reply.CReply?
  requires inp.msg.seqno <= cached_reply.seqno
  ensures  Replica_Next_Process_Request_Postconditions(replica, replica', inp, packets_sent)
  ensures  replica' == replica
{
  //var start_time := Time.GetDebugTimeTicks();
  lemma_AbstractifyCReplyCacheToReplyCache_properties(replica.executor.reply_cache);
  ghost var s := AbstractifyReplicaStateToLReplica(replica);
  ghost var received_packet := AbstractifyCPacketToRslPacket(inp);

  assert AbstractifyCReplyToReply(replica.executor.reply_cache[inp.src]) == AbstractifyReplicaStateToLReplica(replica).executor.reply_cache[received_packet.src];
  packets_sent := ExecutorProcessRequest(replica.executor, inp, reply_cache_mutable);
  assert OutboundPacketsIsValid(packets_sent);
  replica' := replica;
  var isCachedTime := Time.GetDebugTimeTicks();
  //RecordTimingSeq("Replica_Next_Process_Request_isCached_ExecutorProcessRequest", start_time, isCachedTime);
  assert Replica_Next_Process_Request_Postconditions(replica, replica', inp, packets_sent);
}

method Replica_Next_Process_Request(
  replica:ReplicaState,
  inp:CPacket,
  cur_req_set:MutableSet<CRequestHeader>,
  prev_req_set:MutableSet<CRequestHeader>,
  reply_cache_mutable:MutableMap<EndPoint, CReply>
  ) returns (
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_Request_Preconditions(replica, inp)
  requires cur_req_set != prev_req_set
  requires MutableSet.SetOf(cur_req_set) == replica.proposer.election_state.cur_req_set
  requires MutableSet.SetOf(prev_req_set) == replica.proposer.election_state.prev_req_set
  requires replica.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
  modifies cur_req_set, prev_req_set, reply_cache_mutable
  ensures  Replica_Next_Process_Request_Postconditions(replica, replica', inp, packets_sent)
  ensures  MutableSet.SetOf(cur_req_set) == replica'.proposer.election_state.cur_req_set
  ensures  MutableSet.SetOf(prev_req_set) == replica'.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
{
  //var start_time := Time.GetDebugTimeTicks();
  //var afterCheck_time := Time.GetDebugTimeTicks();
  //RecordTimingSeq("Replica_Next_Process_Request_checkIsCached", start_time, afterCheck_time);
  var cached, cached_reply := reply_cache_mutable.TryGetValue(inp.src);
  if !cached { // ==> inp.src !in replica.executor.reply_cache {
    replica', packets_sent := ReplicaNextProcessRequestImplCaseUncached(replica, inp, cur_req_set, prev_req_set, reply_cache_mutable);
  } else if (!cached_reply.CReply?){
    replica', packets_sent := ReplicaNextProcessRequestImplCaseCachedNonReply(replica, inp, cur_req_set, prev_req_set, reply_cache_mutable, cached_reply);
  } else if (inp.msg.seqno > cached_reply.seqno) {
    replica', packets_sent := ReplicaNextProcessRequestImplCaseCachedOld(replica, inp, cur_req_set, prev_req_set, reply_cache_mutable, cached_reply);
  } else {
    replica', packets_sent := ReplicaNextProcessRequestImplCaseCachedFresh(replica, inp, reply_cache_mutable, cached_reply);
  }
  assert OutboundPacketsIsValid(packets_sent);
  //var end_time := Time.GetDebugTimeTicks();
  //RecordTimingSeq("Replica_Next_Process_Request", start_time, end_time);
}
method Replica_Next_Process_1a(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_Process_1a_Preconditions(replica, inp)
  ensures Replica_Next_Process_1a_Postconditions(replica, replica', inp, packets_sent)
  ensures replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set
  ensures replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == replica.executor.reply_cache
{
  //print("Replica_Next_Process_1a: Calling NextAcceptorState_Phase1\n");
  //var start_time := Time.GetDebugTimeTicks();
  var newAcceptor, packets := NextAcceptorState_Phase1(replica.acceptor, inp.msg, inp.src);
  replica' := replica.(acceptor := newAcceptor);
  assert ConstantsStayConstant(replica.acceptor, newAcceptor);
  assert AbstractifyAcceptorStateToAcceptor(replica.acceptor).constants == AbstractifyAcceptorStateToAcceptor(newAcceptor).constants;
  assert AbstractifyAcceptorStateToAcceptor(replica.acceptor).constants == AbstractifyAcceptorStateToAcceptor(replica'.acceptor).constants;
  packets_sent := Broadcast(packets);
  //var end_time := Time.GetDebugTimeTicks();
  //RecordTimingSeq("Replica_Next_Process_1a", start_time, end_time);
}

} 
