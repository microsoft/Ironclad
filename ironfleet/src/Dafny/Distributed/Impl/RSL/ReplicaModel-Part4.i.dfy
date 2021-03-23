include "AppInterface.i.dfy"
include "ReplicaState.i.dfy"
include "ProposerModel.i.dfy"
include "AcceptorModel.i.dfy"
include "LearnerModel.i.dfy"
include "ExecutorModel.i.dfy"
include "../Common/Util.i.dfy"

module LiveRSL__ReplicaModel_Part4_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__Acceptor_i
import opened LiveRSL__AcceptorModel_i
import opened LiveRSL__AcceptorState_i
import opened LiveRSL__AppInterface_i
import opened LiveRSL__CClockReading_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__ElectionState_i
import opened LiveRSL__Executor_i
import opened LiveRSL__ExecutorModel_i
import opened LiveRSL__ExecutorState_i
import opened LiveRSL__LearnerModel_i
import opened LiveRSL__LearnerState_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__ProposerModel_i
import opened LiveRSL__ProposerState_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ReplicaState_i
import opened LiveRSL__Types_i
import opened Common__NodeIdentity_i
import opened Common__Util_i

method Replica_Next_Process_AppStateRequest(
  replica:ReplicaState,
  inp:CPacket,
  reply_cache_mutable:MutableMap<EndPoint, CReply>
  ) returns (
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_AppStateRequest_Preconditions(replica, inp)
  requires replica.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
  ensures  Replica_Next_Process_AppStateRequest_Postconditions(replica, replica', inp, packets_sent)
  ensures  replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set
  ensures  replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set
  ensures  replica'.executor == replica.executor
{
  var start_time := Time.GetDebugTimeTicks();
  var newExecutor, packets := ExecutorProcessAppStateRequest(replica.executor, inp, reply_cache_mutable);
  replica' := replica.(executor := newExecutor);
  packets_sent := packets;
  //lemma_AbstractifySetOfCPacketsToSetOfRslPackets_properties(packets_sent);
  //lemma_AbstractifyCPacketToRslPacket_src(packets_sent, replica.constants.all.config.replica_ids[replica.constants.my_index]);
  var end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("Replica_Next_Process_AppStateRequest", start_time, end_time);

  ghost var s := AbstractifyReplicaStateToLReplica(replica);
  ghost var s' := AbstractifyReplicaStateToLReplica(replica');
  ghost var received_packet := AbstractifyCPacketToRslPacket(inp);
  ghost var sent_packets := AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent);
  assert LExecutorProcessAppStateRequest(s.executor, s'.executor, received_packet, sent_packets);
  assert LReplicaNextProcessAppStateRequest(s, s', received_packet, sent_packets);
}

method Replica_Next_Process_Heartbeat(
  replica:ReplicaState,
  inp:CPacket,
  clock:uint64,
  cur_req_set:MutableSet<CRequestHeader>,
  prev_req_set:MutableSet<CRequestHeader>
  ) returns (
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_Heartbeat_Preconditions(replica, inp)
  requires cur_req_set != prev_req_set
  requires MutableSet.SetOf(cur_req_set) == replica.proposer.election_state.cur_req_set
  requires MutableSet.SetOf(prev_req_set) == replica.proposer.election_state.prev_req_set
  modifies cur_req_set, prev_req_set
  ensures  Replica_Next_Process_Heartbeat_Postconditions(replica, replica', inp, clock, packets_sent)
  ensures  MutableSet.SetOf(cur_req_set) == replica'.proposer.election_state.cur_req_set
  ensures  MutableSet.SetOf(prev_req_set) == replica'.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == replica.executor.reply_cache
{
  var start_time := Time.GetDebugTimeTicks();
  packets_sent := Broadcast(CBroadcastNop);
  assert OutboundPacketsIsValid(packets_sent);
  var newProposer := ProposerProcessHeartbeat(replica.proposer, inp, clock, cur_req_set, prev_req_set);
  var newAcceptor := NextAcceptorState_ProcessHeartbeat(replica.acceptor, inp.msg, inp.src);
  replica' := replica.(proposer := newProposer,
                      acceptor := newAcceptor);

  var end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("Replica_Next_Process_Heartbeat", start_time, end_time);

  ghost var s := AbstractifyReplicaStateToLReplica(replica);
  ghost var s' := AbstractifyReplicaStateToLReplica(replica');
  ghost var received_packet := AbstractifyCPacketToRslPacket(inp);
  ghost var sent_packets := AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent);
  assert LProposerProcessHeartbeat(s.proposer, s'.proposer, received_packet, clock as int);
  assert LAcceptorProcessHeartbeat(s.acceptor, s'.acceptor, received_packet);
  assert LReplicaNextProcessHeartbeat(s, s', received_packet, clock as int, sent_packets);
}

method {:timeLimitMultiplier 2} Replica_Next_ReadClock_CheckForViewTimeout(
  replica:ReplicaState,
  clock:CClockReading,
  cur_req_set:MutableSet<CRequestHeader>,
  prev_req_set:MutableSet<CRequestHeader>
  ) returns (
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_ReadClock_CheckForViewTimeout_Preconditions(replica)
  requires cur_req_set != prev_req_set
  requires MutableSet.SetOf(cur_req_set) == replica.proposer.election_state.cur_req_set
  requires MutableSet.SetOf(prev_req_set) == replica.proposer.election_state.prev_req_set
  modifies cur_req_set, prev_req_set
  ensures  Replica_Next_ReadClock_CheckForViewTimeout_Postconditions(replica, replica', clock, packets_sent)
  ensures  MutableSet.SetOf(cur_req_set) == replica'.proposer.election_state.cur_req_set
  ensures  MutableSet.SetOf(prev_req_set) == replica'.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == replica.executor.reply_cache
{
  var start_time := Time.GetDebugTimeTicks();
  var newProposer := ProposerCheckForViewTimeout(replica.proposer, clock.t, cur_req_set, prev_req_set);
  replica' := replica.(proposer := newProposer);
  packets_sent := Broadcast(CBroadcastNop);
  assert OutboundPacketsIsValid(packets_sent);
  assert OutboundPacketsHasCorrectSrc(packets_sent, replica.constants.all.config.replica_ids[replica.constants.my_index]);
  //lemma_AbstractifySetOfCPacketsToSetOfRslPackets_properties(packets_sent);
  var end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("Replica_Next_ReadClock_CheckForViewTimeout", start_time, end_time);

  ghost var s := AbstractifyReplicaStateToLReplica(replica);
  ghost var s' := AbstractifyReplicaStateToLReplica(replica');
  ghost var sent_packets := AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent);
  assert LProposerCheckForViewTimeout(s.proposer, s'.proposer, clock.t as int);
  assert LReplicaNextReadClockCheckForViewTimeout(s, s', AbstractifyCClockReadingToClockReading(clock), sent_packets);
}

method {:timeLimitMultiplier 2} Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions(
  replica:ReplicaState,
  clock:CClockReading,
  cur_req_set:MutableSet<CRequestHeader>,
  prev_req_set:MutableSet<CRequestHeader>
  ) returns (
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Preconditions(replica)
  requires cur_req_set != prev_req_set
  requires MutableSet.SetOf(cur_req_set) == replica.proposer.election_state.cur_req_set
  requires MutableSet.SetOf(prev_req_set) == replica.proposer.election_state.prev_req_set
  modifies cur_req_set, prev_req_set
  ensures  Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Postconditions(replica, replica', clock, packets_sent)
  ensures  MutableSet.SetOf(cur_req_set) == replica'.proposer.election_state.cur_req_set
  ensures  MutableSet.SetOf(prev_req_set) == replica'.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == replica.executor.reply_cache
{
  var start_time := Time.GetDebugTimeTicks();
  var newProposer := ProposerCheckForQuorumOfViewSuspicions(replica.proposer, clock.t, cur_req_set, prev_req_set);
  replica' := replica.(proposer := newProposer);
  packets_sent := Broadcast(CBroadcastNop);
  assert OutboundPacketsIsValid(packets_sent);
  assert OutboundPacketsHasCorrectSrc(packets_sent, replica.constants.all.config.replica_ids[replica.constants.my_index]);
  //lemma_AbstractifySetOfCPacketsToSetOfRslPackets_properties(packets_sent);
  var end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions", start_time, end_time);

  ghost var s := AbstractifyReplicaStateToLReplica(replica);
  ghost var s' := AbstractifyReplicaStateToLReplica(replica');
  ghost var sent_packets := AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent);
  assert LProposerCheckForQuorumOfViewSuspicions(s.proposer, s'.proposer, clock.t as int);
  assert LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, s', AbstractifyCClockReadingToClockReading(clock), sent_packets);
}


} 
