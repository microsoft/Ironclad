include "AppInterface.i.dfy"
include "ReplicaState.i.dfy"
include "ProposerModel.i.dfy"
include "AcceptorModel.i.dfy"
include "LearnerModel.i.dfy"
include "ExecutorModel.i.dfy"
include "../Common/Util.i.dfy"

module LiveRSL__ReplicaModel_Part3_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__AppInterface_i
import opened LiveRSL__AcceptorModel_i
import opened LiveRSL__AcceptorState_i
import opened LiveRSL__CClockReading_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__ExecutorModel_i
import opened LiveRSL__ExecutorState_i
import opened LiveRSL__LearnerModel_i
import opened LiveRSL__LearnerState_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__ProposerModel_i
import opened LiveRSL__ProposerState_i
import opened LiveRSL__ReplicaState_i
import opened LiveRSL__Types_i
import opened Common__NodeIdentity_i
import opened Common__Util_i

method Replica_Next_Process_2b(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_Process_2b_Preconditions(replica, inp)
  ensures Replica_Next_Process_2b_Postconditions(replica, replica', inp, packets_sent)
  ensures replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set
  ensures replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == replica.executor.reply_cache
{
  var start_time := Time.GetDebugTimeTicks();

  ghost var r_replica := AbstractifyReplicaStateToLReplica(replica);
  ghost var opn := AbstractifyCPacketToRslPacket(inp).msg.opn_2b;
  ghost var op_learnable := r_replica.executor.ops_complete < opn || (r_replica.executor.ops_complete == opn && r_replica.executor.next_op_to_execute.OutstandingOpUnknown?);

  var copn := inp.msg.opn_2b;
  var cop_learnable := replica.executor.ops_complete.n < copn.n || (replica.executor.ops_complete.n == copn.n && replica.executor.next_op_to_execute.COutstandingOpUnknown?);

  assert op_learnable <==> cop_learnable;

  if cop_learnable {
    var newLearner := LearnerModel_Process2b(replica.learner, replica.executor, inp);
    replica' := replica.(learner := newLearner);
  } else {
    replica' := replica;
  }
  packets_sent := Broadcast(CBroadcastNop);

  var end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("Replica_Next_Process_2b", start_time, end_time);
}

method Replica_Next_Spontaneous_MaybeEnterNewViewAndSend1a(replica:ReplicaState) returns (replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(replica)
  ensures Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions(replica, replica', packets_sent)
  ensures replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set
  ensures replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == replica.executor.reply_cache
{
  var start_time := Time.GetDebugTimeTicks();
  var newProposer, packets := ProposerMaybeEnterNewViewAndSend1a(replica.proposer);
  replica' := replica.(proposer := newProposer);
  packets_sent := Broadcast(packets);
  //lemma_AbstractifySetOfCPacketsToSetOfRslPackets_properties(packets_sent);
  //lemma_AbstractifyCPacketToRslPacket_src(packets_sent, replica.constants.all.config.replica_ids[replica.constants.my_index]);
  var end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("Replica_Next_Spontaneous_MaybeEnterNewViewAndSend1a", start_time, end_time);
}

method Replica_Next_Spontaneous_MaybeEnterPhase2(replica:ReplicaState) returns (replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_MaybeEnterPhase2_Preconditions(replica)
  ensures Replica_Next_MaybeEnterPhase2_Postconditions(replica, replica', packets_sent)
  ensures replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set
  ensures replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == replica.executor.reply_cache
{
  var start_time := Time.GetDebugTimeTicks();
  var newProposer, packets := ProposerMaybeEnterPhase2(replica.proposer, replica.acceptor.log_truncation_point);
  replica' := replica.(proposer := newProposer);
  packets_sent := Broadcast(packets);
  //lemma_AbstractifySetOfCPacketsToSetOfRslPackets_properties(packets_sent);
  //lemma_AbstractifyCPacketToRslPacket_src(packets_sent, replica.constants.all.config.replica_ids[replica.constants.my_index]);
  var end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("Replica_Next_Spontaneous_MaybeEnterPhase2", start_time, end_time);
}

method Replica_Next_Spontaneous_MaybeNominateValueAndSend2a(replica:ReplicaState, clock:CClockReading) returns (replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Preconditions(replica)
  ensures Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Postconditions(replica, replica', clock, packets_sent)
  ensures replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set
  ensures replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == replica.executor.reply_cache
{
  var start_time := Time.GetDebugTimeTicks();
  var newProposer, packets := ProposerMaybeNominateValueAndSend2a(replica.proposer, clock.t, replica.acceptor.log_truncation_point);
  replica' := replica.(proposer := newProposer);
  packets_sent := Broadcast(packets);
  //lemma_AbstractifySetOfCPacketsToSetOfRslPackets_properties(packets_sent);
  //lemma_AbstractifyCPacketToRslPacket_src(packets_sent, replica.constants.all.config.replica_ids[replica.constants.my_index]);
  var end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("Replica_Next_Spontaneous_MaybeNominateValueAndSend2a", start_time, end_time);
}


} 
