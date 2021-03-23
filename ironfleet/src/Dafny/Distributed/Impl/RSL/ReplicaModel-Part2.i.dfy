include "AppInterface.i.dfy"
include "ReplicaState.i.dfy"
include "ProposerModel.i.dfy"
include "AcceptorModel.i.dfy"
include "LearnerModel.i.dfy"
include "ExecutorModel.i.dfy"
include "../Common/Util.i.dfy"

module LiveRSL__ReplicaModel_Part2_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__AcceptorState_i
import opened LiveRSL__AcceptorModel_i
import opened LiveRSL__AppInterface_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__ExecutorState_i
import opened LiveRSL__ExecutorModel_i
import opened LiveRSL__LearnerState_i
import opened LiveRSL__LearnerModel_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__ProposerState_i
import opened LiveRSL__ProposerModel_i
import opened LiveRSL__ReplicaConstantsState_i
import opened LiveRSL__ReplicaState_i
import opened LiveRSL__Types_i
import opened Common__NodeIdentity_i
import opened Common__Util_i

method ProposerSrcNotPresent(proposer:ProposerState, packet:CPacket) returns (b:bool)
  requires ProposerIsValid(proposer)
  ensures b == forall other_packet :: other_packet in proposer.received_1b_packets ==> other_packet.src != packet.src
{
  b := forall other_packet :: other_packet in proposer.received_1b_packets ==> other_packet.src != packet.src;
}

method ReplicaNextProcess1bIgnore(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_Process_1b_Preconditions(replica, inp)
  requires || inp.src !in replica.proposer.constants.all.config.replica_ids
           || inp.msg.bal_1b != replica.proposer.max_ballot_i_sent_1a
           || replica.proposer.current_state != 1
  ensures  Replica_Next_Process_1b_Postconditions(replica, replica', inp, packets_sent)
  ensures  replica' == replica
{
  /*
  if (AbstractifyCPacketToRslPacket(inp).src in AbstractifyReplicaStateToLReplica(replica).proposer.constants.all.config.replica_ids) {
    var hi1 := AbstractifyCPacketToRslPacket(inp).src;
    reveal_AbstractifyEndPointsToNodeIdentities();
    var ep1 :| ep1 in replica.proposer.constants.all.config.replica_ids && AbstractifyEndPointToNodeIdentity(ep1) == hi1;
    var ep2 := inp.src;
    lemma_AbstractifyEndPointToNodeIdentity_injective(ep1, ep2);
    assert ep1 == ep2;
    assert false;
  }
  assert !(AbstractifyCPacketToRslPacket(inp).src in AbstractifyReplicaStateToLReplica(replica).proposer.constants.all.config.replica_ids);
  */
  replica' := replica;
  packets_sent := Broadcast(CBroadcastNop);
}

method ReplicaNextProcess1bAlreadyHave1bFromSource(
  replica:ReplicaState,
  inp:CPacket
  ) returns (
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_1b_Preconditions(replica, inp)
  requires !(forall other_packet :: other_packet in replica.proposer.received_1b_packets ==> other_packet.src != inp.src)
  ensures  Replica_Next_Process_1b_Postconditions(replica, replica', inp, packets_sent)
  ensures  replica' == replica
{
  lemma_AbstractifyEndPointsToNodeIdentities_properties(replica.constants.all.config.replica_ids);
  lemma_AbstractifySetOfCPacketsToSetOfRslPackets_srcMembership(replica.proposer.received_1b_packets, inp.src);
  replica' := replica;
  packets_sent := Broadcast(CBroadcastNop);
}

method ReplicaNextProcess1bActual(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_Process_1b_Preconditions(replica, inp)
  requires inp.src in replica.proposer.constants.all.config.replica_ids
  requires inp.msg.bal_1b == replica.proposer.max_ballot_i_sent_1a
  requires replica.proposer.current_state == 1
  requires forall other_packet :: other_packet in replica.proposer.received_1b_packets ==> other_packet.src != inp.src
  ensures  Replica_Next_Process_1b_Postconditions(replica, replica', inp, packets_sent)
  ensures  replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set
  ensures  replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == replica.executor.reply_cache
{
  lemma_AbstractifyEndPointsToNodeIdentities_properties(replica.constants.all.config.replica_ids);
  lemma_AbstractifySetOfCPacketsToSetOfRslPackets_srcMembership(replica.proposer.received_1b_packets, inp.src);
    
  packets_sent := Broadcast(CBroadcastNop);
  lemma_AbstractifyEndPointsToNodeIdentities_properties(replica.constants.all.config.replica_ids);
  //lemma_AbstractifySetOfCPacketsToSetOfRslPackets_properties(packets_sent);
  lemma_AbstractifySetOfCPacketsToSetOfRslPackets_srcMembership(replica.proposer.received_1b_packets, inp.src);
  var newProposer := ProposerProcess1b(replica.proposer, inp);
  var newAcceptor:= NextAcceptorState_TruncateLog(replica.acceptor, inp.msg.log_truncation_point);
  replica' := replica.(proposer := newProposer,
                       acceptor := newAcceptor);
  assert LProposerProcess1b(AbstractifyReplicaStateToLReplica(replica).proposer, AbstractifyReplicaStateToLReplica(replica').proposer, AbstractifyCPacketToRslPacket(inp));
}

method Replica_Next_Process_1b(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_Process_1b_Preconditions(replica, inp)
  ensures  Replica_Next_Process_1b_Postconditions(replica, replica', inp, packets_sent)
  ensures  replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set
  ensures  replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == replica.executor.reply_cache
{
  var start_time := Time.GetDebugTimeTicks();

  if || inp.src !in replica.proposer.constants.all.config.replica_ids
     || inp.msg.bal_1b != replica.proposer.max_ballot_i_sent_1a
     || replica.proposer.current_state != 1 {
     replica', packets_sent := ReplicaNextProcess1bIgnore(replica, inp);
     var end_time := Time.GetDebugTimeTicks();
     RecordTimingSeq("Replica_Next_Process_1b_discard", start_time, end_time);
  }
  else {
    var srcNotPresent := ProposerSrcNotPresent(replica.proposer, inp);
    if srcNotPresent {
      replica', packets_sent := ReplicaNextProcess1bActual(replica, inp);
      var end_time := Time.GetDebugTimeTicks();
      RecordTimingSeq("Replica_Next_Process_1b_use", start_time, end_time);
    }
    else {
      replica', packets_sent := ReplicaNextProcess1bAlreadyHave1bFromSource(replica, inp);
      var end_time := Time.GetDebugTimeTicks();
      RecordTimingSeq("Replica_Next_Process_1b_discard", start_time, end_time);
    }
  }
}

method Replica_Next_Process_StartingPhase2(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_Process_StartingPhase2_Preconditions(replica, inp)
  ensures Replica_Next_Process_StartingPhase2_Postconditions(replica, replica', inp, packets_sent)
  ensures replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set
  ensures replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == replica.executor.reply_cache
{
  var start_time := Time.GetDebugTimeTicks();
  var newExecutor, packets := ExecutorProcessStartingPhase2(replica.executor, inp);
  replica' := replica.(executor := newExecutor);
  packets_sent := Broadcast(packets);
  //lemma_AbstractifySetOfCPacketsToSetOfRslPackets_properties(packets_sent);
  //lemma_AbstractifyCPacketToRslPacket_src(packets_sent, replica.constants.all.config.replica_ids[replica.constants.my_index]);
  var end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("Replica_Next_Process_StartingPhase2", start_time, end_time);
}


method ReplicaNextProcess2aIgnore(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_Process_2a_Preconditions(replica, inp)
  requires || inp.src !in replica.acceptor.constants.all.config.replica_ids
           || !BalLeq(AbstractifyCBallotToBallot(replica.acceptor.maxBallot), AbstractifyCBallotToBallot(inp.msg.bal_2a))
           || inp.msg.opn_2a.n > replica.acceptor.constants.all.params.max_integer_val
  ensures  Replica_Next_Process_2a_Postconditions(replica, replica', inp, packets_sent)
  ensures  replica' == replica
{
  replica' := replica;
  packets_sent := Broadcast(CBroadcastNop);
}


method ReplicaNextProcess2aActual(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_Process_2a_Preconditions(replica, inp)
  requires inp.src in replica.acceptor.constants.all.config.replica_ids
  requires BalLeq(AbstractifyCBallotToBallot(replica.acceptor.maxBallot), AbstractifyCBallotToBallot(inp.msg.bal_2a))
  requires inp.msg.opn_2a.n <= replica.acceptor.constants.all.params.max_integer_val
  ensures  Replica_Next_Process_2a_Postconditions(replica, replica', inp, packets_sent)
  ensures  replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set
  ensures  replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == replica.executor.reply_cache
{
  assert replica.constants.all.params.max_integer_val > replica.constants.all.params.max_log_length > 0;
  var maxLogLengthMinus1:uint64 := replica.acceptor.constants.all.params.max_log_length - 1;
  var newLogTruncationPoint := replica.acceptor.log_truncation_point.n;

  //if (inp.msg.opn_2a.n - newLogTruncationPoint > maxLogLengthMinus1) {
  //    newLogTruncationPoint := inp.msg.opn_2a.n - replica.acceptor.constants.all.params.max_log_length + 1;
  //}

  var newAcceptor, packets := NextAcceptorState_Phase2(replica.acceptor, inp.msg, inp.src);
  replica' := replica.(acceptor := newAcceptor);
  packets_sent := Broadcast(packets);
}


method Replica_Next_Process_2a(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_Process_2a_Preconditions(replica, inp)
  ensures  Replica_Next_Process_2a_Postconditions(replica, replica', inp, packets_sent)
  ensures  replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set
  ensures  replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set
  ensures  replica'.executor.reply_cache == replica.executor.reply_cache
{
  var start_time := Time.GetDebugTimeTicks();
//  lemma_AbstractifyEndPointsToNodeIdentities_properties(replica.constants.all.config.replica_ids);
  var ballot_leq := CBalLeq(replica.acceptor.maxBallot, inp.msg.bal_2a);
  if (&& inp.src in replica.acceptor.constants.all.config.replica_ids
      && ballot_leq
      //&& replica.acceptor.log_truncation_point.n <= inp.msg.opn_2a.n
      && inp.msg.opn_2a.n <= replica.acceptor.constants.all.params.max_integer_val)
  {
    replica', packets_sent := ReplicaNextProcess2aActual(replica, inp);
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("Replica_Next_Process_2a_use", start_time, end_time);
  }
  else
  {
    replica', packets_sent := ReplicaNextProcess2aIgnore(replica, inp);
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("Replica_Next_Process_2a_discard", start_time, end_time);
  }
  //lemma_AbstractifySetOfCPacketsToSetOfRslPackets_properties(packets_sent);
  //lemma_AbstractifyCPacketToRslPacket_src(packets_sent, replica.constants.all.config.replica_ids[replica.constants.my_index]);
}

} 
