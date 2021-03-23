include "Configuration.i.dfy"
include "Environment.i.dfy"
include "Types.i.dfy"
include "ClockReading.i.dfy"
include "Constants.i.dfy"
include "Proposer.i.dfy"
include "Acceptor.i.dfy"
include "Learner.i.dfy"
include "Executor.i.dfy"

module LiveRSL__Replica_i {
import opened LiveRSL__Configuration_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Types_i
import opened LiveRSL__ClockReading_i
import opened LiveRSL__Constants_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Acceptor_i
import opened LiveRSL__Learner_i
import opened LiveRSL__Executor_i
import opened LiveRSL__Broadcast_i
import opened LiveRSL__Message_i
import opened Common__UpperBound_s
import opened Environment_s

datatype LReplica = LReplica(
  constants:LReplicaConstants,
  nextHeartbeatTime:int,
  proposer:LProposer,
  acceptor:LAcceptor,
  learner:LLearner,
  executor:LExecutor)

predicate LReplicaInit(r:LReplica, c:LReplicaConstants)
  requires WellFormedLConfiguration(c.all.config)
{
  && r.constants == c
  && r.nextHeartbeatTime == 0
  && LProposerInit(r.proposer, c)
  && LAcceptorInit(r.acceptor, c)
  && LLearnerInit(r.learner, c)
  && LExecutorInit(r.executor, c)
}

predicate LReplicaNextProcessInvalid(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
  requires received_packet.msg.RslMessage_Invalid?
{
  && s' == s
  && sent_packets == []
}

predicate LReplicaNextProcessRequest(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
  requires received_packet.msg.RslMessage_Request?
{
  if  && received_packet.src in s.executor.reply_cache
      && s.executor.reply_cache[received_packet.src].Reply?
      && received_packet.msg.seqno_req <= s.executor.reply_cache[received_packet.src].seqno then
     && LExecutorProcessRequest(s.executor, received_packet, sent_packets)
     && s' == s
  else
    && LProposerProcessRequest(s.proposer, s'.proposer, received_packet)
    && sent_packets == []
    && s' == s.(proposer := s'.proposer)
}

predicate LReplicaNextProcess1a(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
  requires received_packet.msg.RslMessage_1a?
{
  && LAcceptorProcess1a(s.acceptor, s'.acceptor, received_packet, sent_packets)
  // UNCHANGED
  && s' == s.(acceptor := s'.acceptor)
}

predicate LReplicaNextProcess1b(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
  requires received_packet.msg.RslMessage_1b?
{
  if  && received_packet.src in s.proposer.constants.all.config.replica_ids
      && received_packet.msg.bal_1b == s.proposer.max_ballot_i_sent_1a
      && s.proposer.current_state == 1
      && (forall other_packet :: other_packet in s.proposer.received_1b_packets ==> other_packet.src != received_packet.src) then
    && LProposerProcess1b(s.proposer, s'.proposer, received_packet)
    && LAcceptorTruncateLog(s.acceptor, s'.acceptor, received_packet.msg.log_truncation_point)
    && sent_packets == []
    && s' == s.(proposer := s'.proposer, acceptor := s'.acceptor)
  else
    s' == s && sent_packets == []
}

predicate LReplicaNextProcessStartingPhase2(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
  requires received_packet.msg.RslMessage_StartingPhase2?
{
  && LExecutorProcessStartingPhase2(s.executor, s'.executor, received_packet, sent_packets)
  && s' == s.(executor := s'.executor)
}

predicate LReplicaNextProcess2a(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
  requires received_packet.msg.RslMessage_2a?
{
  var m := received_packet.msg;
  if  && received_packet.src in s.acceptor.constants.all.config.replica_ids
      && BalLeq(s.acceptor.max_bal, m.bal_2a)
      && LeqUpperBound(m.opn_2a, s.acceptor.constants.all.params.max_integer_val) then
    && LAcceptorProcess2a(s.acceptor, s'.acceptor, received_packet, sent_packets)
    && s' == s.(acceptor := s'.acceptor)
  else
    s' == s && sent_packets == []
}

predicate LReplicaNextProcess2b(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
  requires received_packet.msg.RslMessage_2b?
{
  var opn := received_packet.msg.opn_2b;
  var op_learnable := s.executor.ops_complete < opn || (s.executor.ops_complete == opn && s.executor.next_op_to_execute.OutstandingOpUnknown?);
  if op_learnable then
    && LLearnerProcess2b(s.learner, s'.learner, received_packet)
    && sent_packets == []
    && s' == s.(learner := s'.learner)
  else
    && s' == s
    && sent_packets == []
}

predicate LReplicaNextProcessReply(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
  requires received_packet.msg.RslMessage_Reply?
{
  && sent_packets == []
  && s' == s
}

predicate LReplicaNextProcessAppStateSupply(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
  requires received_packet.msg.RslMessage_AppStateSupply?
{
  if received_packet.src in s.executor.constants.all.config.replica_ids && received_packet.msg.opn_state_supply > s.executor.ops_complete then
    && LLearnerForgetOperationsBefore(s.learner, s'.learner, received_packet.msg.opn_state_supply)
    && LExecutorProcessAppStateSupply(s.executor, s'.executor, received_packet)
    && sent_packets == []
    && s' == s.(learner := s'.learner, executor := s'.executor)
  else
    s' == s && sent_packets == []
}

predicate LReplicaNextProcessAppStateRequest(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
  requires received_packet.msg.RslMessage_AppStateRequest?
{
  && LExecutorProcessAppStateRequest(s.executor, s'.executor, received_packet, sent_packets)
  && s' == s.(executor := s'.executor)
}

predicate LReplicaNextProcessHeartbeat(s:LReplica, s':LReplica, received_packet:RslPacket, clock:int, sent_packets:seq<RslPacket>)
  requires received_packet.msg.RslMessage_Heartbeat?
{
  && LProposerProcessHeartbeat(s.proposer, s'.proposer, received_packet, clock)
  && LAcceptorProcessHeartbeat(s.acceptor, s'.acceptor, received_packet)
  && sent_packets == []
  && s' == s.(proposer := s'.proposer, acceptor := s'.acceptor)
}

predicate LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s:LReplica, s':LReplica, sent_packets:seq<RslPacket>)
{
  && LProposerMaybeEnterNewViewAndSend1a(s.proposer, s'.proposer, sent_packets)
  && s' == s.(proposer := s'.proposer)
}

predicate LReplicaNextSpontaneousMaybeEnterPhase2(s:LReplica, s':LReplica, sent_packets:seq<RslPacket>)
{
  && LProposerMaybeEnterPhase2(s.proposer, s'.proposer, s.acceptor.log_truncation_point, sent_packets)
  && s' == s.(proposer := s'.proposer)
}

predicate LReplicaNextReadClockMaybeNominateValueAndSend2a(s:LReplica, s':LReplica, clock:ClockReading, sent_packets:seq<RslPacket>)
{
  && LProposerMaybeNominateValueAndSend2a(s.proposer, s'.proposer, clock.t, s.acceptor.log_truncation_point, sent_packets)
  && s' == s.(proposer := s'.proposer)
}

predicate LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s:LReplica, s':LReplica, sent_packets:seq<RslPacket>)
{
  (exists opn ::
        && IsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config)
        && opn > s.acceptor.log_truncation_point
        && LAcceptorTruncateLog(s.acceptor, s'.acceptor, opn)
        && s' == s.(acceptor := s'.acceptor)
        && sent_packets == []
  )
  ||
  (exists opn ::
        && IsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config)
        && opn <= s.acceptor.log_truncation_point
        && s' == s
        && sent_packets == []
  )
}

predicate LReplicaNextSpontaneousMaybeMakeDecision(s:LReplica, s':LReplica, sent_packets:seq<RslPacket>)
{
  var opn := s.executor.ops_complete;
  if  && s.executor.next_op_to_execute.OutstandingOpUnknown?
      && opn in s.learner.unexecuted_learner_state
      && |s.learner.unexecuted_learner_state[opn].received_2b_message_senders| >= LMinQuorumSize(s.learner.constants.all.config) then
    && LExecutorGetDecision(s.executor, s'.executor, s.learner.max_ballot_seen, opn,
                           s.learner.unexecuted_learner_state[opn].candidate_learned_value)
    && s' == s.(executor := s'.executor)
    && sent_packets == []
  else
    s' == s && sent_packets == []
}

predicate LReplicaNextSpontaneousMaybeExecute(s:LReplica, s':LReplica, sent_packets:seq<RslPacket>)
{
  if  && s.executor.next_op_to_execute.OutstandingOpKnown?
      && LtUpperBound(s.executor.ops_complete, s.executor.constants.all.params.max_integer_val)
      && LReplicaConstantsValid(s.executor.constants) then
    var v := s.executor.next_op_to_execute.v;
    && LProposerResetViewTimerDueToExecution(s.proposer, s'.proposer, v)
    && LLearnerForgetDecision(s.learner, s'.learner, s.executor.ops_complete)
    && LExecutorExecute(s.executor, s'.executor, sent_packets)
    && s' == s.(proposer := s'.proposer, learner := s'.learner, executor := s'.executor)
  else
    s' == s && sent_packets == []
}

predicate LReplicaNextReadClockMaybeSendHeartbeat(s:LReplica, s':LReplica, clock:ClockReading, sent_packets:seq<RslPacket>)
{
  if clock.t < s.nextHeartbeatTime then
    s' == s && sent_packets == []
  else
    && s'.nextHeartbeatTime == UpperBoundedAddition(clock.t, s.constants.all.params.heartbeat_period, s.constants.all.params.max_integer_val)
    && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index,
                           RslMessage_Heartbeat(s.proposer.election_state.current_view,
                                                s.constants.my_index in s.proposer.election_state.current_view_suspectors,
                                                s.executor.ops_complete),
                           sent_packets)
    && s' == s.(nextHeartbeatTime := s'.nextHeartbeatTime)
}

predicate LReplicaNextReadClockCheckForViewTimeout(s:LReplica, s':LReplica, clock:ClockReading, sent_packets:seq<RslPacket>)
{
  && LProposerCheckForViewTimeout(s.proposer, s'.proposer, clock.t)
  && sent_packets == []
  && s' == s.(proposer := s'.proposer)
}

predicate LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s:LReplica, s':LReplica, clock:ClockReading, sent_packets:seq<RslPacket>)
{
  && LProposerCheckForQuorumOfViewSuspicions(s.proposer, s'.proposer, clock.t)
  && sent_packets == []
  && s' == s.(proposer := s'.proposer)
}

function {:opaque} ExtractSentPacketsFromIos(ios:seq<RslIo>) : seq<RslPacket>
  ensures forall p :: p in ExtractSentPacketsFromIos(ios) <==> LIoOpSend(p) in ios
{
  if |ios| == 0 then
    []
  else if ios[0].LIoOpSend? then
    [ios[0].s] + ExtractSentPacketsFromIos(ios[1..])
  else
    ExtractSentPacketsFromIos(ios[1..])
}

predicate LReplicaNextReadClockAndProcessPacket(s:LReplica, s':LReplica, ios:seq<RslIo>)
  requires |ios| >= 1
  requires ios[0].LIoOpReceive?
  requires ios[0].r.msg.RslMessage_Heartbeat?
{
  && |ios| > 1
  && ios[1].LIoOpReadClock?
  && (forall io :: io in ios[2..] ==> io.LIoOpSend?)
  && LReplicaNextProcessHeartbeat(s, s', ios[0].r, ios[1].t, ExtractSentPacketsFromIos(ios))
}

predicate LReplicaNextProcessPacketWithoutReadingClock(s:LReplica, s':LReplica, ios:seq<RslIo>)
  requires |ios| >= 1
  requires ios[0].LIoOpReceive?
  requires !ios[0].r.msg.RslMessage_Heartbeat?
{
  && (forall io :: io in ios[1..] ==> io.LIoOpSend?)
  && var sent_packets := ExtractSentPacketsFromIos(ios);
    match ios[0].r.msg
       case RslMessage_Invalid => LReplicaNextProcessInvalid(s, s', ios[0].r, sent_packets)
       case RslMessage_Request(_, _) => LReplicaNextProcessRequest(s, s', ios[0].r, sent_packets)
       case RslMessage_1a(_) => LReplicaNextProcess1a(s, s', ios[0].r, sent_packets)
       case RslMessage_1b(_, _, _) => LReplicaNextProcess1b(s, s', ios[0].r, sent_packets)
       case RslMessage_StartingPhase2(_, _) => LReplicaNextProcessStartingPhase2(s, s', ios[0].r, sent_packets)
       case RslMessage_2a(_, _, _) => LReplicaNextProcess2a(s, s', ios[0].r, sent_packets)
       case RslMessage_2b(_, _, _) => LReplicaNextProcess2b(s, s', ios[0].r, sent_packets)
       case RslMessage_Reply(_, _) => LReplicaNextProcessReply(s, s', ios[0].r, sent_packets)
       case RslMessage_AppStateRequest(_, _) => LReplicaNextProcessAppStateRequest(s, s', ios[0].r, sent_packets)
       case RslMessage_AppStateSupply(_, _, _, _) => LReplicaNextProcessAppStateSupply(s, s', ios[0].r, sent_packets)
}

predicate LReplicaNextProcessPacket(s:LReplica, s':LReplica, ios:seq<RslIo>)
{
  && |ios| >= 1
  && if ios[0].LIoOpTimeoutReceive? then
      s' == s && |ios| == 1
    else
      (&& ios[0].LIoOpReceive?
       && if ios[0].r.msg.RslMessage_Heartbeat? then
           LReplicaNextReadClockAndProcessPacket(s, s', ios)
         else
           LReplicaNextProcessPacketWithoutReadingClock(s, s', ios)
      )
}

function LReplicaNumActions() : int
{
  10
}

predicate SpontaneousIos(ios:seq<RslIo>, clocks:int)
  requires 0<=clocks<=1
{
  && clocks <= |ios|
  && (forall i :: 0<=i<clocks ==> ios[i].LIoOpReadClock?)
  && (forall i :: clocks<=i<|ios| ==> ios[i].LIoOpSend?)
}

function SpontaneousClock(ios:seq<RslIo>) : ClockReading
{
  if SpontaneousIos(ios, 1) then ClockReading(ios[0].t) else ClockReading(0) // nonsense to avoid putting a precondition on this function
}

predicate LReplicaNoReceiveNext(s:LReplica, nextActionIndex:int, s':LReplica, ios:seq<RslIo>)
{
  var sent_packets := ExtractSentPacketsFromIos(ios);

  if nextActionIndex == 1 then
    && SpontaneousIos(ios, 0)
    && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s, s', sent_packets)
  else if nextActionIndex == 2 then
    && SpontaneousIos(ios, 0)
    && LReplicaNextSpontaneousMaybeEnterPhase2(s, s', sent_packets)
  else if nextActionIndex == 3 then
    && SpontaneousIos(ios, 1)
    && LReplicaNextReadClockMaybeNominateValueAndSend2a(s, s', SpontaneousClock(ios), sent_packets)
  else if nextActionIndex == 4 then
    && SpontaneousIos(ios, 0)
    && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', sent_packets)
  else if nextActionIndex == 5 then
    && SpontaneousIos(ios, 0)
    && LReplicaNextSpontaneousMaybeMakeDecision(s, s', sent_packets)
  else if nextActionIndex == 6 then
    && SpontaneousIos(ios, 0)
    && LReplicaNextSpontaneousMaybeExecute(s, s', sent_packets)
  else if nextActionIndex == 7 then
    && SpontaneousIos(ios, 1)
    && LReplicaNextReadClockCheckForViewTimeout(s, s', SpontaneousClock(ios), sent_packets)
  else if nextActionIndex == 8 then
    && SpontaneousIos(ios, 1)
    && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, s', SpontaneousClock(ios), sent_packets)
  else
    && nextActionIndex == 9
    && SpontaneousIos(ios, 1)
    && LReplicaNextReadClockMaybeSendHeartbeat(s, s', SpontaneousClock(ios), sent_packets)
}

datatype LScheduler = LScheduler(replica:LReplica, nextActionIndex:int)

predicate LSchedulerInit(s:LScheduler, c:LReplicaConstants)
  requires WellFormedLConfiguration(c.all.config)
{
  && LReplicaInit(s.replica, c)
  && s.nextActionIndex == 0
}

predicate LSchedulerNext(s:LScheduler, s':LScheduler, ios:seq<RslIo>)
{
  && s'.nextActionIndex == (s.nextActionIndex + 1) % LReplicaNumActions()
  && if s.nextActionIndex == 0 then
      LReplicaNextProcessPacket(s.replica, s'.replica, ios)
    else
      LReplicaNoReceiveNext(s.replica, s.nextActionIndex, s'.replica, ios)
}

} 
