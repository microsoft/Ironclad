include "../../Protocol/RSL/Replica.i.dfy"
include "ReplicaConstantsState.i.dfy"
include "ProposerState.i.dfy"
include "AcceptorState.i.dfy"
include "LearnerState.i.dfy"
include "ExecutorState.i.dfy"
include "CClockReading.i.dfy"

module LiveRSL__ReplicaState_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__AcceptorState_i
import opened LiveRSL__AppInterface_i
import opened LiveRSL__CClockReading_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__ExecutorState_i
import opened LiveRSL__LearnerState_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__ProposerState_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ReplicaConstantsState_i

datatype ReplicaState = ReplicaState(
  constants:ReplicaConstantsState,
  nextHeartbeatTime:uint64,
  proposer:ProposerState,
  acceptor:AcceptorState,
  learner:CLearnerState,
  executor:ExecutorState
  )

predicate ReplicaStateIsAbstractable(replica:ReplicaState)
{
  && ReplicaConstantsStateIsAbstractable(replica.constants)
  && ProposerIsAbstractable(replica.proposer)
  && AcceptorIsAbstractable(replica.acceptor)
  && LearnerState_IsAbstractable(replica.learner)
  && ExecutorState_IsAbstractable(replica.executor)
}

function AbstractifyReplicaStateToLReplica(replica:ReplicaState) : LReplica
  requires ReplicaStateIsAbstractable(replica)
{
  LReplica(
    AbstractifyReplicaConstantsStateToLReplicaConstants(replica.constants),
    replica.nextHeartbeatTime as int,
    AbstractifyProposerStateToLProposer(replica.proposer),
    AbstractifyAcceptorStateToAcceptor(replica.acceptor),
    AbstractifyLearnerStateToLLearner(replica.learner),
    AbstractifyExecutorStateToLExecutor(replica.executor))
}

//////////////////////////////////////////////////////////////////////////////

predicate ReplicaCommonPreconditions(replica:ReplicaState)
{
  ReplicaStateIsValid(replica)
}

predicate ReplicaReceivePreconditions(replica:ReplicaState, cpacket:CPacket)
{
  && ReplicaCommonPreconditions(replica)
  && CPacketIsSendable(cpacket)
  && PaxosEndPointIsValid(cpacket.src, replica.constants.all.config)
}

predicate ReplicaCommonPostconditions(replica:ReplicaState, replica':ReplicaState, sent_packets:OutboundPackets)
{
  && ReplicaCommonPreconditions(replica)
  && ReplicaStateIsAbstractable(replica')
  && OutboundPacketsIsValid(sent_packets)
  && OutboundPacketsIsAbstractable(sent_packets)
  && ReplicaStateIsValid(replica')
  && OutboundPacketsHasCorrectSrc(sent_packets, replica.constants.all.config.replica_ids[replica.constants.my_index])
  && replica'.constants == replica.constants
}

//
//////////////////////////////////////////////////////////////////////////////

predicate ReplicaStateIsValid(replica:ReplicaState)
{
  && ProposerIsValid(replica.proposer)
  && AcceptorIsValid(replica.acceptor)
  && LearnerState_IsValid(replica.learner)
  && ExecutorState_IsValid(replica.executor)
  && ReplicaStateIsAbstractable(replica)
  && ReplicaConstantsState_IsValid(replica.constants)
  && replica.constants == replica.proposer.constants
  && replica.constants == replica.acceptor.constants
  && replica.constants == replica.learner.rcs
  && replica.constants == replica.executor.constants
}

predicate ConstantsStayConstant_Replica(replica:ReplicaState, replica':ReplicaState)
{
  && replica.constants == replica'.constants
  && replica.proposer.constants == replica'.proposer.constants
  && replica.acceptor.constants == replica'.acceptor.constants
  && replica.learner.rcs        == replica'.learner.rcs
  && replica.executor.constants == replica'.executor.constants
}

predicate Replica_Common_Preconditions(replica:ReplicaState, inp:CPacket)
{
  && ReplicaStateIsValid(replica)
  && CPacketIsSendable(inp)
  && PaxosEndPointIsValid(inp.src, replica.constants.all.config)
}

predicate Replica_Common_Postconditions(replica:ReplicaState, replica':ReplicaState, inp:CPacket, packets_sent:OutboundPackets)
  requires Replica_Common_Preconditions(replica, inp)
{
  && ReplicaStateIsAbstractable(replica')
  && ConstantsStayConstant_Replica(replica, replica')
  && ReplicaStateIsValid(replica')
  && OutboundPacketsIsValid(packets_sent)
  && OutboundPacketsHasCorrectSrc(packets_sent, replica.constants.all.config.replica_ids[replica.constants.my_index])
  && OutboundPacketsIsAbstractable(packets_sent)
  && replica'.constants == replica.constants
}

predicate Replica_Common_Postconditions_NoPacket(replica:ReplicaState, replica':ReplicaState, packets_sent:OutboundPackets)
{
  && ReplicaStateIsValid(replica)
  && ReplicaStateIsAbstractable(replica')
  && ConstantsStayConstant_Replica(replica, replica')
  && ReplicaStateIsValid(replica')
  && OutboundPacketsIsValid(packets_sent)
  && OutboundPacketsHasCorrectSrc(packets_sent, replica.constants.all.config.replica_ids[replica.constants.my_index])
  && OutboundPacketsIsAbstractable(packets_sent)
  && replica'.constants == replica.constants
}

predicate Replica_Next_Process_Request_Preconditions(replica:ReplicaState, inp:CPacket)
{
  && Replica_Common_Preconditions(replica, inp)
  && ProposerIsValid(replica.proposer)
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_Request?
}

predicate Replica_Next_Process_Request_Postconditions(replica:ReplicaState, replica':ReplicaState, inp:CPacket, packets_sent:OutboundPackets)
  requires Replica_Next_Process_Request_Preconditions(replica, inp)
{
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcessRequest(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Process_1a_Preconditions(replica:ReplicaState, inp:CPacket)
{
  && Replica_Common_Preconditions(replica, inp)
  && NextAcceptorState_Phase1Preconditions(replica.acceptor, inp.msg, inp.src)
}

predicate Replica_Next_Process_1a_Postconditions(replica:ReplicaState, replica':ReplicaState, inp:CPacket, packets_sent:OutboundPackets)
  requires Replica_Next_Process_1a_Preconditions(replica, inp)
{
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcess1a(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Process_1b_Preconditions(replica:ReplicaState, inp:CPacket)
{
  && Replica_Common_Preconditions(replica, inp)
  && ProposerIsValid(replica.proposer)
  && CPacketIsAbstractable(inp)
//  && replica.proposer.current_state == 1
//  && ConvertUint64ToEndPoint(inp.src) in replica.proposer.constants.all.config.replica_ids
  && inp.msg.CMessage_1b?
//  && inp.msg.bal_1b == replica.proposer.max_ballot_i_sent_1a
}

predicate Replica_Next_Process_1b_Postconditions(replica:ReplicaState, replica':ReplicaState, inp:CPacket, packets_sent:OutboundPackets)
  requires Replica_Next_Process_1b_Preconditions(replica, inp)
{
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcess1b(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Process_StartingPhase2_Preconditions(replica:ReplicaState, inp:CPacket)
{
  && Replica_Common_Preconditions(replica, inp)
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_StartingPhase2?
}

predicate Replica_Next_Process_StartingPhase2_Postconditions(replica:ReplicaState, replica':ReplicaState, inp:CPacket, packets_sent:OutboundPackets)
  requires Replica_Next_Process_StartingPhase2_Preconditions(replica, inp)
{
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcessStartingPhase2(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Process_2a_Preconditions(replica:ReplicaState, inp:CPacket)
{
  && Replica_Common_Preconditions(replica, inp)
  && NextAcceptorState_Phase2Preconditions_AlwaysEnabled(replica.acceptor, inp.msg, inp.src)
}

predicate Replica_Next_Process_2a_Postconditions(replica:ReplicaState, replica':ReplicaState, inp:CPacket, packets_sent:OutboundPackets)
  requires Replica_Next_Process_2a_Preconditions(replica, inp)
{
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcess2a(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Process_2b_Preconditions(replica:ReplicaState, inp:CPacket)
{
  && Replica_Common_Preconditions(replica, inp)
  && LearnerState_Process2b__Preconditions(replica.learner, replica.executor, inp)
}

predicate Replica_Next_Process_2b_Postconditions(replica:ReplicaState, replica':ReplicaState, inp:CPacket, packets_sent:OutboundPackets)
  requires Replica_Next_Process_2b_Preconditions(replica, inp)
{
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcess2b(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(replica:ReplicaState)
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions(replica:ReplicaState, replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(replica)
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_MaybeEnterPhase2_Preconditions(replica:ReplicaState)
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_MaybeEnterPhase2_Postconditions(replica:ReplicaState, replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_MaybeEnterPhase2_Preconditions(replica)
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextSpontaneousMaybeEnterPhase2(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Preconditions(replica:ReplicaState)
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Postconditions(replica:ReplicaState, replica':ReplicaState, clock:CClockReading, packets_sent:OutboundPackets)
  requires Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Preconditions(replica)
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextReadClockMaybeNominateValueAndSend2a(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCClockReadingToClockReading(clock),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Process_AppStateRequest_Preconditions(replica:ReplicaState, inp:CPacket)
{
  && Replica_Common_Preconditions(replica, inp)
  && AppStateMarshallable(replica.executor.app)
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_AppStateRequest?
}

predicate Replica_Next_Process_AppStateRequest_Postconditions(replica:ReplicaState, replica':ReplicaState, inp:CPacket, packets_sent:OutboundPackets)
  requires Replica_Next_Process_AppStateRequest_Preconditions(replica, inp)
{
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcessAppStateRequest(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Process_Heartbeat_Preconditions(replica:ReplicaState, inp:CPacket)
{
  && Replica_Common_Preconditions(replica, inp)
  && NextAcceptorState_ProcessHeartbeatPreconditions(replica.acceptor, inp.msg, inp.src)
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_Heartbeat?
}

predicate Replica_Next_Process_Heartbeat_Postconditions(replica:ReplicaState, replica':ReplicaState, inp:CPacket, clock:uint64, packets_sent:OutboundPackets)
  requires Replica_Next_Process_Heartbeat_Preconditions(replica, inp)
{
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcessHeartbeat(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      clock as int,
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_ReadClock_CheckForViewTimeout_Preconditions(replica:ReplicaState)
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_ReadClock_CheckForViewTimeout_Postconditions(replica:ReplicaState, replica':ReplicaState, clock:CClockReading, packets_sent:OutboundPackets)
  requires Replica_Next_ReadClock_CheckForViewTimeout_Preconditions(replica)
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextReadClockCheckForViewTimeout(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCClockReadingToClockReading(clock),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Preconditions(replica:ReplicaState)
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Postconditions(replica:ReplicaState, replica':ReplicaState, clock:CClockReading, packets_sent:OutboundPackets)
  requires Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Preconditions(replica)
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCClockReadingToClockReading(clock),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Process_AppStateSupply_Preconditions(replica:ReplicaState, inp:CPacket)
{
  && Replica_Common_Preconditions(replica, inp)
  && inp.msg.CMessage_AppStateSupply?
  && LearnerState_ForgetOperationsBefore__Preconditions(replica.learner, inp.msg.opn_state_supply)
}

predicate Replica_Next_Process_AppStateSupply_Postconditions(replica:ReplicaState, replica':ReplicaState, inp:CPacket, packets_sent:OutboundPackets)
  requires Replica_Next_Process_AppStateSupply_Preconditions(replica, inp)
{
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcessAppStateSupply(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica:ReplicaState)
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_Spontaneous_MaybeExecute_Postconditions(replica:ReplicaState, replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica)
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextSpontaneousMaybeExecute(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica:ReplicaState)
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions(replica:ReplicaState, replica':ReplicaState, clock:CClockReading, packets_sent:OutboundPackets)
  requires Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica)
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextReadClockMaybeSendHeartbeat(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCClockReadingToClockReading(clock),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica:ReplicaState)
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(replica:ReplicaState, replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica)
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextSpontaneousMaybeMakeDecision(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica:ReplicaState)
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions(replica:ReplicaState, replica':ReplicaState, packets_sent:OutboundPackets)
  requires Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica)
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(
      AbstractifyReplicaStateToLReplica(replica),
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

} 
