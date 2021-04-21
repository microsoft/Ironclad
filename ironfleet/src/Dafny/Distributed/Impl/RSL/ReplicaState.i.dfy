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

function AbstractifyReplicaStateToLReplica(replica:ReplicaState) : (lreplica:LReplica)
  reads replica.executor.app
  requires ReplicaStateIsAbstractable(replica)
  ensures  lreplica.constants == AbstractifyReplicaConstantsStateToLReplicaConstants(replica.constants)
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
  reads replica.executor.app
{
  ReplicaStateIsValid(replica)
}

predicate ReplicaReceivePreconditions(replica:ReplicaState, cpacket:CPacket)
  reads replica.executor.app
{
  && ReplicaCommonPreconditions(replica)
  && CPacketIsSendable(cpacket)
  && PaxosEndPointIsValid(cpacket.src, replica.constants.all.config)
}

predicate ReplicaCommonPostconditions(replica:LReplica, replica':ReplicaState, sent_packets:OutboundPackets)
  reads replica'.executor.app
{
  && ReplicaConstantsState_IsValid(replica'.constants)
  && AbstractifyReplicaConstantsStateToLReplicaConstants(replica'.constants) == replica.constants
  && ReplicaStateIsAbstractable(replica')
  && OutboundPacketsIsValid(sent_packets)
  && OutboundPacketsIsAbstractable(sent_packets)
  && ReplicaStateIsValid(replica')
  && OutboundPacketsHasCorrectSrc(sent_packets, replica'.constants.all.config.replica_ids[replica'.constants.my_index])
}

//
//////////////////////////////////////////////////////////////////////////////

predicate ReplicaStateIsValid(replica:ReplicaState)
  reads replica.executor.app
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

predicate ConstantsStayConstant_Replica(replica:LReplica, replica':ReplicaState)
  requires ReplicaConstantsStateIsAbstractable(replica'.constants)
{
  && AbstractifyReplicaConstantsStateToLReplicaConstants(replica'.constants) == replica.constants
  && replica.constants == replica.proposer.constants
  && replica.constants == replica.acceptor.constants
  && replica.constants == replica.learner.constants
  && replica.constants == replica.executor.constants
  && replica'.constants == replica'.proposer.constants
  && replica'.constants == replica'.acceptor.constants
  && replica'.constants == replica'.learner.rcs
  && replica'.constants == replica'.executor.constants
}

predicate Replica_Common_Preconditions(replica:ReplicaState, inp:CPacket)
  reads replica.executor.app
{
  && ReplicaStateIsValid(replica)
  && CPacketIsSendable(inp)
  && PaxosEndPointIsValid(inp.src, replica.constants.all.config)
}

predicate Replica_Common_Postconditions(replica:LReplica, replica':ReplicaState, inp:CPacket, packets_sent:OutboundPackets)
  reads replica'.executor.app
{
  && ReplicaConstantsState_IsValid(replica'.constants)
  && CPacketIsSendable(inp)
  && PaxosEndPointIsValid(inp.src, replica'.constants.all.config)
  && ReplicaStateIsAbstractable(replica')
  && ConstantsStayConstant_Replica(replica, replica')
  && ReplicaStateIsValid(replica')
  && OutboundPacketsIsValid(packets_sent)
  && OutboundPacketsHasCorrectSrc(packets_sent, replica'.constants.all.config.replica_ids[replica'.constants.my_index])
  && OutboundPacketsIsAbstractable(packets_sent)
}

predicate Replica_Common_Postconditions_NoPacket(replica:LReplica, replica':ReplicaState, packets_sent:OutboundPackets)
  reads replica'.executor.app
{
  && ReplicaConstantsState_IsValid(replica'.constants)
  && ReplicaStateIsAbstractable(replica')
  && ConstantsStayConstant_Replica(replica, replica')
  && ReplicaStateIsValid(replica')
  && OutboundPacketsIsValid(packets_sent)
  && OutboundPacketsHasCorrectSrc(packets_sent, replica'.constants.all.config.replica_ids[replica'.constants.my_index])
  && OutboundPacketsIsAbstractable(packets_sent)
}

predicate Replica_Next_Process_Request_Preconditions(replica:ReplicaState, inp:CPacket)
  reads replica.executor.app
{
  && Replica_Common_Preconditions(replica, inp)
  && ProposerIsValid(replica.proposer)
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_Request?
}

predicate Replica_Next_Process_Request_Postconditions(replica:LReplica, replica':ReplicaState, inp:CPacket,
                                                      packets_sent:OutboundPackets)
  reads replica'.executor.app
{
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_Request?
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcessRequest(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Process_1a_Preconditions(replica:ReplicaState, inp:CPacket)
  reads replica.executor.app
{
  && Replica_Common_Preconditions(replica, inp)
  && NextAcceptorState_Phase1Preconditions(replica.acceptor, inp.msg, inp.src)
}

predicate Replica_Next_Process_1a_Postconditions(replica:LReplica, replica':ReplicaState, inp:CPacket,
                                                 packets_sent:OutboundPackets)
  reads replica'.executor.app
{
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_1a?
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcess1a(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Process_1b_Preconditions(replica:ReplicaState, inp:CPacket)
  reads replica.executor.app
{
  && Replica_Common_Preconditions(replica, inp)
  && ProposerIsValid(replica.proposer)
  && CPacketIsAbstractable(inp)
//  && replica.proposer.current_state == 1
//  && ConvertUint64ToEndPoint(inp.src) in replica.proposer.constants.all.config.replica_ids
  && inp.msg.CMessage_1b?
//  && inp.msg.bal_1b == replica.proposer.max_ballot_i_sent_1a
}

predicate Replica_Next_Process_1b_Postconditions(replica:LReplica, replica':ReplicaState, inp:CPacket,
                                                 packets_sent:OutboundPackets)
  reads replica'.executor.app
{
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_1b?
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcess1b(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Process_StartingPhase2_Preconditions(replica:ReplicaState, inp:CPacket)
  reads replica.executor.app
{
  && Replica_Common_Preconditions(replica, inp)
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_StartingPhase2?
}

predicate Replica_Next_Process_StartingPhase2_Postconditions(replica:LReplica, replica':ReplicaState, inp:CPacket,
                                                             packets_sent:OutboundPackets)
  reads replica'.executor.app
{
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_StartingPhase2?
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcessStartingPhase2(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Process_2a_Preconditions(replica:ReplicaState, inp:CPacket)
  reads replica.executor.app
{
  && Replica_Common_Preconditions(replica, inp)
  && NextAcceptorState_Phase2Preconditions_AlwaysEnabled(replica.acceptor, inp.msg, inp.src)
}

predicate Replica_Next_Process_2a_Postconditions(replica:LReplica, replica':ReplicaState, inp:CPacket,
                                                 packets_sent:OutboundPackets)
  reads replica'.executor.app
{
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_2a?
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcess2a(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Process_2b_Preconditions(replica:ReplicaState, inp:CPacket)
  reads replica.executor.app
{
  && Replica_Common_Preconditions(replica, inp)
  && LearnerState_Process2b__Preconditions(replica.learner, replica.executor, inp)
}

predicate Replica_Next_Process_2b_Postconditions(replica:LReplica, replica':ReplicaState, inp:CPacket,
                                                 packets_sent:OutboundPackets)
  reads replica'.executor.app
{
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_2b?
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcess2b(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(replica:ReplicaState)
  reads replica.executor.app
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions(replica:LReplica, replica':ReplicaState, packets_sent:OutboundPackets)
  reads replica'.executor.app
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_MaybeEnterPhase2_Preconditions(replica:ReplicaState)
  reads replica.executor.app
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_MaybeEnterPhase2_Postconditions(replica:LReplica, replica':ReplicaState, packets_sent:OutboundPackets)
  reads replica'.executor.app
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextSpontaneousMaybeEnterPhase2(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Preconditions(replica:ReplicaState)
  reads replica.executor.app
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Postconditions(
  replica:LReplica,
  replica':ReplicaState,
  clock:CClockReading,
  packets_sent:OutboundPackets
  )
  reads replica'.executor.app
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextReadClockMaybeNominateValueAndSend2a(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCClockReadingToClockReading(clock),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Process_AppStateRequest_Preconditions(replica:ReplicaState, inp:CPacket)
  reads replica.executor.app
{
  && Replica_Common_Preconditions(replica, inp)
  && AppStateMarshallable(replica.executor.app)
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_AppStateRequest?
}

predicate Replica_Next_Process_AppStateRequest_Postconditions(replica:LReplica, replica':ReplicaState,
                                                              inp:CPacket, packets_sent:OutboundPackets)
  reads replica'.executor.app
{
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_AppStateRequest?
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcessAppStateRequest(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Process_Heartbeat_Preconditions(replica:ReplicaState, inp:CPacket)
  reads replica.executor.app
{
  && Replica_Common_Preconditions(replica, inp)
  && NextAcceptorState_ProcessHeartbeatPreconditions(replica.acceptor, inp.msg, inp.src)
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_Heartbeat?
}

predicate Replica_Next_Process_Heartbeat_Postconditions(replica:LReplica, replica':ReplicaState,
                                                        inp:CPacket, clock:uint64, packets_sent:OutboundPackets)
  reads replica'.executor.app
{
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_Heartbeat?
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcessHeartbeat(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      clock as int,
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_ReadClock_CheckForViewTimeout_Preconditions(replica:ReplicaState)
  reads replica.executor.app
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_ReadClock_CheckForViewTimeout_Postconditions(
  replica:LReplica,
  replica':ReplicaState,
  clock:CClockReading,
  packets_sent:OutboundPackets
  )
  reads replica'.executor.app
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextReadClockCheckForViewTimeout(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCClockReadingToClockReading(clock),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Preconditions(replica:ReplicaState)
  reads replica.executor.app
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Postconditions(
  replica:LReplica,
  replica':ReplicaState,
  clock:CClockReading,
  packets_sent:OutboundPackets
  )
  reads replica'.executor.app
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCClockReadingToClockReading(clock),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Process_AppStateSupply_Preconditions(replica:ReplicaState, inp:CPacket)
  reads replica.executor.app
{
  && Replica_Common_Preconditions(replica, inp)
  && inp.msg.CMessage_AppStateSupply?
  && LearnerState_ForgetOperationsBefore__Preconditions(replica.learner, inp.msg.opn_state_supply)
}

predicate Replica_Next_Process_AppStateSupply_Postconditions(replica:LReplica, replica':ReplicaState,
                                                             inp:CPacket, packets_sent:OutboundPackets)
  reads replica'.executor.app
{
  && CPacketIsAbstractable(inp)
  && inp.msg.CMessage_AppStateSupply?
  && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
  && LReplicaNextProcessAppStateSupply(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCPacketToRslPacket(inp),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica:ReplicaState)
  reads replica.executor.app
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_Spontaneous_MaybeExecute_Postconditions(replica:LReplica, replica':ReplicaState,
                                                               packets_sent:OutboundPackets)
  reads replica'.executor.app
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextSpontaneousMaybeExecute(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica:ReplicaState)
  reads replica.executor.app
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions(
  replica:LReplica,
  replica':ReplicaState,
  clock:CClockReading,
  packets_sent:OutboundPackets
  )
  reads replica'.executor.app
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextReadClockMaybeSendHeartbeat(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyCClockReadingToClockReading(clock),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica:ReplicaState)
  reads replica.executor.app
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(
  replica:LReplica,
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  reads replica'.executor.app
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextSpontaneousMaybeMakeDecision(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

predicate Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica:ReplicaState)
  reads replica.executor.app
{
  ReplicaStateIsValid(replica)
}

predicate Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions(
  replica:LReplica,
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  reads replica'.executor.app
{
  && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
  && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(
      replica,
      AbstractifyReplicaStateToLReplica(replica'),
      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
}

} 
