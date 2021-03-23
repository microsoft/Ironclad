include "../../Protocol/RSL/Acceptor.i.dfy"
include "PacketParsing.i.dfy"
include "ReplicaConstantsState.i.dfy"
include "CLastCheckpointedMap.i.dfy"

module LiveRSL__AcceptorState_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__Acceptor_i
import opened LiveRSL__Broadcast_i
import opened LiveRSL__CLastCheckpointedMap_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__ReplicaConstantsState_i
import opened Common__UpperBound_s

datatype AcceptorState = AcceptorState(
  constants:ReplicaConstantsState,
  maxBallot:CBallot,
  votes:CVotes,
  last_checkpointed_operation:CLastCheckpointedMap,
  log_truncation_point:COperationNumber,
  minVotedOpn:COperationNumber
  )

predicate AcceptorIsAbstractable(acceptor:AcceptorState)
{
  && ReplicaConstantsStateIsAbstractable(acceptor.constants)
  && CBallotIsAbstractable(acceptor.maxBallot)
  && CVotesIsAbstractable(acceptor.votes)
  && CLastCheckpointedMapIsAbstractable(acceptor.last_checkpointed_operation)
  && COperationNumberIsAbstractable(acceptor.log_truncation_point)
  && ReplicaConstantsStateIsAbstractable(acceptor.constants)
}

function AbstractifyAcceptorStateToAcceptor(acceptor:AcceptorState) : LAcceptor
    requires AcceptorIsAbstractable(acceptor);
{
  LAcceptor(
//    AbstractifyEndPointToNodeIdentity(acceptor.constants.me),
    AbstractifyReplicaConstantsStateToLReplicaConstants(acceptor.constants),
    AbstractifyCBallotToBallot(acceptor.maxBallot),
    AbstractifyCVotesToVotes(acceptor.votes),
    AbstractifyCLastCheckpointedMapToOperationNumberSequence(acceptor.last_checkpointed_operation),
    AbstractifyCOperationNumberToOperationNumber(acceptor.log_truncation_point))
}

predicate VotedMinimum(acceptor:AcceptorState)
{
  forall v :: v in acceptor.votes.v ==> v.n >= acceptor.minVotedOpn.n
}

predicate AcceptorIsValid(acceptor:AcceptorState)
{
  && ReplicaConstantsState_IsValid(acceptor.constants)
  && acceptor.constants.all.config.replica_ids == acceptor.constants.all.config.replica_ids
  && ValidVotes(acceptor.votes)
  && acceptor.constants.all.params.max_integer_val > acceptor.constants.all.params.max_log_length > 0
  && (forall opn :: opn in acceptor.votes.v ==>
               AbstractifyCOperationNumberToOperationNumber(acceptor.log_truncation_point)
               <= AbstractifyCOperationNumberToOperationNumber(opn)
               <= UpperBoundedAddition(AbstractifyCOperationNumberToOperationNumber(acceptor.log_truncation_point),
                                      (acceptor.constants.all.params.max_log_length-1) as int,
                                      UpperBoundFinite(acceptor.constants.all.params.max_integer_val as int)))
  && AcceptorIsAbstractable(acceptor)
  && LMinQuorumSize(AbstractifyAcceptorStateToAcceptor(acceptor).constants.all.config) <= |acceptor.last_checkpointed_operation|
  && VotedMinimum(acceptor)
  && |acceptor.last_checkpointed_operation| == |acceptor.constants.all.config.replica_ids|
}

predicate NextAcceptorState_InitPostconditions(acceptor:AcceptorState, rcs:ReplicaConstantsState)
  requires ReplicaConstantsState_IsValid(rcs)
{
  && AcceptorIsValid(acceptor)
  && AcceptorIsAbstractable(acceptor)
  && acceptor.constants == rcs
  && LAcceptorInit(AbstractifyAcceptorStateToAcceptor(acceptor), AbstractifyReplicaConstantsStateToLReplicaConstants(rcs))
}

predicate ConstantsStayConstant(acceptor:AcceptorState, acceptor':AcceptorState)
//  requires AcceptorIsAbstractable(acceptor)
//  requires AcceptorIsAbstractable(acceptor')
//  requires ReplicaConstantsStateIsAbstractable(acceptor.constants)
//  requires ReplicaConstantsStateIsAbstractable(acceptor'.constants)
{
//  AbstractifyAcceptorStateToAcceptor(acceptor).constants == AbstractifyAcceptorStateToAcceptor(acceptor').constants
  acceptor.constants == acceptor'.constants
}

predicate CommonAcceptorPreconditions(acceptor:AcceptorState, in_msg:CMessage, sender:EndPoint)
{
  && AcceptorIsValid(acceptor)
  && AcceptorIsAbstractable(acceptor)
  && ReplicaConstantsState_IsValid(acceptor.constants)
  && CMessageIsValid(in_msg)
  && CMessageIsAbstractable(in_msg)
  && PaxosEndPointIsValid(sender, acceptor.constants.all.config)
}

predicate CommonAcceptorPostconditions(acceptor:AcceptorState, acceptor':AcceptorState, packets_sent:CBroadcast)
  requires AcceptorIsValid(acceptor)
  requires AcceptorIsAbstractable(acceptor)
{
  && AcceptorIsValid(acceptor')
  && AcceptorIsAbstractable(acceptor')
  && ConstantsStayConstant(acceptor, acceptor')
  && CBroadcastIsValid(packets_sent)
  && (packets_sent.CBroadcast? ==> packets_sent.src == acceptor.constants.all.config.replica_ids[acceptor.constants.my_index])
}

predicate NextAcceptorState_Phase1Preconditions(acceptor:AcceptorState, in_msg:CMessage, sender:EndPoint)
{
  && CommonAcceptorPreconditions(acceptor, in_msg, sender)
  && in_msg.CMessage_1a?
}

predicate NextAcceptorState_Phase1Postconditions(acceptor:AcceptorState, acceptor':AcceptorState, in_msg:CMessage, sender:EndPoint, packets_sent:CBroadcast)
{
  && NextAcceptorState_Phase1Preconditions(acceptor, in_msg, sender)
  && CommonAcceptorPostconditions(acceptor, acceptor', packets_sent)
  && LAcceptorProcess1a(
      AbstractifyAcceptorStateToAcceptor(acceptor),
      AbstractifyAcceptorStateToAcceptor(acceptor'),
      AbstractifyCMessageToRslPacket(acceptor.constants.all.config.replica_ids[acceptor.constants.my_index], sender, in_msg),
      AbstractifyCBroadcastToRlsPacketSeq(packets_sent))
}

predicate NextAcceptorState_Phase2Preconditions_AlwaysEnabled(acceptor:AcceptorState, in_msg:CMessage, sender:EndPoint)
{
  && CommonAcceptorPreconditions(acceptor, in_msg, sender)
  && in_msg.CMessage_2a?
  && CPaxosConfigurationIsAbstractable(acceptor.constants.all.config)
}

predicate NextAcceptorState_Phase2Preconditions(acceptor:AcceptorState, in_msg:CMessage, sender:EndPoint)
{
  && NextAcceptorState_Phase2Preconditions_AlwaysEnabled(acceptor, in_msg, sender)
  && CBallotIsNotGreaterThan(acceptor.maxBallot, in_msg.bal_2a)
  //&& AbstractifyCOperationNumberToOperationNumber(acceptor.log_truncation_point) <= 
  && AbstractifyCOperationNumberToOperationNumber(in_msg.opn_2a) <= acceptor.constants.all.params.max_integer_val as int
  && sender in acceptor.constants.all.config.replica_ids
}

predicate NextAcceptorState_Phase2Postconditions(acceptor:AcceptorState, acceptor':AcceptorState, in_msg:CMessage, sender:EndPoint, packets_sent:CBroadcast)
{
  && NextAcceptorState_Phase2Preconditions(acceptor, in_msg, sender)
  && CommonAcceptorPostconditions(acceptor, acceptor', packets_sent)
  && LAcceptorProcess2a(
      AbstractifyAcceptorStateToAcceptor(acceptor),
      AbstractifyAcceptorStateToAcceptor(acceptor'),
      AbstractifyCMessageToRslPacket(acceptor.constants.all.config.replica_ids[acceptor.constants.my_index], sender, in_msg),
      AbstractifyCBroadcastToRlsPacketSeq(packets_sent))
}

predicate NextAcceptorState_ProcessHeartbeatPreconditions(acceptor:AcceptorState, in_msg:CMessage, sender:EndPoint)
{
  && CommonAcceptorPreconditions(acceptor, in_msg, sender)
  && in_msg.CMessage_Heartbeat?
  && CPaxosConfigurationIsAbstractable(acceptor.constants.all.config)
}

predicate NextAcceptorState_ProcessHeartbeatPostconditions(acceptor:AcceptorState, acceptor':AcceptorState, in_msg:CMessage, sender:EndPoint)
{
  && NextAcceptorState_ProcessHeartbeatPreconditions(acceptor, in_msg, sender)
  && AcceptorIsValid(acceptor')
  && AcceptorIsAbstractable(acceptor')
  && ConstantsStayConstant(acceptor, acceptor')
  && LAcceptorProcessHeartbeat(
      AbstractifyAcceptorStateToAcceptor(acceptor),
      AbstractifyAcceptorStateToAcceptor(acceptor'),
      AbstractifyCMessageToRslPacket(acceptor.constants.all.config.replica_ids[acceptor.constants.my_index], sender, in_msg))
}

predicate NextAcceptorState_TruncateLogPreconditions(acceptor:AcceptorState, opn:COperationNumber)
{
  && AcceptorIsValid(acceptor)
  && AcceptorIsAbstractable(acceptor)
  //&& opn.n > acceptor.log_truncation_point.n
}

predicate NextAcceptorState_TruncateLogPostconditions(acceptor:AcceptorState, acceptor':AcceptorState, opn:COperationNumber)
{
  && NextAcceptorState_TruncateLogPreconditions(acceptor, opn)
  && AcceptorIsValid(acceptor')
  && AcceptorIsAbstractable(acceptor')
  && ConstantsStayConstant(acceptor, acceptor')
  && LAcceptorTruncateLog(
      AbstractifyAcceptorStateToAcceptor(acceptor),
      AbstractifyAcceptorStateToAcceptor(acceptor'),
      AbstractifyCOperationNumberToOperationNumber(opn))
}

} 
