include "../../Protocol/RSL/Executor.i.dfy"
include "PacketParsing.i.dfy"
include "ReplicaConstantsState.i.dfy"

module LiveRSL__ExecutorState_i {
import opened Native__NativeTypes_s
import opened LiveRSL__CTypes_i
import opened LiveRSL__Executor_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__ReplicaConstantsState_i
import opened AppStateMachine_s

///////////////////////////
// COutstandingOperation
///////////////////////////

datatype COutstandingOperation = COutstandingOpKnown(v:CRequestBatch,bal:CBallot) | COutstandingOpUnknown()

predicate COutstandingOperationIsAbstractable(op:COutstandingOperation)
{
  || op.COutstandingOpUnknown?
  || (CRequestBatchIsAbstractable(op.v) && CBallotIsAbstractable(op.bal))
}

function AbstractifyCOutstandingOperationToOutstandingOperation(op:COutstandingOperation):OutstandingOperation
  requires COutstandingOperationIsAbstractable(op)
{
  match op
    case COutstandingOpKnown(v,bal) => OutstandingOpKnown(AbstractifyCRequestBatchToRequestBatch(v),AbstractifyCBallotToBallot(bal))
    case COutstandingOpUnknown => OutstandingOpUnknown()
}

///////////////////////////
// ExecutorState
///////////////////////////

datatype ExecutorState = ExecutorState(
  constants:ReplicaConstantsState,
  app:AppStateMachine,
  ops_complete:COperationNumber,
  max_bal_reflected:CBallot,
  next_op_to_execute:COutstandingOperation,
  ghost reply_cache:CReplyCache)

predicate ExecutorState_IsAbstractable(executor:ExecutorState)
{
  && ReplicaConstantsStateIsAbstractable(executor.constants)
  && COperationNumberIsAbstractable(executor.ops_complete)
  && CBallotIsAbstractable(executor.max_bal_reflected)
  && COutstandingOperationIsAbstractable(executor.next_op_to_execute)
  && CReplyCacheIsAbstractable(executor.reply_cache)
}

function AbstractifyExecutorStateToLExecutor(executor:ExecutorState) : LExecutor
  reads executor.app
  requires ExecutorState_IsAbstractable(executor)
{
  LExecutor(
    AbstractifyReplicaConstantsStateToLReplicaConstants(executor.constants),
    executor.app.Abstractify(),
    AbstractifyCOperationNumberToOperationNumber(executor.ops_complete),
    AbstractifyCBallotToBallot(executor.max_bal_reflected),
    AbstractifyCOutstandingOperationToOutstandingOperation(executor.next_op_to_execute),
    AbstractifyCReplyCacheToReplyCache(executor.reply_cache))
}

predicate ExecutorState_IsValid(executor:ExecutorState)
{
  && ExecutorState_IsAbstractable(executor)
  && ReplicaConstantsState_IsValid(executor.constants)
  && ValidReplyCache(executor.reply_cache)
  && (executor.next_op_to_execute.COutstandingOpKnown? ==> ValidRequestBatch(executor.next_op_to_execute.v))
}

predicate ExecutorState_CommonPreconditions(executor:ExecutorState)
{
  && ExecutorState_IsValid(executor)
  && ExecutorState_IsAbstractable(executor)    // Can I have this too?
}

} 
