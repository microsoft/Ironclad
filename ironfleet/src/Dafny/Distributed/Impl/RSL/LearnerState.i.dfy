include "../../Protocol/RSL/Learner.i.dfy"
include "ReplicaConstantsState.i.dfy"
include "ExecutorState.i.dfy"

module LiveRSL__LearnerState_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__AppInterface_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__ExecutorState_i
import opened LiveRSL__Learner_i
import opened LiveRSL__ReplicaConstantsState_i
import opened LiveRSL__Types_i
import opened Common__NodeIdentity_i
import opened Common__SeqIsUniqueDef_i
import opened Collections__Sets_i
import opened Collections__Maps_i
import opened GenericRefinement_i

datatype CLearnerTuple =
  CLearnerTuple(
    received_2b_message_senders:seq<EndPoint>,
    candidate_learned_value:seq<CRequest>)

datatype CLearnerState =
  CLearnerState(
    rcs:ReplicaConstantsState,
    max_ballot_seen:CBallot,
    unexecuted_ops:map<COperationNumber, CLearnerTuple>,
    sendDecision:bool,
    opn:COperationNumber,
    recv2b:bool,
    recvCp:CPacket)

predicate CLearnerTupleIsValid(tuple:CLearnerTuple) 
{
  && SeqIsUnique(tuple.received_2b_message_senders)
  && |tuple.candidate_learned_value| <= RequestBatchSizeLimit()
}

predicate LearnerState_IsValid(learner:CLearnerState)
{
  && LearnerState_IsAbstractable(learner)
  && (forall o :: o in learner.unexecuted_ops ==> CLearnerTupleIsValid(learner.unexecuted_ops[o]))
  && ReplicaConstantsState_IsValid(learner.rcs)
  && ReplicaConstantsStateIsAbstractable(learner.rcs)
}

predicate LearnerTupleIsAbstractable(tuple:CLearnerTuple)
{
  && SeqOfEndPointsIsAbstractable(tuple.received_2b_message_senders)
  && CRequestBatchIsAbstractable(tuple.candidate_learned_value)
}

function AbstractifyCLearnerTupleToLearnerTuple(tuple:CLearnerTuple) : LearnerTuple
  ensures LearnerTupleIsAbstractable(tuple) ==> AbstractifyCLearnerTupleToLearnerTuple(tuple) == LearnerTuple(MapSeqToSet(AbstractifyEndPointsToNodeIdentities(tuple.received_2b_message_senders), x=>x), AbstractifyCRequestBatchToRequestBatch(tuple.candidate_learned_value))
{
  if (LearnerTupleIsAbstractable(tuple)) then 
    var pkts := AbstractifyEndPointsToNodeIdentities(tuple.received_2b_message_senders);
    var value := AbstractifyCRequestBatchToRequestBatch(tuple.candidate_learned_value);
    LearnerTuple(MapSeqToSet(pkts, x=>x), value)
  else 
    var lt:LearnerTuple :| (true); lt
}

predicate CLearnerTuplesAreAbstractable(tuples:map<COperationNumber,CLearnerTuple>)
{
  && (forall opn :: opn in tuples ==> COperationNumberIsAbstractable(opn))
  && (forall opn :: opn in tuples ==> LearnerTupleIsAbstractable(tuples[opn]))
}

function RefineOperationNumberToCOperationNumber(o:OperationNumber) : COperationNumber 
  // requires 0 <= o < 0x1_0000_0000_0000_0000
  ensures (0 <= o < 0x1_0000_0000_0000_0000) ==> RefineOperationNumberToCOperationNumber(o) == COperationNumber(o as uint64)
{
  if (0 <= o  && o < 0x1_0000_0000_0000_0000) then
    COperationNumber(o as uint64)
  else
    var co:COperationNumber :| (true); co
}

function {:opaque} AbstractifyCLearnerTuplesToLearnerTuples(m:map<COperationNumber,CLearnerTuple>) : map<OperationNumber,LearnerTuple>
  requires CLearnerTuplesAreAbstractable(m)
  ensures  var rm  := AbstractifyCLearnerTuplesToLearnerTuples(m);
           forall k :: k in rm ==> (exists ck :: ck in m && AbstractifyCOperationNumberToOperationNumber(ck) == k)
{
  AbstractifyMap(m, AbstractifyCOperationNumberToOperationNumber, AbstractifyCLearnerTupleToLearnerTuple, RefineOperationNumberToCOperationNumber)
}

lemma lemma_AbstractifyCLearnerTuplesToLearnerTuples_properties(m:map<COperationNumber,CLearnerTuple>)
  requires CLearnerTuplesAreAbstractable(m)
  ensures  m == map [] ==> AbstractifyCLearnerTuplesToLearnerTuples(m) == map []
  ensures  forall o :: (o in m <==> AbstractifyCOperationNumberToOperationNumber(o) in AbstractifyCLearnerTuplesToLearnerTuples(m))
  ensures  forall o :: (o !in m ==> AbstractifyCOperationNumberToOperationNumber(o) !in AbstractifyCLearnerTuplesToLearnerTuples(m))
  ensures  forall o :: o in m ==> AbstractifyCLearnerTuplesToLearnerTuples(m)[AbstractifyCOperationNumberToOperationNumber(o)] == AbstractifyCLearnerTupleToLearnerTuple(m[o])
  ensures  var rm  := AbstractifyCLearnerTuplesToLearnerTuples(m);
           forall k :: k in rm ==> (exists ck :: ck in m && AbstractifyCOperationNumberToOperationNumber(ck) == k)
  ensures  forall o, t {:trigger AbstractifyCOperationNumberToOperationNumber(o), AbstractifyCLearnerTupleToLearnerTuple(t)}
                      {:trigger m[o := t]} :: LearnerTupleIsAbstractable(t) ==>
             var rm  := AbstractifyCLearnerTuplesToLearnerTuples(m);
             var rm' := AbstractifyCLearnerTuplesToLearnerTuples(m[o := t]);
             rm' == AbstractifyCLearnerTuplesToLearnerTuples(m)[AbstractifyCOperationNumberToOperationNumber(o) := AbstractifyCLearnerTupleToLearnerTuple(t)]
  ensures  forall o {:trigger RemoveElt(m,o)} :: o in m ==>
             var rm  := AbstractifyCLearnerTuplesToLearnerTuples(m);
             var rm' := AbstractifyCLearnerTuplesToLearnerTuples(RemoveElt(m, o));
             rm' == RemoveElt(AbstractifyCLearnerTuplesToLearnerTuples(m), AbstractifyCOperationNumberToOperationNumber(o))
{
  var rm  := AbstractifyCLearnerTuplesToLearnerTuples(m);
  reveal AbstractifyCLearnerTuplesToLearnerTuples();

  lemma_AbstractifyMap_properties(m, AbstractifyCOperationNumberToOperationNumber, AbstractifyCLearnerTupleToLearnerTuple, RefineOperationNumberToCOperationNumber);
}

predicate LearnerState_IsAbstractable(learner:CLearnerState)
{
  && CBallotIsAbstractable(learner.max_ballot_seen)
  && ReplicaConstantsStateIsAbstractable(learner.rcs)
  && CLearnerTuplesAreAbstractable(learner.unexecuted_ops)
}

function AbstractifyLearnerStateToLLearner(learner:CLearnerState) : LLearner
  requires LearnerState_IsAbstractable(learner)
{
  var rcs := AbstractifyReplicaConstantsStateToLReplicaConstants(learner.rcs);
  var ballot := AbstractifyCBallotToBallot(learner.max_ballot_seen);
  var unexecuted_ops := AbstractifyCLearnerTuplesToLearnerTuples(learner.unexecuted_ops);
  LLearner(rcs, ballot, unexecuted_ops)
}

function LearnerState_EndPoint(learner:CLearnerState) : EndPoint
  requires LearnerState_IsValid(learner)
{
  learner.rcs.all.config.replica_ids[learner.rcs.my_index]
}

function LearnerState_Config(learner:CLearnerState) : CPaxosConfiguration
  requires LearnerState_IsValid(learner)
{
  learner.rcs.all.config
}

method LearnerState_Init(rcs:ReplicaConstantsState) returns (learner:CLearnerState)
  requires ReplicaConstantsStateIsAbstractable(rcs)
  requires ReplicaConstantsState_IsValid(rcs)
  ensures learner.rcs == rcs
  ensures LearnerState_IsValid(learner)
  ensures LLearnerInit(AbstractifyLearnerStateToLLearner(learner), AbstractifyReplicaConstantsStateToLReplicaConstants(learner.rcs))
{
  var endPoint := rcs.all.config.replica_ids[rcs.my_index];
  var unknown:CAppMessage := *;
  learner :=
    CLearnerState(
      rcs,
      CBallot(0, 0),
      map[],
      false, // sendDecision
      COperationNumber(0),
      false, // recv2b
      CPacket(
        endPoint,
        endPoint,
        CMessage_2b(
          CBallot(0,0),
          COperationNumber(0),
          [])));

  lemma_AbstractifyCLearnerTuplesToLearnerTuples_properties(learner.unexecuted_ops);
  assert LLearnerInit(AbstractifyLearnerStateToLLearner(learner), AbstractifyReplicaConstantsStateToLReplicaConstants(learner.rcs));
}

predicate LearnerState_CommonPreconditions(learner:CLearnerState)
{
  LearnerState_IsValid(learner)
}

predicate LearnerState_CommonPostconditions(learner:CLearnerState, learner':CLearnerState)
{
  && LearnerState_CommonPreconditions(learner)
  && LearnerState_IsValid(learner')
  && learner.rcs == learner'.rcs
}

predicate LearnerState_Process2b__Preconditions(learner:CLearnerState, executor:ExecutorState, packet:CPacket)
{
  && LearnerState_CommonPreconditions(learner)
  && ExecutorState_CommonPreconditions(executor)
  && CPacketIsAbstractable(packet)
  && packet.msg.CMessage_2b?
}

predicate LearnerState_Process2b__Postconditions(learner:CLearnerState, executor:ExecutorState, packet:CPacket, learner':CLearnerState)
{
  && LearnerState_Process2b__Preconditions(learner, executor, packet)
  && LearnerState_CommonPostconditions(learner, learner')
  && LLearnerProcess2b(AbstractifyLearnerStateToLLearner(learner), AbstractifyLearnerStateToLLearner(learner'), AbstractifyCPacketToRslPacket(packet))
}

predicate LearnerState_ForgetDecision__Preconditions(learner:CLearnerState, opn:COperationNumber)
{
  && LearnerState_CommonPreconditions(learner)
  && COperationNumberIsAbstractable(opn)
}

predicate LearnerState_ForgetDecision__Postconditions(learner:CLearnerState, opn:COperationNumber, learner':CLearnerState)
{
  && LearnerState_ForgetDecision__Preconditions(learner, opn)
  && LearnerState_CommonPostconditions(learner, learner')
  && LLearnerForgetDecision(AbstractifyLearnerStateToLLearner(learner), AbstractifyLearnerStateToLLearner(learner'), AbstractifyCOperationNumberToOperationNumber(opn))
}

predicate LearnerState_ForgetOperationsBefore__Preconditions(learner:CLearnerState, opn:COperationNumber)
{
  && LearnerState_CommonPreconditions(learner)
  && COperationNumberIsAbstractable(opn)
}

predicate LearnerState_ForgetOperationsBefore__Postconditions(learner:CLearnerState, opn:COperationNumber, learner':CLearnerState)
{
  && LearnerState_ForgetOperationsBefore__Preconditions(learner, opn)
  && LearnerState_CommonPostconditions(learner, learner')
  && LLearnerForgetOperationsBefore(AbstractifyLearnerStateToLLearner(learner), AbstractifyLearnerStateToLLearner(learner'), AbstractifyCOperationNumberToOperationNumber(opn))
}

} 
