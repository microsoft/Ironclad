include "../../Protocol/RSL/Learner.i.dfy"
include "ReplicaConstantsState.i.dfy"
include "ExecutorState.i.dfy"

module LiveRSL__LearnerState_i {
import opened LiveRSL__Learner_i
import opened LiveRSL__ReplicaConstantsState_i
import opened LiveRSL__ExecutorState_i

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
    SeqIsUnique(tuple.received_2b_message_senders)
 && |tuple.candidate_learned_value| <= RequestBatchSizeLimit()
}

predicate LearnerState_IsValid(learner:CLearnerState)
{
       LearnerState_IsAbstractable(learner)
    && (forall o :: o in learner.unexecuted_ops ==> CLearnerTupleIsValid(learner.unexecuted_ops[o]))
    && ReplicaConstantsState_IsValid(learner.rcs)
    && ReplicaConstantsStateIsAbstractable(learner.rcs)
}

predicate LearnerTupleIsAbstractable(tuple:CLearnerTuple)
{
       SeqOfEndPointsIsAbstractable(tuple.received_2b_message_senders)
    && CRequestBatchIsAbstractable(tuple.candidate_learned_value)
}

function AbstractifyCLearnerTupleToLearnerTuple(tuple:CLearnerTuple) : LearnerTuple
    requires LearnerTupleIsAbstractable(tuple);
{
    var pkts := AbstractifyEndPointsToNodeIdentities(tuple.received_2b_message_senders);
    var value := AbstractifyCRequestBatchToRequestBatch(tuple.candidate_learned_value);
    LearnerTuple(MapSeqToSet(pkts, x=>x), value)
}

predicate LearnerTuplesAreRefinable(tuples:map<COperationNumber,CLearnerTuple>)
{
       (forall opn :: opn in tuples ==> COperationNumberIsAbstractable(opn))
    && (forall opn :: opn in tuples ==> LearnerTupleIsAbstractable(tuples[opn]))
}

function RefineOperationNumberToCOperationNumber(o:OperationNumber) : COperationNumber 
    requires 0 <= o < 0x1_0000_0000_0000_0000;
{
    COperationNumber(uint64(o))
}

function {:opaque} RefineToLearnerTuples(m:map<COperationNumber,CLearnerTuple>) : map<OperationNumber,LearnerTuple>
    requires LearnerTuplesAreRefinable(m);
{
    RefineToMap(m, AbstractifyCOperationNumberToOperationNumber, AbstractifyCLearnerTupleToLearnerTuple, RefineOperationNumberToCOperationNumber)
}

//function{:opaque} RefineToLearnerTuples(tuples:map<COperationNumber,CLearnerTuple>) : map<OperationNumber,LLearnerTuple>
//    requires LearnerTuplesAreRefinable(tuples);
//{
//    var newDomain := set opn | opn in tuples :: AbstractifyCOperationNumberToOperationNumber(opn);
//    map opn | opn in newDomain :: AbstractifyCLearnerTupleToLearnerTuple(tuples[COperationNumber(uint64(opn))])
//}

lemma lemma_RefineToLearnerTuplesProperties(m:map<COperationNumber,CLearnerTuple>)
    requires LearnerTuplesAreRefinable(m);
    ensures  m == map [] ==> RefineToLearnerTuples(m) == map [];
    ensures  forall o :: (o in m <==> AbstractifyCOperationNumberToOperationNumber(o) in RefineToLearnerTuples(m));
    ensures  forall o :: (o !in m ==> AbstractifyCOperationNumberToOperationNumber(o) !in RefineToLearnerTuples(m));
    ensures  forall o :: o in m ==> RefineToLearnerTuples(m)[AbstractifyCOperationNumberToOperationNumber(o)] == AbstractifyCLearnerTupleToLearnerTuple(m[o]);
    ensures  var rm  := RefineToLearnerTuples(m);
             forall k :: k in rm ==> (exists ck :: ck in m && AbstractifyCOperationNumberToOperationNumber(ck) == k);
    ensures  forall o, t :: LearnerTupleIsAbstractable(t) ==>
                var rm  := RefineToLearnerTuples(m);
                var rm' := RefineToLearnerTuples(m[o := t]);
                rm' == RefineToLearnerTuples(m)[AbstractifyCOperationNumberToOperationNumber(o) := AbstractifyCLearnerTupleToLearnerTuple(t)];
    ensures  forall o {:trigger RemoveElt(m,o)} :: o in m ==>
                var rm  := RefineToLearnerTuples(m);
                var rm' := RefineToLearnerTuples(RemoveElt(m, o));
                rm' == RemoveElt(RefineToLearnerTuples(m), AbstractifyCOperationNumberToOperationNumber(o));
{
    reveal_RefineToLearnerTuples();

    lemma_RefineToMap_properties(m, AbstractifyCOperationNumberToOperationNumber, AbstractifyCLearnerTupleToLearnerTuple, RefineOperationNumberToCOperationNumber);
}

predicate LearnerState_IsAbstractable(learner:CLearnerState)
{
       CBallotIsAbstractable(learner.max_ballot_seen)
    && ReplicaConstantsStateIsAbstractable(learner.rcs)
    && LearnerTuplesAreRefinable(learner.unexecuted_ops)
}

function AbstractifyLearnerStateToLLearner(learner:CLearnerState) : LLearner
    requires LearnerState_IsAbstractable(learner);
{
    var rcs := AbstractifyReplicaConstantsStateToLReplicaConstants(learner.rcs);
    var ballot := AbstractifyCBallotToBallot(learner.max_ballot_seen);
    var unexecuted_ops := RefineToLearnerTuples(learner.unexecuted_ops);
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

/*
   THIS LEMMA IS NO LONGER TRUE!  We now refine to a set of message senders
   rather than a sequence.  So, if the message senders are in a different order,
   it may still refine to the same thing.

lemma lemma_RefineToLearnerTupleIsInjective(c1:CLearnerTuple, c2:CLearnerTuple)
    requires LearnerTupleIsAbstractable(c1);
    requires LearnerTupleIsAbstractable(c2);
    requires AbstractifyCLearnerTupleToLearnerTuple(c1) == AbstractifyCLearnerTupleToLearnerTuple(c2);
    ensures  c1 == c2;
{
    var rc1 := AbstractifyCLearnerTupleToLearnerTuple(c1);
    var rc2 := AbstractifyCLearnerTupleToLearnerTuple(c2);
    assert rc1.received_2b_message_senders == rc2.received_2b_message_senders;
    assert rc1.candidate_learned_value == rc2.candidate_learned_value;
    lemma_AbstractifyCRequestBatchToRequestBatch_isInjective();
    lemma_AbstractifyEndPointsToNodeIdentities_injective(c1.received_2b_message_senders, c2.received_2b_message_senders);
}

*/

method LearnerState_Init(rcs:ReplicaConstantsState) returns (learner:CLearnerState)
    requires ReplicaConstantsStateIsAbstractable(rcs);
    requires ReplicaConstantsState_IsValid(rcs);
    ensures learner.rcs == rcs;
    ensures LearnerState_IsValid(learner);
    ensures LLearnerInit(AbstractifyLearnerStateToLLearner(learner), AbstractifyReplicaConstantsStateToLReplicaConstants(learner.rcs));
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

    lemma_RefineToLearnerTuplesProperties(learner.unexecuted_ops);
    assert LLearnerInit(AbstractifyLearnerStateToLLearner(learner), AbstractifyReplicaConstantsStateToLReplicaConstants(learner.rcs));
}

predicate LearnerState_CommonPreconditions(learner:CLearnerState)
{
    LearnerState_IsValid(learner)
}

predicate LearnerState_CommonPostconditions(learner:CLearnerState, learner':CLearnerState)
{
       LearnerState_CommonPreconditions(learner)
    && LearnerState_IsValid(learner')
    && learner.rcs == learner'.rcs
}

predicate LearnerState_Process2b__Preconditions(learner:CLearnerState, executor:ExecutorState, packet:CPacket)
{
       LearnerState_CommonPreconditions(learner)
    && ExecutorState_CommonPreconditions(executor)
    && CPacketIsAbstractable(packet)
    && packet.msg.CMessage_2b?
}

predicate LearnerState_Process2b__Postconditions(learner:CLearnerState, executor:ExecutorState, packet:CPacket, learner':CLearnerState)
{
       LearnerState_Process2b__Preconditions(learner, executor, packet)
    && LearnerState_CommonPostconditions(learner, learner')
    && LLearnerProcess2b(AbstractifyLearnerStateToLLearner(learner), AbstractifyLearnerStateToLLearner(learner'), AbstractifyCPacketToRslPacket(packet))
}

predicate LearnerState_ForgetDecision__Preconditions(learner:CLearnerState, opn:COperationNumber)
{
       LearnerState_CommonPreconditions(learner)
    && COperationNumberIsAbstractable(opn)
}

predicate LearnerState_ForgetDecision__Postconditions(learner:CLearnerState, opn:COperationNumber, learner':CLearnerState)
{
       LearnerState_ForgetDecision__Preconditions(learner, opn)
    && LearnerState_CommonPostconditions(learner, learner')
    && LLearnerForgetDecision(AbstractifyLearnerStateToLLearner(learner), AbstractifyLearnerStateToLLearner(learner'), AbstractifyCOperationNumberToOperationNumber(opn))
}

predicate LearnerState_ForgetOperationsBefore__Preconditions(learner:CLearnerState, opn:COperationNumber)
{
       LearnerState_CommonPreconditions(learner)
    && COperationNumberIsAbstractable(opn)
}

predicate LearnerState_ForgetOperationsBefore__Postconditions(learner:CLearnerState, opn:COperationNumber, learner':CLearnerState)
{
       LearnerState_ForgetOperationsBefore__Preconditions(learner, opn)
    && LearnerState_CommonPostconditions(learner, learner')
    && LLearnerForgetOperationsBefore(AbstractifyLearnerStateToLLearner(learner), AbstractifyLearnerStateToLLearner(learner'), AbstractifyCOperationNumberToOperationNumber(opn))
}

} 
