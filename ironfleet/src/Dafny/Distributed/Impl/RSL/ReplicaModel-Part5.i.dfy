include "AppInterface.i.dfy"
include "ReplicaState.i.dfy"
include "ProposerModel.i.dfy"
include "AcceptorModel.i.dfy"
include "LearnerModel.i.dfy"
include "ExecutorModel.i.dfy"
include "../Common/Util.i.dfy"

module LiveRSL__ReplicaModel_Part5_i {
import opened LiveRSL__AppInterface_i
import opened LiveRSL__ReplicaState_i
import opened LiveRSL__ProposerModel_i
import opened LiveRSL__AcceptorModel_i
import opened LiveRSL__LearnerModel_i
import opened LiveRSL__ExecutorModel_i

method ReplicaNextProcessAppStateSupplyIgnore(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
    requires Replica_Next_Process_AppStateSupply_Preconditions(replica, inp);
    requires    inp.src !in replica.executor.constants.all.config.replica_ids
             || inp.msg.opn_state_supply.n <= replica.executor.ops_complete.n;
    ensures  Replica_Next_Process_AppStateSupply_Postconditions(replica, replica', inp, packets_sent);
    ensures  replica' == replica;
{
    replica' := replica;
    packets_sent := Broadcast(CBroadcastNop);
}

method ReplicaNextProcessAppStateSupplyActual(replica:ReplicaState, inp:CPacket)
    returns
    (replica':ReplicaState,
     packets_sent:OutboundPackets,
     reply_cache_mutable:MutableMap<EndPoint, CReply>)
    requires Replica_Next_Process_AppStateSupply_Preconditions(replica, inp);
    requires inp.src in replica.executor.constants.all.config.replica_ids;
    requires inp.msg.opn_state_supply.n > replica.executor.ops_complete.n;
    ensures  Replica_Next_Process_AppStateSupply_Postconditions(replica, replica', inp, packets_sent);
    ensures  replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set;
    ensures  replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set;
    ensures  reply_cache_mutable != null;
    ensures  fresh(reply_cache_mutable);
    ensures  replica'.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable);
{
    var newLearner := LearnerModel_ForgetOperationsBefore(replica.learner, inp.msg.opn_state_supply);
    var newExecutor;
    newExecutor, reply_cache_mutable := ExecutorProcessAppStateSupply(replica.executor, inp);
    replica' := replica[learner := newLearner]
                       [executor := newExecutor];
    packets_sent := Broadcast(CBroadcastNop);
}

method Replica_Next_Process_AppStateSupply(replica:ReplicaState, inp:CPacket)
    returns
    (replica':ReplicaState,
     packets_sent:OutboundPackets,
     replicaChanged:bool,
     reply_cache_mutable:MutableMap<EndPoint, CReply>)
    requires Replica_Next_Process_AppStateSupply_Preconditions(replica, inp);
    ensures  Replica_Next_Process_AppStateSupply_Postconditions(replica, replica', inp, packets_sent);
    ensures  replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set;
    ensures  replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set;
    ensures  replicaChanged ==> reply_cache_mutable != null && fresh(reply_cache_mutable);
    ensures  replicaChanged ==> replica'.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable);
    ensures  !replicaChanged ==> replica' == replica;
{
    var start_time := Time.GetDebugTimeTicks();
//    lemma_AbstractifyEndPointsToNodeIdentities_properties(replica.executor.constants.all.config.replica_ids);
    if (    inp.src in replica.executor.constants.all.config.replica_ids
         && inp.msg.opn_state_supply.n > replica.executor.ops_complete.n)
    {
        replica', packets_sent, reply_cache_mutable := ReplicaNextProcessAppStateSupplyActual(replica, inp);
        var end_time := Time.GetDebugTimeTicks();
        RecordTimingSeq("Replica_Next_Process_AppStateSupply_work", start_time, end_time);
        replicaChanged := true;
    } else {
        replica', packets_sent := ReplicaNextProcessAppStateSupplyIgnore(replica, inp);
        var end_time := Time.GetDebugTimeTicks();
        RecordTimingSeq("Replica_Next_Process_AppStateSupply_nada", start_time, end_time);
        replicaChanged := false;
    }
    //lemma_RefineCPacketsToPacketsProperties(packets_sent);
}

method ReplicaNextSpontaneousMaybeExecuteIgnore(replica:ReplicaState) returns (replica':ReplicaState, packets_sent:OutboundPackets)
    requires Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica);
    requires    !replica.executor.next_op_to_execute.COutstandingOpKnown?
             || replica.executor.ops_complete.n >= replica.executor.constants.all.params.max_integer_val;
    ensures  Replica_Next_Spontaneous_MaybeExecute_Postconditions(replica, replica', packets_sent);
    ensures  replica' == replica;
{
    replica' := replica;
    packets_sent := OutboundPacket(None);
}

method ReplicaNextSpontaneousMaybeExecuteActual(
    replica:ReplicaState,
    cur_req_set:MutableSet<CRequestHeader>,
    prev_req_set:MutableSet<CRequestHeader>,
    reply_cache_mutable:MutableMap<EndPoint, CReply>)
    returns
    (replica':ReplicaState, packets_sent:OutboundPackets)
    requires Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica);
    requires cur_req_set != null && prev_req_set != null && cur_req_set != prev_req_set;
    requires MutableSet.SetOf(cur_req_set) == replica.proposer.election_state.cur_req_set;
    requires MutableSet.SetOf(prev_req_set) == replica.proposer.election_state.prev_req_set;
    requires reply_cache_mutable != null && replica.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable);
    requires replica.executor.next_op_to_execute.COutstandingOpKnown?;
    requires replica.executor.ops_complete.n < replica.executor.constants.all.params.max_integer_val;
    modifies cur_req_set, prev_req_set, reply_cache_mutable;
    ensures  Replica_Next_Spontaneous_MaybeExecute_Postconditions(replica, replica', packets_sent);
    ensures  MutableSet.SetOf(cur_req_set) == replica'.proposer.election_state.cur_req_set;
    ensures  MutableSet.SetOf(prev_req_set) == replica'.proposer.election_state.prev_req_set;
    ensures  replica'.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable);
{
    var val := replica.executor.next_op_to_execute.v;
    //assert ValidRequestBatch(replica.executor.next_op_to_execute.v);
    
    //var end_time_proposer := Time.GetDebugTimeTicks();

    //var start_time_learner := Time.GetDebugTimeTicks();
    var newLearner := LearnerModel_ForgetDecision(replica.learner, replica.executor.ops_complete);
    assert LLearnerForgetDecision(AbstractifyLearnerStateToLLearner(replica.learner), AbstractifyLearnerStateToLLearner(newLearner), 
                                   AbstractifyCOperationNumberToOperationNumber(replica.executor.ops_complete));
    //var end_time_learner := Time.GetDebugTimeTicks();

    //var start_time_executor := Time.GetDebugTimeTicks();
    var newExecutor, packets := ExecutorExecute(replica.executor, reply_cache_mutable);
    assert LExecutorExecute(AbstractifyExecutorStateToLExecutor(replica.executor), AbstractifyExecutorStateToLExecutor(newExecutor), 
                             AbstractifyOutboundCPacketsToSeqOfRslPackets(packets));
    //var end_time_executor := Time.GetDebugTimeTicks();

    var newProposer := ProposerResetViewTimerDueToExecution(replica.proposer, val, cur_req_set, prev_req_set);
    assert LProposerResetViewTimerDueToExecution(AbstractifyProposerStateToLProposer(replica.proposer), 
                                                  AbstractifyProposerStateToLProposer(newProposer), 
                                                  AbstractifyCRequestBatchToRequestBatch(val));
    assert MutableSet.SetOf(cur_req_set) == newProposer.election_state.cur_req_set;
    assert MutableSet.SetOf(prev_req_set) == newProposer.election_state.prev_req_set;
    
    replica' := replica[proposer := newProposer]
                       [learner := newLearner]
                       [executor := newExecutor];
    packets_sent := packets;

    ghost var s := AbstractifyReplicaStateToLReplica(replica);
    ghost var s' := AbstractifyReplicaStateToLReplica(replica');
    ghost var sent_packets := AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent);

    assert LProposerResetViewTimerDueToExecution(s.proposer, s'.proposer, AbstractifyCRequestBatchToRequestBatch(val));
    assert LLearnerForgetDecision(s.learner, s'.learner, AbstractifyCOperationNumberToOperationNumber(replica.executor.ops_complete));
    assert LExecutorExecute(s.executor, s'.executor, sent_packets);
    assert LReplicaNextSpontaneousMaybeExecute(s, s', sent_packets);
}

method Replica_Next_Spontaneous_MaybeExecute(
    replica:ReplicaState,
    cur_req_set:MutableSet<CRequestHeader>,
    prev_req_set:MutableSet<CRequestHeader>,
    reply_cache_mutable:MutableMap<EndPoint, CReply>)
    returns
    (replica':ReplicaState, packets_sent:OutboundPackets)
    requires Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica);
    requires cur_req_set != null && prev_req_set != null && cur_req_set != prev_req_set;
    requires MutableSet.SetOf(cur_req_set) == replica.proposer.election_state.cur_req_set;
    requires MutableSet.SetOf(prev_req_set) == replica.proposer.election_state.prev_req_set;
    requires reply_cache_mutable != null && replica.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable);
    modifies cur_req_set, prev_req_set, reply_cache_mutable;
    ensures Replica_Next_Spontaneous_MaybeExecute_Postconditions(replica, replica', packets_sent);
    ensures  MutableSet.SetOf(cur_req_set) == replica'.proposer.election_state.cur_req_set;
    ensures  MutableSet.SetOf(prev_req_set) == replica'.proposer.election_state.prev_req_set;
    ensures  replica'.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable);
{
    //var start_time := Time.GetDebugTimeTicks();
    if (    replica.executor.next_op_to_execute.COutstandingOpKnown?
         && replica.executor.ops_complete.n < replica.executor.constants.all.params.max_integer_val
        )
    {
        replica', packets_sent := ReplicaNextSpontaneousMaybeExecuteActual(replica, cur_req_set, prev_req_set, reply_cache_mutable);
        //var end_time := Time.GetDebugTimeTicks();
//        RecordTimingSeq("Replica_Next_Spontaneous_MaybeExecute_work", start_time, end_time);
//        RecordTimingSeq("Replica_Next_Spontaneous_MaybeExecute_work_proposer", start_time, end_time_proposer);
//        RecordTimingSeq("Replica_Next_Spontaneous_MaybeExecute_work_learner", start_time_learner, end_time_learner);
//        RecordTimingSeq("Replica_Next_Spontaneous_MaybeExecute_work_execute", start_time_executor, end_time_executor);
    } else {
        replica', packets_sent := ReplicaNextSpontaneousMaybeExecuteIgnore(replica);
        //var end_time := Time.GetDebugTimeTicks();
//        RecordTimingSeq("Replica_Next_Spontaneous_MaybeExecute_nada", start_time, end_time);
    }
    //lemma_AbstractifyCPacketToRslPacket_src(packets_sent, replica.constants.all.config.replica_ids[replica.constants.my_index]);
}

method ReplicaNextReadClockMaybeSendHeartbeatSkip(
    replica:ReplicaState,
    clock:CClockReading
    ) returns (replica':ReplicaState, packets_sent:OutboundPackets)
    requires Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica);
    requires clock.t < replica.nextHeartbeatTime;
    ensures  Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions(replica, replica', clock, packets_sent);
    ensures  replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set;
    ensures  replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set;
    ensures  replica'.executor.reply_cache == replica.executor.reply_cache;
{
    replica' := replica;
    packets_sent := Broadcast(CBroadcastNop);
    //lemma_RefineCPacketsToPacketsProperties(packets_sent);
}

method ReplicaNextReadClockMaybeSendHeartbeatActual(
    replica:ReplicaState,
    clock:CClockReading
    ) returns (replica':ReplicaState, packets_sent:OutboundPackets)
    requires Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica);
    requires clock.t >= replica.nextHeartbeatTime;
    ensures  Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions(replica, replica', clock, packets_sent);
    ensures  replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set;
    ensures  replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set;
    ensures  replica'.executor.reply_cache == replica.executor.reply_cache;
{
    var heartbeat := UpperBoundedAdditionImpl(clock.t, replica.constants.all.params.heartbeat_period, replica.constants.all.params.max_integer_val);
    replica' := replica[nextHeartbeatTime := heartbeat];
    var flag := (replica.constants.my_index in replica.proposer.election_state.current_view_suspectors);
    var msg := CMessage_Heartbeat(replica.proposer.election_state.current_view, flag, replica.executor.ops_complete);
    var packets := BuildBroadcastToEveryone(replica.constants.all.config, replica.constants.my_index, msg);
    lemma_AbstractifySeqOfUint64sToSetOfInts_properties(replica.proposer.election_state.current_view_suspectors);
    packets_sent := Broadcast(packets);
    //lemma_RefineCPacketsToPacketsProperties(packets_sent);
}

method Replica_Next_ReadClock_MaybeSendHeartbeat(
    replica:ReplicaState,
    clock:CClockReading
    ) returns (replica':ReplicaState, packets_sent:OutboundPackets)
    requires Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica);
    ensures Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions(replica, replica', clock, packets_sent);
    ensures replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set;
    ensures replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set;
    ensures  replica'.executor.reply_cache == replica.executor.reply_cache;
{
    var start_time := Time.GetDebugTimeTicks();
    if (clock.t >= replica.nextHeartbeatTime) {
        replica', packets_sent := ReplicaNextReadClockMaybeSendHeartbeatActual(replica, clock);
        var end_time := Time.GetDebugTimeTicks();
        RecordTimingSeq("Replica_Next_ReadClock_MaybeSendHeartbeat_work", start_time, end_time);
    } else {
        replica', packets_sent := ReplicaNextReadClockMaybeSendHeartbeatSkip(replica, clock);
        var end_time := Time.GetDebugTimeTicks();
        RecordTimingSeq("Replica_Next_ReadClock_MaybeSendHeartbeat_nada", start_time, end_time);
    }
    //lemma_AbstractifyCPacketToRslPacket_src(packets_sent, replica.constants.all.config.replica_ids[replica.constants.my_index]);
}

method ReplicaNextSpontaneousMaybeMakeDecisionSkip(replica:ReplicaState) returns (replica':ReplicaState, packets_sent:OutboundPackets)
    requires Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica);
    requires var opn := replica.executor.ops_complete;
                !replica.executor.next_op_to_execute.COutstandingOpUnknown?
             || opn !in replica.learner.unexecuted_ops
             || |replica.learner.unexecuted_ops[opn].received_2b_message_senders| < LMinQuorumSize(AbstractifyCPaxosConfigurationToConfiguration(replica.learner.rcs.all.config));
    ensures  Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(replica, replica', packets_sent);
    ensures  replica' == replica;
{
    replica' := replica;
    packets_sent := Broadcast(CBroadcastNop);

    lemma_AbstractifyCOperationNumberToOperationNumber_isInjective();
    lemma_RefineToLearnerTuplesProperties(replica.learner.unexecuted_ops);

    ghost var s := AbstractifyReplicaStateToLReplica(replica);
    ghost var opn := replica.executor.ops_complete;
    if replica.executor.next_op_to_execute.COutstandingOpUnknown? && opn in replica.learner.unexecuted_ops
    {
        assert AbstractifyCOperationNumberToOperationNumber(opn) in s.learner.unexecuted_learner_state;
        calc {
            |s.learner.unexecuted_learner_state[AbstractifyCOperationNumberToOperationNumber(opn)].received_2b_message_senders|;
                { lemma_Received2bPacketsSameSizeAsRefinement(replica.learner.unexecuted_ops[opn], AbstractifyCLearnerTupleToLearnerTuple(replica.learner.unexecuted_ops[opn])); }
            |replica.learner.unexecuted_ops[opn].received_2b_message_senders|;
            < LMinQuorumSize(AbstractifyCPaxosConfigurationToConfiguration(replica.learner.rcs.all.config));
            LMinQuorumSize(s.learner.constants.all.config);
        }
    }
}

method ReplicaNextSpontaneousMaybeMakeDecisionActual(replica:ReplicaState) returns (replica':ReplicaState, packets_sent:OutboundPackets)
    requires Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica);
    requires replica.executor.next_op_to_execute.COutstandingOpUnknown?;
    requires replica.executor.ops_complete in replica.learner.unexecuted_ops;
    requires |replica.learner.unexecuted_ops[replica.executor.ops_complete].received_2b_message_senders| >= LMinQuorumSize(AbstractifyCPaxosConfigurationToConfiguration(replica.learner.rcs.all.config));
    ensures  Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(replica, replica', packets_sent);
    ensures  replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set;
    ensures  replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set;
    ensures  replica'.executor.reply_cache == replica.executor.reply_cache;
{
    lemma_AbstractifyCOperationNumberToOperationNumber_isInjective();
    lemma_AbstractifyCRequestToRequest_isInjective();
    lemma_RefineToLearnerTuplesProperties(replica.learner.unexecuted_ops);
    
    var opn := replica.executor.ops_complete;

    lemma_Received2bPacketsSameSizeAsRefinement(replica.learner.unexecuted_ops[opn], AbstractifyCLearnerTupleToLearnerTuple(replica.learner.unexecuted_ops[opn]));

    var candValue:CRequestBatch := replica.learner.unexecuted_ops[opn].candidate_learned_value;
    assert CLearnerTupleIsValid(replica.learner.unexecuted_ops[opn]);
    assert ValidRequestBatch(replica.learner.unexecuted_ops[opn].candidate_learned_value);
    var newExecutor := ExecutorGetDecision(replica.executor, replica.learner.max_ballot_seen, opn, candValue);

    /*
    if (replica.learner.unexecuted_ops[opn].candidate_learned_value.CValue?) {
        candValue := replica.learner.unexecuted_ops[opn].candidate_learned_value;
        newExecutor := ExecutorGetDecision(replica.executor, opn, candValue);
        assert LExecutorGetDecision(AbstractifyExecutorStateToLExecutor(replica.executor), AbstractifyExecutorStateToLExecutor(newExecutor), AbstractifyCOperationNumberToOperationNumber(opn), RefineToValue(candValue));
    } else {
        candValue := CValueNoOp();
        newExecutor := ExecutorGetDecision(replica.executor, opn, candValue);
        assert LExecutorGetDecision(AbstractifyExecutorStateToLExecutor(replica.executor), AbstractifyExecutorStateToLExecutor(newExecutor), AbstractifyCOperationNumberToOperationNumber(opn), RefineToValue(candValue));
    }
    */

    //assert RefineToAppRequest(candValue) == 
    replica' := replica[executor := newExecutor];

    packets_sent := Broadcast(CBroadcastNop);
    //lemma_RefineCPacketsToPacketsProperties(packets_sent);
    lemma_AbstractifyCRequestToRequest_isInjective();

    /*
    if (candValue.CValue?) {
        assert !candValue.CValueNoOp?;
        //assert RefineToAppRequest(candValue) == RefineToValue(replica.learner.unexecuted_ops[opn].candidate_learned_value);
        assert Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(replica, replica', packets_sent);
    } else {
        //assert RefineToAppRequest(candValue) == AppValueNoOp();
        assert candValue.CValueNoOp?;
        assert RefineToAppRequest(CValueNoOp()) == ValueNoOp();
        assert Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(replica, replica', packets_sent);
    }
     */

    ghost var s := AbstractifyReplicaStateToLReplica(replica);
    ghost var s' := AbstractifyReplicaStateToLReplica(replica');
    ghost var sent_packets := AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent);

    assert LExecutorGetDecision(s.executor, s'.executor, AbstractifyCBallotToBallot(replica.learner.max_ballot_seen),
                                 AbstractifyCOperationNumberToOperationNumber(opn), AbstractifyCRequestBatchToRequestBatch(candValue));
    assert LReplicaNextSpontaneousMaybeMakeDecision(s, s', sent_packets);
}

method Replica_Next_Spontaneous_MaybeMakeDecision(replica:ReplicaState) returns (replica':ReplicaState, packets_sent:OutboundPackets)
    requires Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica);
    ensures Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(replica, replica', packets_sent);
    ensures replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set;
    ensures replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set;
    ensures  replica'.executor.reply_cache == replica.executor.reply_cache;
{
    var start_time := Time.GetDebugTimeTicks();
    var opn := replica.executor.ops_complete;
    var minCQS := MinCQuorumSize(replica.learner.rcs.all.config);

    if (   replica.executor.next_op_to_execute.COutstandingOpUnknown?
        && opn in replica.learner.unexecuted_ops
        && (|replica.learner.unexecuted_ops[opn].received_2b_message_senders|) >= int(minCQS))
    {
        replica', packets_sent := ReplicaNextSpontaneousMaybeMakeDecisionActual(replica);
        var end_time := Time.GetDebugTimeTicks();
        RecordTimingSeq("Replica_Next_Spontaneous_MaybeMakeDecision_work", start_time, end_time);
    } else {
        replica', packets_sent := ReplicaNextSpontaneousMaybeMakeDecisionSkip(replica);
        var end_time := Time.GetDebugTimeTicks();
        RecordTimingSeq("Replica_Next_Spontaneous_MaybeMakeDecision_nada", start_time, end_time);
    }
}

method ReplicaNextSpontaneousTruncateLogBasedOnCheckpointsSkip(
    replica:ReplicaState,
    newLogTruncationPoint:COperationNumber
    )
    returns (replica':ReplicaState, packets_sent:OutboundPackets)
    requires Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica);
    requires IsLogTruncationPointValid(AbstractifyCOperationNumberToOperationNumber(newLogTruncationPoint),
                                       AbstractifyReplicaStateToLReplica(replica).acceptor.last_checkpointed_operation,
                                       AbstractifyReplicaStateToLReplica(replica).acceptor.constants.all.config);
    requires newLogTruncationPoint.n <= replica.acceptor.log_truncation_point.n;
    ensures  Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions(replica, replica', packets_sent);
    ensures  replica' == replica;
{
    replica' := replica;
    packets_sent := Broadcast(CBroadcastNop);
}

method ReplicaNextSpontaneousTruncateLogBasedOnCheckpointsActual(
    replica:ReplicaState,
    newLogTruncationPoint:COperationNumber
    )
    returns (replica':ReplicaState, packets_sent:OutboundPackets)
    requires Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica);
    requires IsLogTruncationPointValid(AbstractifyCOperationNumberToOperationNumber(newLogTruncationPoint),
                                       AbstractifyReplicaStateToLReplica(replica).acceptor.last_checkpointed_operation,
                                       AbstractifyReplicaStateToLReplica(replica).acceptor.constants.all.config);
    requires newLogTruncationPoint.n > replica.acceptor.log_truncation_point.n;
    ensures  Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions(replica, replica', packets_sent);
    ensures  replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set;
    ensures  replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set;
    ensures  replica'.executor.reply_cache == replica.executor.reply_cache;
{
    assert AbstractifyCOperationNumberToOperationNumber(newLogTruncationPoint) > AbstractifyAcceptorStateToAcceptor(replica.acceptor).log_truncation_point;
    var newAcceptor := NextAcceptorState_TruncateLog(replica.acceptor, newLogTruncationPoint);
    replica' := replica[acceptor := newAcceptor];
    packets_sent := Broadcast(CBroadcastNop);
    //lemma_RefineCPacketsToPacketsProperties(packets_sent);
}

method Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints(replica:ReplicaState)
    returns (replica':ReplicaState, packets_sent:OutboundPackets)
    requires Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica);
    ensures  Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions(replica, replica', packets_sent);
    ensures  replica'.proposer.election_state.cur_req_set == replica.proposer.election_state.cur_req_set;
    ensures  replica'.proposer.election_state.prev_req_set == replica.proposer.election_state.prev_req_set;
    ensures  replica'.executor.reply_cache == replica.executor.reply_cache;
{
    var start_time := Time.GetDebugTimeTicks();
    var minCQS := MinCQuorumSize(replica.acceptor.constants.all.config);
    var newLogTruncationPoint := AcceptorModel_GetNthHighestValueAmongReportedCheckpoints(replica.acceptor, minCQS);
    if newLogTruncationPoint.n > replica.acceptor.log_truncation_point.n {
        replica', packets_sent := ReplicaNextSpontaneousTruncateLogBasedOnCheckpointsActual(replica, newLogTruncationPoint);
        var end_time := Time.GetDebugTimeTicks();
        RecordTimingSeq("Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_work", start_time, end_time);
    } else {
        replica', packets_sent := ReplicaNextSpontaneousTruncateLogBasedOnCheckpointsSkip(replica, newLogTruncationPoint);
        var end_time := Time.GetDebugTimeTicks();
        RecordTimingSeq("Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_nada", start_time, end_time);
    }
}

} 
