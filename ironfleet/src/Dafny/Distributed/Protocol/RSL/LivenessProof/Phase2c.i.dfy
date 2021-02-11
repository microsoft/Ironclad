include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "StablePeriod.i.dfy"
include "NextOp.i.dfy"
include "Phase2b.i.dfy"
include "GenericInvariants.i.dfy"
include "../CommonProof/Quorum.i.dfy"
include "../CommonProof/LearnerState.i.dfy"

// Sure, there's no Phase 2c in Paxos.  But it's what this file calls the phase
// when the executors have finished executing the request and are telling the
// primary about it so it can do log truncation.

module LivenessProof__Phase2c_i {

import opened LiveRSL__Acceptor_i
import opened LiveRSL__Broadcast_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Message_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Catchup_i
import opened LivenessProof__Environment_i
import opened LivenessProof__GenericInvariants_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__NextOp_i
import opened LivenessProof__PacketHandling_i
import opened LivenessProof__Phase2b_i
import opened LivenessProof__Phase2Invariants_i
import opened LivenessProof__RealTime_i
import opened LivenessProof__RoundRobin_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__WF1_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened CommonProof__LogTruncationPoint_i
import opened CommonProof__Quorum_i
import opened Temporal__Induction_i
import opened Temporal__LeadsTo_i
import opened Temporal__Rules_i
import opened Temporal__Sets_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Temporal__Time_i
import opened Temporal__WF1_i
import opened Environment_s
import opened Collections__CountMatches_i
import opened Collections__Maps2_s
import opened Collections__Sets_i
import opened Math__mul_i

predicate ReplicaSentHeartbeatToPrimaryReflectingOpn(
  ps:RslState,
  replica_idx:int,
  primary_idx:int,
  opn:OperationNumber,
  p:RslPacket
  )
{
  && ps.environment.nextStep.LEnvStepHostIos?
  && LIoOpSend(p) in ps.environment.nextStep.ios
  && 0 <= replica_idx < |ps.constants.config.replica_ids|
  && 0 <= primary_idx < |ps.constants.config.replica_ids|
  && p.src == ps.constants.config.replica_ids[replica_idx]
  && p.dst == ps.constants.config.replica_ids[primary_idx]
  && p.msg.RslMessage_Heartbeat?
  && p.msg.opn_ckpt >= opn
  && 0 <= replica_idx < |ps.replicas|
  && ps.replicas[replica_idx].replica.executor.ops_complete >= opn
}

function{:opaque} ReplicaSentHeartbeatToPrimaryReflectingOpnTemporal(
  b:Behavior<RslState>,
  replica_idx:int,
  primary_idx:int,
  opn:OperationNumber
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, ReplicaSentHeartbeatToPrimaryReflectingOpnTemporal(b, replica_idx, primary_idx, opn))} ::
             sat(i, ReplicaSentHeartbeatToPrimaryReflectingOpnTemporal(b, replica_idx, primary_idx, opn)) <==>
             exists p :: ReplicaSentHeartbeatToPrimaryReflectingOpn(b[i], replica_idx, primary_idx, opn, p)
{
  stepmap(imap i :: exists p :: ReplicaSentHeartbeatToPrimaryReflectingOpn(b[i], replica_idx, primary_idx, opn, p))
}

function{:opaque} NextHeartbeatTimeOfReplicaIsParticularValueTemporal(
  b:Behavior<RslState>,
  idx:int,
  nextHeartbeatTime:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, NextHeartbeatTimeOfReplicaIsParticularValueTemporal(b, idx, nextHeartbeatTime))} ::
             sat(i, NextHeartbeatTimeOfReplicaIsParticularValueTemporal(b, idx, nextHeartbeatTime)) <==>
             (0 <= idx < |b[i].replicas| && b[i].replicas[idx].replica.nextHeartbeatTime == nextHeartbeatTime)
{
  stepmap(imap i :: 0 <= idx < |b[i].replicas| && b[i].replicas[idx].replica.nextHeartbeatTime == nextHeartbeatTime)
}

predicate PrimaryKnowsReplicaHasOpsComplete(
  ps:RslState,
  replica_idx:int,
  primary_idx:int,
  opn:OperationNumber
  )
{
  && 0 <= primary_idx < |ps.replicas|
  && 0 <= replica_idx < |ps.replicas|
  && 0 <= replica_idx < |ps.replicas[primary_idx].replica.acceptor.last_checkpointed_operation|
  && ps.replicas[primary_idx].replica.acceptor.last_checkpointed_operation[replica_idx] >= opn
  && ps.replicas[replica_idx].replica.executor.ops_complete>= opn
}

function{:opaque} PrimaryKnowsReplicaHasOpsCompleteTemporal(
  b:Behavior<RslState>,
  replica_idx:int,
  primary_idx:int,
  opn:OperationNumber
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, PrimaryKnowsReplicaHasOpsCompleteTemporal(b, replica_idx, primary_idx, opn))} ::
             sat(i, PrimaryKnowsReplicaHasOpsCompleteTemporal(b, replica_idx, primary_idx, opn)) <==>
             PrimaryKnowsReplicaHasOpsComplete(b[i], replica_idx, primary_idx, opn)
{
  stepmap(imap i :: PrimaryKnowsReplicaHasOpsComplete(b[i], replica_idx, primary_idx, opn))
}

function{:opaque} PrimaryKnowsEveryReplicaHasOpsCompleteTemporalSet(
  b:Behavior<RslState>,
  replica_indices:set<int>,
  primary_idx:int,
  opn:OperationNumber
  ):set<temporal>
  requires imaptotal(b)
  ensures  forall replica_idx :: replica_idx in replica_indices
             ==> PrimaryKnowsReplicaHasOpsCompleteTemporal(b, replica_idx, primary_idx, opn)
                 in PrimaryKnowsEveryReplicaHasOpsCompleteTemporalSet(b, replica_indices, primary_idx, opn)
  ensures  forall x :: x in PrimaryKnowsEveryReplicaHasOpsCompleteTemporalSet(b, replica_indices, primary_idx, opn) ==>
             exists replica_idx :: && replica_idx in replica_indices
                             && x == PrimaryKnowsReplicaHasOpsCompleteTemporal(b, replica_idx, primary_idx, opn)
{
  set replica_idx | replica_idx in replica_indices :: PrimaryKnowsReplicaHasOpsCompleteTemporal(b, replica_idx, primary_idx, opn)
}

predicate PrimaryHasAdvancedLogTruncationPoint(
  ps:RslState,
  live_quorum:set<int>,
  view:Ballot,
  opn:int
  )
{
  && (forall idx :: idx in live_quorum ==> ReplicaCaughtUp(ps, idx, opn))
  && 0 <= view.proposer_id < |ps.replicas|
  && ps.replicas[view.proposer_id].replica.acceptor.log_truncation_point >= opn
}

function {:opaque} PrimaryHasAdvancedLogTruncationPointTemporal(
  b:Behavior<RslState>,
  live_quorum:set<int>,
  view:Ballot,
  opn:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, PrimaryHasAdvancedLogTruncationPointTemporal(b, live_quorum, view, opn))} ::
             sat(i, PrimaryHasAdvancedLogTruncationPointTemporal(b, live_quorum, view, opn)) ==
             PrimaryHasAdvancedLogTruncationPoint(b[i], live_quorum, view, opn)
{
  stepmap(imap i :: PrimaryHasAdvancedLogTruncationPoint(b[i], live_quorum, view, opn))
}

lemma lemma_IfExecutorCaughtUpThenExecutorEventuallyExecutesItAndTellsPrimary(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int,
  first_step:int,
  executor_idx:int
  ) returns (
  step:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= prev_step <= first_step
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  requires executor_idx in asp.live_quorum
  requires sat(first_step, ReplicaCaughtUpTemporal(b, executor_idx, opn + 1))
  ensures  h.start_step + 1 <= step
  ensures  b[step].environment.time <= b[first_step].environment.time + asp.c.params.heartbeat_period + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp)
  ensures  var x := ReplicaSentHeartbeatToPrimaryReflectingOpnTemporal(b, executor_idx, h.view.proposer_id, opn + 1);
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, or(x, or(y, not(z))))
{
  var f := PaxosTimeMap(b);
  var w := ReplicaCaughtUpTemporal(b, executor_idx, opn + 1);
  var x := ReplicaSentHeartbeatToPrimaryReflectingOpnTemporal(b, executor_idx, h.view.proposer_id, opn + 1);
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var z := NoReplicaBeyondViewTemporal(b, h.view);

  lemma_ConstantsAllConsistent(b, asp.c, first_step);
  var nextHeartbeatTime := b[first_step].replicas[executor_idx].replica.nextHeartbeatTime;
  lemma_HeartbeatTimerNeverTooFarInFuture(b, asp, first_step, executor_idx);
  assert nextHeartbeatTime <= b[first_step].environment.time + asp.c.params.heartbeat_period + asp.max_clock_ambiguity;

  var P := and(w, NextHeartbeatTimeOfReplicaIsParticularValueTemporal(b, executor_idx, nextHeartbeatTime));
  var Q := or(x, or(y, not(z)));
  var Action := ReplicaSchedule(b, executor_idx)[9];
  forall i | first_step <= i
    ensures sat(i, TemporalWF1Req1(P, Q))
    ensures sat(i, TemporalWF1RealTimeDelayedReq2(P, Q, Action, nextHeartbeatTime + asp.max_clock_ambiguity, f))
  {
    if sat(i, P) && !sat(i, Q) && !sat(i+1, Q)
    {
      lemma_ConstantsAllConsistent(b, asp.c, i);
      lemma_ConstantsAllConsistent(b, asp.c, i+1);
      lemma_AssumptionsMakeValidTransition(b, asp.c, i);
      var s := b[i].replicas[executor_idx].replica;
      var s' := b[i+1].replicas[executor_idx].replica;
      var m := RslMessage_Heartbeat(s.proposer.election_state.current_view,
                                    s.constants.my_index in s.proposer.election_state.current_view_suspectors,
                                    s.executor.ops_complete);
      var p := LPacket(asp.c.config.replica_ids[h.view.proposer_id], asp.c.config.replica_ids[executor_idx], m);

      lemma_OpsCompleteMonotonic(b, asp.c, first_step, i+1, executor_idx);

      if !sat(i+1, P)
      {
        var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, executor_idx);
        assert LBroadcastToEveryone(asp.c.config, executor_idx, m, ExtractSentPacketsFromIos(ios));
        assert LIoOpSend(p) in ios;
        assert ReplicaSentHeartbeatToPrimaryReflectingOpn(b[i], executor_idx, h.view.proposer_id, opn + 1, p);
        assert sat(i+1, x);
        assert false;
      }
            
      if sat(i, nextafter(Action, nextHeartbeatTime + asp.max_clock_ambiguity, f))
      {
        assert SpecificClockReadingRslActionOccurs(b[i], b[i+1], LReplicaNextReadClockMaybeSendHeartbeat, executor_idx);
        var ios:seq<RslIo> :| && RslNextOneReplica(b[i], b[i+1], executor_idx, ios)
                              && SpontaneousIos(ios, 1)
                              && LReplicaNextReadClockMaybeSendHeartbeat(s, s', SpontaneousClock(ios), ExtractSentPacketsFromIos(ios));
        lemma_ClockAmbiguityLimitApplies(b, asp, i, executor_idx, ios[0]);
        assert ios[0].t >= b[i].environment.time - asp.max_clock_ambiguity == b[i+1].environment.time - asp.max_clock_ambiguity >= nextHeartbeatTime == s.nextHeartbeatTime;
        assert LBroadcastToEveryone(asp.c.config, executor_idx, m, ExtractSentPacketsFromIos(ios));
        assert LIoOpSend(p) in ios;
        assert ReplicaSentHeartbeatToPrimaryReflectingOpn(b[i], executor_idx, h.view.proposer_id, opn + 1, p);
        assert sat(i+1, x);
        assert false;
      }
    }
  }

  TemporalAlways(first_step, TemporalWF1Req1(P, Q));
  TemporalAlways(first_step, TemporalWF1RealTimeDelayedReq2(P, Q, Action, nextHeartbeatTime + asp.max_clock_ambiguity, f));
  lemma_ReplicaNextPerformsSubactionPeriodically(b, asp, executor_idx, 9);
  lemma_EstablishRequirementsForWF1RealTimeDelayed(b, asp, first_step, Action, TimeToPerformGenericAction(asp));
  step := TemporalWF1RealTimeDelayed(first_step, P, Q, Action, TimeToPerformGenericAction(asp), nextHeartbeatTime + asp.max_clock_ambiguity, f);
}

lemma lemma_IfLiveReplicasReadyForAnOperationThenExecutorEventuallyExecutesItAndTellsPrimary(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int,
  executor_idx:int
  ) returns (
  step:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= prev_step
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  requires executor_idx in asp.live_quorum
  ensures  h.start_step + 1 <= step
  ensures  var f := PaxosTimeMap(b);
           var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 4 + asp.c.params.heartbeat_period + TimeToPerformGenericAction(asp) * 5 + h.processing_bound * 2;
           var x := ReplicaSentHeartbeatToPrimaryReflectingOpnTemporal(b, executor_idx, h.view.proposer_id, opn + 1);
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, beforeabsolutetime(or(x, or(y, not(z))), t, f))
{
  var first_step := lemma_IfLiveReplicasReadyForAnOperationThenExecutorEventuallyExecutesIt(b, asp, h, opn, prev_step, executor_idx);
  var w := ReplicaCaughtUpTemporal(b, executor_idx, opn + 1);
  var x := ReplicaSentHeartbeatToPrimaryReflectingOpnTemporal(b, executor_idx, h.view.proposer_id, opn + 1);
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var z := NoReplicaBeyondViewTemporal(b, h.view);

  if sat(first_step, or(x, or(y, not(z))))
  {
    step := first_step;
    return;
  }

  if first_step < prev_step
  {
    lemma_OpsCompleteMonotonic(b, asp.c, first_step, prev_step, executor_idx);
    first_step := prev_step;
  }
  assert sat(first_step, w);

  step := lemma_IfExecutorCaughtUpThenExecutorEventuallyExecutesItAndTellsPrimary(b, asp, h, opn, prev_step, first_step, executor_idx);
}

lemma lemma_IfLiveReplicasReadyForAnOperationThenPrimaryFindsOutExecutorExecutedIt(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int,
  executor_idx:int
  ) returns (
  step:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= prev_step
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  requires executor_idx in asp.live_quorum
  ensures  h.start_step + 1 <= step
  ensures  var f := PaxosTimeMap(b);
           var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 4 + asp.c.params.heartbeat_period + TimeToPerformGenericAction(asp) * 5 + h.processing_bound * 3;
           var x := PrimaryKnowsReplicaHasOpsCompleteTemporal(b, executor_idx, h.view.proposer_id, opn + 1);
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, beforeabsolutetime(or(x, or(y, not(z))), t, f))
{
  var f := PaxosTimeMap(b);
  var w := ReplicaSentHeartbeatToPrimaryReflectingOpnTemporal(b, executor_idx, h.view.proposer_id, opn + 1);
  var x := PrimaryKnowsReplicaHasOpsCompleteTemporal(b, executor_idx, h.view.proposer_id, opn + 1);
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var z := NoReplicaBeyondViewTemporal(b, h.view);
  var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 4
           + asp.c.params.heartbeat_period + TimeToPerformGenericAction(asp) * 5 + h.processing_bound * 3;

  var first_step := lemma_IfLiveReplicasReadyForAnOperationThenExecutorEventuallyExecutesItAndTellsPrimary(b, asp, h, opn, prev_step, executor_idx);

  if sat(first_step, or(x, or(y, not(z))))
  {
    step := first_step;
    return;
  }

  assert !PrimaryKnowsReplicaHasOpsComplete(b[first_step], executor_idx, h.view.proposer_id, opn + 1);
  assert !AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmpty(b[first_step], asp.live_quorum, h.view, opn + 1);
  assert NoReplicaBeyondView(b[first_step], h.view);

  lemma_ConstantsAllConsistent(b, asp.c, first_step);
  assert sat(first_step, w);
  var p :| ReplicaSentHeartbeatToPrimaryReflectingOpn(b[first_step], executor_idx, h.view.proposer_id, opn + 1, p);
  lemma_AssumptionsMakeValidTransition(b, asp.c, first_step);
  assert b[first_step+1].environment.time == b[first_step].environment.time;

  var processing_step, ios := lemma_PacketSentToIndexProcessedByIt(b, asp, h.start_step, h.processing_bound, first_step, h.view.proposer_id, p);
  lemma_ConstantsAllConsistent(b, asp.c, processing_step);
  lemma_ConstantsAllConsistent(b, asp.c, processing_step+1);

  lemma_NextCheckpointedOperationAlwaysSizeOfReplicas(b, asp.c, processing_step, h.view.proposer_id);
  assert ReplicasDistinct(asp.c.config.replica_ids, executor_idx, GetReplicaIndex(p.src, asp.c.config));
  
  lemma_OpsCompleteMonotonic(b, asp.c, first_step, processing_step + 1, executor_idx);
  assert PrimaryKnowsReplicaHasOpsComplete(b[processing_step+1], executor_idx, h.view.proposer_id, opn + 1);
  step := processing_step + 1;
  assert f[step] <= t;
  assert sat(step, x);
}

lemma lemma_IfLiveReplicasReadyForAnOperationThenPrimaryAlwaysKnowsExecutorExecutedIt(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int,
  executor_idx:int
  ) returns (
  step:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= prev_step
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  requires executor_idx in asp.live_quorum
  ensures  h.start_step + 1 <= step
  ensures  var f := PaxosTimeMap(b);
           var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 4 + asp.c.params.heartbeat_period + TimeToPerformGenericAction(asp) * 5 + h.processing_bound * 3;
           var x := PrimaryKnowsReplicaHasOpsCompleteTemporal(b, executor_idx, h.view.proposer_id, opn + 1);
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, beforeabsolutetime(or(always(x), or(y, not(z))), t, f))
{
  var f := PaxosTimeMap(b);
  var x := PrimaryKnowsReplicaHasOpsCompleteTemporal(b, executor_idx, h.view.proposer_id, opn + 1);
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var z := NoReplicaBeyondViewTemporal(b, h.view);

  step := lemma_IfLiveReplicasReadyForAnOperationThenPrimaryFindsOutExecutorExecutedIt(b, asp, h, opn, prev_step, executor_idx);
  if sat(step, or(y, not(z)))
  {
    return;
  }
  assert sat(step, x);

  forall i | step <= i
    ensures sat(i, imply(x, next(x)))
  {
    if sat(i, x) && !sat(i+1, x)
    {
      lemma_ConstantsAllConsistent(b, asp.c, i);
      lemma_ConstantsAllConsistent(b, asp.c, i+1);
      lemma_AssumptionsMakeValidTransition(b, asp.c, i);
      lemma_OpsCompleteMonotonicOneStep(b, asp.c, i, executor_idx);
      lemma_NextCheckpointedOperationAlwaysSizeOfReplicas(b, asp.c, i, h.view.proposer_id);
      var s := b[i].replicas[h.view.proposer_id].replica.acceptor;
      var s' := b[i+1].replicas[h.view.proposer_id].replica.acceptor;
      assert s' != s;
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, h.view.proposer_id);
      var action_index := b[i].replicas[h.view.proposer_id].nextActionIndex;
      if action_index == 1 || action_index == 2 || action_index == 3 || action_index == 4 || action_index == 5
         || action_index == 6 || action_index == 7 || action_index == 8 || action_index == 9
      {
        assert s'.last_checkpointed_operation == s.last_checkpointed_operation;
        assert false;
      }
      else if ios[0].LIoOpTimeoutReceive? {
        assert s' == s;
        assert false;
      }
      else {
        assert ios[0].LIoOpReceive?;
        var msg := ios[0].r.msg;
        if msg.RslMessage_Invalid? || msg.RslMessage_Request? || msg.RslMessage_1a? || msg.RslMessage_1b?
           || msg.RslMessage_StartingPhase2? || msg.RslMessage_2a? || msg.RslMessage_2b? || msg.RslMessage_Reply?
           || msg.RslMessage_AppStateRequest? || msg.RslMessage_AppStateSupply? {
          assert s'.last_checkpointed_operation == s.last_checkpointed_operation;
          assert false;
        }
        else {
          assert msg.RslMessage_Heartbeat?;
          assert false;
        }
      }
    }
    reveal imply();
    reveal next();
  }
    
  TemporalInductionNext(step, x);
}

lemma lemma_IfLiveReplicasReadyForAnOperationThenPrimaryAlwaysKnowsEveryExecutorExecutedIt(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int
  ) returns (
  step:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= prev_step
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  ensures  h.start_step + 1 <= step
  ensures  var f := PaxosTimeMap(b);
           var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 4 + asp.c.params.heartbeat_period + TimeToPerformGenericAction(asp) * 5 + h.processing_bound * 3;
           var always_xs := always(andset(PrimaryKnowsEveryReplicaHasOpsCompleteTemporalSet(b, asp.live_quorum, h.view.proposer_id, opn + 1)));
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, beforeabsolutetime(or(always_xs, or(y, not(z))), t, f))
{
  var f := PaxosTimeMap(b);
  var xs := PrimaryKnowsEveryReplicaHasOpsCompleteTemporalSet(b, asp.live_quorum, h.view.proposer_id, opn + 1);
  var always_xs := always(andset(xs));
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var z := NoReplicaBeyondViewTemporal(b, h.view);

  var start_time := b[h.start_step + 1].environment.time;
  var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 4 + asp.c.params.heartbeat_period + TimeToPerformGenericAction(asp) * 5 + h.processing_bound * 3;
  lemma_TimeAdvancesBetween(b, asp, h.start_step + 1, prev_step);

  forall x | x in xs
    ensures sat(h.start_step + 1, eventuallywithin(or(always(x), or(y, not(z))), t - start_time, f))
  {
    var executor_idx :| executor_idx in asp.live_quorum && x == PrimaryKnowsReplicaHasOpsCompleteTemporal(b, executor_idx, h.view.proposer_id, opn + 1);
    var my_step := lemma_IfLiveReplicasReadyForAnOperationThenPrimaryAlwaysKnowsExecutorExecutedIt(b, asp, h, opn, prev_step, executor_idx);
    TemporalEventuallyWithin(h.start_step + 1, my_step, or(always(x), or(y, not(z))), t - start_time, f);
  }

  Lemma_EventuallyAlwaysWithinEachOrAlternativeImpliesEventuallyAlwaysWithinAllOrAlternative(h.start_step + 1, xs, or(y, not(z)), t - start_time, f);
  step := TemporalDeduceFromEventuallyWithin(h.start_step + 1, or(always_xs, or(y, not(z))), t - start_time, f);
}

lemma lemma_IfPrimaryTruncatesLogDueToCheckpointsWhileKnowingAllRepliesExecutedOpnThenItAdvancesLogTruncationPoint(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  i:int,
  ios:seq<RslIo>
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= i
  requires sat(i, andset(PrimaryKnowsEveryReplicaHasOpsCompleteTemporalSet(b, asp.live_quorum, h.view.proposer_id, opn + 1)))
  requires RslNextOneReplica(b[i], b[i+1], h.view.proposer_id, ios)
  requires 0 <= h.view.proposer_id < |b[i].replicas|
  requires 0 <= h.view.proposer_id < |b[i+1].replicas|
  requires LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(b[i].replicas[h.view.proposer_id].replica, b[i+1].replicas[h.view.proposer_id].replica, ExtractSentPacketsFromIos(ios))
  ensures  PrimaryHasAdvancedLogTruncationPoint(b[i+1], asp.live_quorum, h.view, opn + 1)
{
  var xs := PrimaryKnowsEveryReplicaHasOpsCompleteTemporalSet(b, asp.live_quorum, h.view.proposer_id, opn + 1);
  var s := b[i].replicas[h.view.proposer_id].replica;

  forall idx | idx in asp.live_quorum
    ensures ReplicaCaughtUp(b[i+1], idx, opn + 1)
    ensures 0 <= idx < |s.acceptor.last_checkpointed_operation|
    ensures s.acceptor.last_checkpointed_operation[idx] >= opn + 1
  {
    var x := PrimaryKnowsReplicaHasOpsCompleteTemporal(b, idx, h.view.proposer_id, opn + 1);
    assert x in xs;
    assert sat(i, x);
  }

  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i+1);

  var a := s.acceptor.last_checkpointed_operation;
  forall opn' | IsLogTruncationPointValid(opn', a, s.constants.all.config)
    ensures opn' >= opn + 1
  {
    if opn' < opn + 1
    {
      assert IsNthHighestValueInSequence(opn', a, LMinQuorumSize(asp.c.config));
      var matchfun := x => x > opn';
      var matches := SetOfIndicesOfMatchesInSeq(a, matchfun);
      forall idx | idx in asp.live_quorum
        ensures idx in matches
      {
        assert 0 <= idx < |a|;    // OBSERVE
        assert matchfun(a[idx]); // OBSERVE
      }
      assert asp.live_quorum <= matches;
      SubsetCardinality(asp.live_quorum, matches);
      assert |asp.live_quorum| <= |matches| == CountMatchesInSeq(a, matchfun) < LMinQuorumSize(asp.c.config);
      assert false;
    }
  }
    
  assert PrimaryHasAdvancedLogTruncationPoint(b[i+1], asp.live_quorum, h.view, opn + 1);
}

lemma lemma_IfLiveReplicasReadyForAnOperationThenEventuallyPrimaryAdvancesLogTruncationPointHelper(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int,
  first_step:int,
  i:int
  )
  requires imaptotal(b)
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= prev_step
  requires h.start_step + 1 <= first_step <= i
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  requires var ws := PrimaryKnowsEveryReplicaHasOpsCompleteTemporalSet(b, asp.live_quorum, h.view.proposer_id, opn + 1);
           var always_ws := always(andset(ws));
           var P := always_ws;
           var x := PrimaryHasAdvancedLogTruncationPointTemporal(b, asp.live_quorum, h.view, opn + 1);
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           var Q := or(x, or(y, not(z)));
           sat(first_step, P) && sat(i, P) && !sat(i, Q) && !sat(i+1, Q)
  requires sat(i, ReplicaSchedule(b, h.view.proposer_id)[4])
  ensures  false
{
  var ws := PrimaryKnowsEveryReplicaHasOpsCompleteTemporalSet(b, asp.live_quorum, h.view.proposer_id, opn + 1);
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i+1);
  Lemma_AlwaysImpliesLaterAlways(first_step, i+1, andset(ws));
  var s := b[i].replicas[h.view.proposer_id].replica;
  var s' := b[i+1].replicas[h.view.proposer_id].replica;
  lemma_ExpandReplicaSchedule(b, h.view.proposer_id, 4);
  assert sat(i, MakeRslActionTemporalFromSpontaneousReplicaFunction(b, LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints,
                                                                    h.view.proposer_id));
  assert SpecificSpontaneousRslActionOccurs(b[i], b[i+1], LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints, h.view.proposer_id);
  var ios:seq<RslIo> :| && RslNextOneReplica(b[i], b[i+1], h.view.proposer_id, ios)
                        && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', ExtractSentPacketsFromIos(ios));
  TemporalDeduceFromAlways(i, i, andset(ws));
  lemma_IfPrimaryTruncatesLogDueToCheckpointsWhileKnowingAllRepliesExecutedOpnThenItAdvancesLogTruncationPoint(b, asp, h, opn, i, ios);
}

lemma lemma_IfLiveReplicasReadyForAnOperationThenEventuallyPrimaryAdvancesLogTruncationPoint(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int
  ) returns (
  step:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= prev_step
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  ensures  h.start_step + 1 <= step
  ensures  var f := PaxosTimeMap(b);
           var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 4 + asp.c.params.heartbeat_period + TimeToPerformGenericAction(asp) * 6 + h.processing_bound * 3;
           var x := PrimaryHasAdvancedLogTruncationPointTemporal(b, asp.live_quorum, h.view, opn + 1);
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, beforeabsolutetime(or(x, or(y, not(z))), t, f))
{
  var f := PaxosTimeMap(b);
  var ws := PrimaryKnowsEveryReplicaHasOpsCompleteTemporalSet(b, asp.live_quorum, h.view.proposer_id, opn + 1);
  var always_ws := always(andset(ws));
    
  var x := PrimaryHasAdvancedLogTruncationPointTemporal(b, asp.live_quorum, h.view, opn + 1);
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var z := NoReplicaBeyondViewTemporal(b, h.view);
    
  var first_step := lemma_IfLiveReplicasReadyForAnOperationThenPrimaryAlwaysKnowsEveryExecutorExecutedIt(b, asp, h, opn, prev_step);
  if sat(first_step, or(y, not(z)))
  {
    step := first_step;
    return;
  }
  assert sat(first_step, always_ws);

  var P := always_ws;
  var Q := or(x, or(y, not(z)));
  forall i | first_step <= i
    ensures sat(i, TemporalWF1Req1(P, Q))
  {
    if sat(i, P) {
      Lemma_AlwaysImpliesLaterAlways(first_step, i+1, andset(ws));
      assert sat(i+1, P);
    }
  }
  var Action := ReplicaSchedule(b, h.view.proposer_id)[4];
  forall i | first_step <= i
    ensures sat(i, TemporalWF1Req2(P, Q, Action))
  {
    if sat(i, P) && sat(i, Action) && !sat(i, Q) && !sat(i+1, Q)
    {
      lemma_IfLiveReplicasReadyForAnOperationThenEventuallyPrimaryAdvancesLogTruncationPointHelper(b, asp, h, opn, prev_step,
                                                                                                   first_step, i);
    }
  }

  TemporalAlways(first_step, TemporalWF1Req1(P, Q));
  TemporalAlways(first_step, TemporalWF1Req2(P, Q, Action));
  lemma_ReplicaNextPerformsSubactionPeriodically(b, asp, h.view.proposer_id, 4);
  lemma_EstablishRequirementsForWF1RealTime(b, asp, first_step, Action, TimeToPerformGenericAction(asp));
  TemporalWF1RealTime(first_step, P, Q, Action, TimeToPerformGenericAction(asp), f);
  step := TemporalDeduceFromLeadsToWithin(first_step, first_step, P, Q, TimeToPerformGenericAction(asp), f);
}

lemma lemma_IfLiveReplicasReadyForAnOperationTheyllEventuallyBeReadyForNextOperation(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int
  ) returns (
  step:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= prev_step
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  ensures  h.start_step + 1 <= step
  ensures  var f := PaxosTimeMap(b);
           var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 4 + asp.c.params.heartbeat_period + TimeToPerformGenericAction(asp) * 6 + h.processing_bound * 3;
           var x := AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn + 1);
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, beforeabsolutetime(or(x, or(y, not(z))), t, f))
{
  var x := AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn + 1);
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var z := NoReplicaBeyondViewTemporal(b, h.view);

  var step1 := lemma_IfLiveReplicasReadyForAnOperationThenEventuallyPrimaryAdvancesLogTruncationPoint(b, asp, h, opn, prev_step);
  if sat(step1, or(y, not(z)))
  {
    step := step1;
    return;
  }
  lemma_ConstantsAllConsistent(b, asp.c, step1);
  assert forall idx :: idx in asp.live_quorum ==> ReplicaCaughtUp(b[step1], idx, opn + 1);
  assert b[step1].replicas[h.view.proposer_id].replica.acceptor.log_truncation_point >= opn + 1;

  var step2 := lemma_IfLiveReplicasReadyForAnOperationThenProposerEventuallyAdvancesNextOp(b, asp, h, opn, prev_step);
  if sat(step2, or(y, not(z)))
  {
    step := step2;
    return;
  }
  lemma_ConstantsAllConsistent(b, asp.c, step2);
  assert b[step2].replicas[h.view.proposer_id].replica.proposer.next_operation_number_to_propose >= opn + 1;

  if step1 < step2
  {
    step := step2;
    forall idx | idx in asp.live_quorum
      ensures ReplicaCaughtUp(b[step], idx, opn + 1)
    {
      lemma_OpsCompleteMonotonic(b, asp.c, step1, step2, idx);
    }
    lemma_LogTruncationPointMonotonic(b, asp.c, step1, step2, h.view.proposer_id);
    assert AllLiveReplicasReadyForNextOperation(b[step], asp.live_quorum, h.view, opn + 1);
  }
  else
  {
    step := step1;
    lemma_NextOperationNumberToProposeIncreasesInPhase2(b, asp, h, step2, step1);
    assert AllLiveReplicasReadyForNextOperation(b[step], asp.live_quorum, h.view, opn + 1);
  }
}

lemma lemma_EventuallyAllLiveReplicasReadyForCertainOperation(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber
  ) returns (
  step:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  ensures  h.start_step + 1 <= step
  ensures  b[step].environment.time <= b[h.start_step + 1].environment.time + TimeToBeginPhase2(asp, h.processing_bound) + (opn - h.log_truncation_point) * TimeToAdvanceOneOperation(asp, h.processing_bound)
  ensures  sat(step, or(AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn),
                        or(AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn),
                           not(NoReplicaBeyondViewTemporal(b, h.view)))))
  decreases opn - h.log_truncation_point
{
  if opn == h.log_truncation_point
  {
    step := lemma_EventuallyAllLiveReplicasReadyForFirstOperation(b, asp, h);
    return;
  }

  var prev_step := lemma_EventuallyAllLiveReplicasReadyForCertainOperation(b, asp, h, opn - 1);
  calc {
    b[prev_step].environment.time + TimeToAdvanceOneOperation(asp, h.processing_bound);
    <= b[h.start_step+1].environment.time + TimeToBeginPhase2(asp, h.processing_bound)
      + (opn - 1 - h.log_truncation_point) * TimeToAdvanceOneOperation(asp, h.processing_bound) + TimeToAdvanceOneOperation(asp, h.processing_bound);
    == b[h.start_step+1].environment.time + TimeToBeginPhase2(asp, h.processing_bound)
       + (opn - 1 - h.log_truncation_point) * TimeToAdvanceOneOperation(asp, h.processing_bound) + 1 * TimeToAdvanceOneOperation(asp, h.processing_bound);
    == { lemma_mul_is_distributive_add_other_way(TimeToAdvanceOneOperation(asp, h.processing_bound), opn - 1 - h.log_truncation_point, 1); }
        b[h.start_step+1].environment.time + TimeToBeginPhase2(asp, h.processing_bound) + (opn - h.log_truncation_point) * TimeToAdvanceOneOperation(asp, h.processing_bound);
  }

  if !sat(prev_step, AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn - 1))
  {
    step := prev_step;
    return;
  }

  step := lemma_IfLiveReplicasReadyForAnOperationTheyllEventuallyBeReadyForNextOperation(b, asp, h, opn - 1, prev_step);
}

}
