include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "StablePeriod.i.dfy"
include "NextOp.i.dfy"
include "Phase2a.i.dfy"
include "../CommonProof/Quorum.i.dfy"
include "../CommonProof/LearnerState.i.dfy"

module LivenessProof__Phase2b_i {

import opened LiveRSL__Configuration_i
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Executor_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__NextOp_i
import opened LivenessProof__Phase2a_i
import opened LivenessProof__Phase2Invariants_i
import opened LivenessProof__RealTime_i
import opened LivenessProof__RoundRobin_i
import opened LivenessProof__WF1_i
import opened CommonProof__Actions_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__LearnerState_i
import opened CommonProof__LogTruncationPoint_i
import opened CommonProof__Quorum_i
import opened Temporal__LeadsTo_i
import opened Temporal__Rules_i
import opened Temporal__Sets_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Temporal__WF1_i
import opened Environment_s
import opened Collections__Maps2_s
import opened Collections__Sets_i

lemma lemma_IfLiveReplicasReadyForAnOperationAndLearnerHas2bsFromAllLiveReplicasThenExecutorEventuallyHasDecisionWF1Req2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int,
  i:int,
  learner_idx:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= prev_step <= i
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  requires learner_idx in asp.live_quorum
  requires sat(i, always(andset(LearnerHas2bFromEveryAcceptorInViewTemporalSet(b, asp.live_quorum, learner_idx, h.view, opn))))
  requires !sat(i, ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn))
  requires !sat(i+1, ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn))
  requires !sat(i, AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1))
  requires !sat(i+1, AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1))
  requires sat(i, NoReplicaBeyondViewTemporal(b, h.view))
  requires sat(i+1, NoReplicaBeyondViewTemporal(b, h.view))
  requires sat(i, ReplicaSchedule(b, learner_idx)[5])
  ensures  false
{
  var w_once := andset(LearnerHas2bFromEveryAcceptorInViewTemporalSet(b, asp.live_quorum, learner_idx, h.view, opn));
  var x := ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn);
  var z := NoReplicaBeyondViewTemporal(b, h.view);

  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i+1);
  var s := b[i].replicas[learner_idx].replica;
  var s' := b[i+1].replicas[learner_idx].replica;
  assert SpecificSpontaneousRslActionOccurs(b[i], b[i+1], LReplicaNextSpontaneousMaybeMakeDecision, learner_idx);
  var ios:seq<RslIo> :| && RslNextOneReplica(b[i], b[i+1], learner_idx, ios)
                        && LReplicaNextSpontaneousMaybeMakeDecision(s, s', ExtractSentPacketsFromIos(ios));
  lemma_ConstantsAllConsistent(b, asp.c, prev_step);
  lemma_OpsCompleteMonotonic(b, asp.c, prev_step, i, learner_idx);
  assert s.executor.ops_complete == opn;
  assert s.executor.next_op_to_execute.OutstandingOpUnknown?;

  forall acceptor_idx | acceptor_idx in asp.live_quorum
    ensures opn in s.learner.unexecuted_learner_state
    ensures asp.c.config.replica_ids[acceptor_idx] in s.learner.unexecuted_learner_state[opn].received_2b_message_senders
  {
    var a := or(LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, h.view, opn), or(x, not(z)));
    assert a in LearnerHas2bFromEveryAcceptorInViewTemporalSet(b, asp.live_quorum, learner_idx, h.view, opn);
    TemporalDeduceFromAlways(i, i+1, w_once);
    assert sat(i+1, a);
  }

  assert {:split_here} true;

  assert opn in s.learner.unexecuted_learner_state;
  lemma_Received2bMessageSendersAlwaysValidReplicas(b, asp.c, i, learner_idx, opn);
  var acceptor_indices := lemma_GetIndicesFromNodes(s.learner.unexecuted_learner_state[opn].received_2b_message_senders, asp.c.config);

  forall acceptor_idx | acceptor_idx in asp.live_quorum
    ensures acceptor_idx in acceptor_indices
  {
    assert asp.c.config.replica_ids[acceptor_idx] in s.learner.unexecuted_learner_state[opn].received_2b_message_senders;
    assert ReplicasDistinct(asp.c.config.replica_ids, acceptor_idx, GetReplicaIndex(asp.c.config.replica_ids[acceptor_idx], asp.c.config));
  }

  assert {:split_here} true;
                
  SubsetCardinality(asp.live_quorum, acceptor_indices);
  assert |asp.live_quorum| <= |s.learner.unexecuted_learner_state[opn].received_2b_message_senders|;
  assert |s.learner.unexecuted_learner_state[opn].received_2b_message_senders| >= LMinQuorumSize(s.learner.constants.all.config);
  assert LExecutorGetDecision(s.executor, s'.executor, s.learner.max_ballot_seen, opn, s.learner.unexecuted_learner_state[opn].candidate_learned_value);

  assert sat(i+1, ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn));
  assert !sat(i+1, ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn));
  assert false;
}

lemma lemma_IfLiveReplicasReadyForAnOperationAndLearnerHas2bsFromAllLiveReplicasThenExecutorEventuallyHasDecision(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int,
  first_step:int,
  learner_idx:int
  ) returns (
  step:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= prev_step <= first_step
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  requires sat(first_step, always(andset(LearnerHas2bFromEveryAcceptorInViewTemporalSet(b, asp.live_quorum, learner_idx, h.view, opn))))
  requires learner_idx in asp.live_quorum
  ensures  first_step <= step
  ensures  b[step].environment.time <= b[first_step].environment.time + TimeToPerformGenericAction(asp)
  ensures  var x := ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn);
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, or(x, or(y, not(z))))
{
  var f := PaxosTimeMap(b);
  var w_once := andset(LearnerHas2bFromEveryAcceptorInViewTemporalSet(b, asp.live_quorum, learner_idx, h.view, opn));
  var w := always(w_once);
  var x := ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn);
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var z := NoReplicaBeyondViewTemporal(b, h.view);
  lemma_TimeAdvancesBetween(b, asp, h.start_step + 1, prev_step);

  var P := w;
  var Q := or(x, or(y, not(z)));
  var Action := ReplicaSchedule(b, learner_idx)[5];
  forall i | first_step <= i
    ensures sat(i, TemporalWF1Req1(P, Q))
    ensures sat(i, TemporalWF1Req2(P, Q, Action))
  {
    if sat(i, P) && !sat(i, Q) && !sat(i+1, Q)
    {
      Lemma_AlwaysImpliesLaterAlways(i, i+1, w_once);
      assert sat(i+1, P);

      if sat(i, Action)
      {
        lemma_IfLiveReplicasReadyForAnOperationAndLearnerHas2bsFromAllLiveReplicasThenExecutorEventuallyHasDecisionWF1Req2(b, asp, h, opn, prev_step, i, learner_idx);
        assert false;
      }
    }
  }

  TemporalAlways(first_step, TemporalWF1Req1(P, Q));
  TemporalAlways(first_step, TemporalWF1Req2(P, Q, Action));
  lemma_ReplicaNextPerformsSubactionPeriodically(b, asp, learner_idx, 5);
  lemma_EstablishRequirementsForWF1RealTime(b, asp, first_step, Action, TimeToPerformGenericAction(asp));
  TemporalWF1RealTime(first_step, P, Q, Action, TimeToPerformGenericAction(asp), f);
  step := TemporalDeduceFromLeadsToWithin(first_step, first_step, P, Q, TimeToPerformGenericAction(asp), f);
}

lemma lemma_IfLiveReplicasReadyForAnOperationThenExecutorEventuallyHasDecision(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int,
  learner_idx:int
  ) returns (
  step:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= prev_step
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  requires learner_idx in asp.live_quorum
  ensures  h.start_step + 1 <= step
  ensures  var f := PaxosTimeMap(b);
           var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp) * 3 + h.processing_bound * 2;
           var x := ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn);
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, beforeabsolutetime(or(x, or(y, not(z))), t, f))
{
  var w_once := andset(LearnerHas2bFromEveryAcceptorInViewTemporalSet(b, asp.live_quorum, learner_idx, h.view, opn));
  var w := always(w_once);
  var x := ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn);
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var z := NoReplicaBeyondViewTemporal(b, h.view);

  var first_step := lemma_IfLiveReplicasReadyForAnOperationThenLearnerEventuallyLearnsItFromAll(b, asp, h, opn, prev_step, learner_idx);
  if sat(first_step, or(x, or(y, not(z))))
  {
    step := first_step;
    return;
  }

  if first_step < prev_step
  {
    Lemma_AlwaysImpliesLaterAlways(first_step, prev_step, w_once);
    first_step := prev_step;
  }
  assert sat(first_step, w);

  step := lemma_IfLiveReplicasReadyForAnOperationAndLearnerHas2bsFromAllLiveReplicasThenExecutorEventuallyHasDecision(b, asp, h, opn, prev_step, first_step, learner_idx);
}

lemma lemma_ExecutorHasLearnedDecisionAboutOpStable(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  j:int,
  idx:int,
  opn:OperationNumber
  )
  requires IsValidBehaviorPrefix(b, c, j)
  requires 0 <= i <= j
  requires 0 <= idx < |b[i].replicas|
  requires sat(i, ExecutorHasLearnedDecisionAboutOpTemporal(b, idx, opn))
  ensures  sat(j, ExecutorHasLearnedDecisionAboutOpTemporal(b, idx, opn))
  decreases j - i
{
  if j == i
  {
    return;
  }

  lemma_ExecutorHasLearnedDecisionAboutOpStable(b, c, i, j-1, idx, opn);
  if !sat(j, ExecutorHasLearnedDecisionAboutOpTemporal(b, idx, opn))
  {
    lemma_ConstantsAllConsistent(b, c, j-1);
    lemma_ConstantsAllConsistent(b, c, j);
    var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, j-1, idx);
    assert false;
  }
}

lemma lemma_IfLiveReplicasReadyForAnOperationThenExecutorEventuallyExecutesIt(
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
           var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp) * 4 + h.processing_bound * 2;
           var x := ReplicaCaughtUpTemporal(b, executor_idx, opn + 1);
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, beforeabsolutetime(or(x, or(y, not(z))), t, f))
{
  var f := PaxosTimeMap(b);
  var w := ExecutorHasLearnedDecisionAboutOpTemporal(b, executor_idx, opn);
  var x := ReplicaCaughtUpTemporal(b, executor_idx, opn + 1);
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var z := NoReplicaBeyondViewTemporal(b, h.view);
  var first_step := lemma_IfLiveReplicasReadyForAnOperationThenExecutorEventuallyHasDecision(b, asp, h, opn, prev_step, executor_idx);

  if sat(first_step, or(x, or(y, not(z))))
  {
    step := first_step;
    return;
  }

  if first_step < prev_step
  {
    lemma_ExecutorHasLearnedDecisionAboutOpStable(b, asp.c, first_step, prev_step, executor_idx, opn);
    first_step := prev_step;
  }
  assert sat(first_step, w);

  var P := w;
  var Q := or(x, or(y, not(z)));
  var Action := ReplicaSchedule(b, executor_idx)[6];
  forall i | first_step <= i
    ensures sat(i, TemporalWF1Req1(P, Q))
    ensures sat(i, TemporalWF1Req2(P, Q, Action))
  {
    if sat(i, P) && !sat(i, Q) && !sat(i+1, Q)
    {
      lemma_ExecutorHasLearnedDecisionAboutOpStable(b, asp.c, first_step, i+1, executor_idx, opn);
      assert sat(i+1, P);
      
      if sat(i, Action)
      {
        lemma_ConstantsAllConsistent(b, asp.c, i);
        lemma_ConstantsAllConsistent(b, asp.c, i+1);
        var s := b[i].replicas[executor_idx].replica;
        var s' := b[i+1].replicas[executor_idx].replica;
        assert SpecificSpontaneousRslActionOccurs(b[i], b[i+1], LReplicaNextSpontaneousMaybeExecute, executor_idx);
        var ios:seq<RslIo> :| && RslNextOneReplica(b[i], b[i+1], executor_idx, ios)
                              && LReplicaNextSpontaneousMaybeExecute(s, s', ExtractSentPacketsFromIos(ios));
        lemma_OverflowProtectionNotUsedForReplica(b, asp, i, executor_idx);
        assert LExecutorExecute(s.executor, s'.executor, ExtractSentPacketsFromIos(ios));
        assert false;
      }
    }
  }

  TemporalAlways(first_step, TemporalWF1Req1(P, Q));
  TemporalAlways(first_step, TemporalWF1Req2(P, Q, Action));
  lemma_ReplicaNextPerformsSubactionPeriodically(b, asp, executor_idx, 6);
  lemma_EstablishRequirementsForWF1RealTime(b, asp, first_step, Action, TimeToPerformGenericAction(asp));
  TemporalWF1RealTime(first_step, P, Q, Action, TimeToPerformGenericAction(asp), f);
  step := TemporalDeduceFromLeadsToWithin(first_step, first_step, P, Q, TimeToPerformGenericAction(asp), f);
}

}
