include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "StablePeriod.i.dfy"
include "NextOp.i.dfy"

module LivenessProof__Phase2a_i {

import opened LiveRSL__Broadcast_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Learner_i
import opened LiveRSL__Message_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__NextOp_i
import opened LivenessProof__PacketHandling_i
import opened LivenessProof__Phase2Invariants_i
import opened LivenessProof__RealTime_i
import opened LivenessProof__RoundRobin_i
import opened LivenessProof__StablePeriod_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened Temporal__Induction_i
import opened Temporal__Rules_i
import opened Temporal__Sets_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Temporal__Time_i
import opened Environment_s
import opened Collections__Maps2_s
import opened Common__UpperBound_s

predicate ProposerSends2asForOperation(
  ps:RslState,
  ps':RslState,
  idx:int,
  opn:OperationNumber,
  ios:seq<RslIo>
  )
{
  && 0 <= idx < |ps.replicas|
  && 0 <= idx < |ps'.replicas|
  && ps.replicas[idx].replica.proposer.next_operation_number_to_propose == opn
  && ps'.replicas[idx].replica.proposer.next_operation_number_to_propose == opn + 1
  && RslNextOneReplica(ps, ps', idx, ios)
  && SpontaneousIos(ios, 1)
  && LProposerMaybeNominateValueAndSend2a(ps.replicas[idx].replica.proposer,
                                         ps'.replicas[idx].replica.proposer,
                                         ios[0].t,
                                         ps.replicas[idx].replica.acceptor.log_truncation_point,
                                         ExtractSentPacketsFromIos(ios))
}

function{:opaque} ProposerSends2asForOperationTemporal(
  b:Behavior<RslState>,
  idx:int,
  opn:OperationNumber
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, ProposerSends2asForOperationTemporal(b, idx, opn))} ::
             sat(i, ProposerSends2asForOperationTemporal(b, idx, opn)) <==>
             exists ios {:trigger ProposerSends2asForOperation(b[i], b[nextstep(i)], idx, opn, ios)} ::
                    ProposerSends2asForOperation(b[i], b[nextstep(i)], idx, opn, ios)
{
  stepmap(imap i :: exists ios {:trigger ProposerSends2asForOperation(b[i], b[nextstep(i)], idx, opn, ios)} ::
                         ProposerSends2asForOperation(b[i], b[nextstep(i)], idx, opn, ios))
}

predicate LearnerHas2bFromAcceptorInView(
  ps:RslState,
  acceptor_idx:int,
  learner_idx:int,
  view:Ballot,
  opn:OperationNumber
  )
{
  && 0 <= acceptor_idx < |ps.constants.config.replica_ids|
  && 0 <= learner_idx < |ps.replicas|
  && var s := ps.replicas[learner_idx].replica.learner;
    && s.max_ballot_seen == view
    && opn in s.unexecuted_learner_state
    && ps.constants.config.replica_ids[acceptor_idx] in s.unexecuted_learner_state[opn].received_2b_message_senders
}

function{:opaque} LearnerHas2bFromAcceptorInViewTemporal(
  b:Behavior<RslState>,
  acceptor_idx:int,
  learner_idx:int,
  view:Ballot,
  opn:OperationNumber
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, view, opn))} ::
             sat(i, LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, view, opn))
             == LearnerHas2bFromAcceptorInView(b[i], acceptor_idx, learner_idx, view, opn);
{
  stepmap(imap i :: LearnerHas2bFromAcceptorInView(b[i], acceptor_idx, learner_idx, view, opn))
}

predicate ExecutorHasLearnedDecisionAboutOp(
  ps:RslState,
  idx:int,
  opn:OperationNumber
  )
{
  && 0 <= idx < |ps.replicas|
  && var s := ps.replicas[idx].replica.executor;
    s.ops_complete > opn || (s.ops_complete == opn && s.next_op_to_execute.OutstandingOpKnown?)
}

function{:opaque} ExecutorHasLearnedDecisionAboutOpTemporal(
  b:Behavior<RslState>,
  idx:int,
  opn:OperationNumber
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, ExecutorHasLearnedDecisionAboutOpTemporal(b, idx, opn))} ::
             sat(i, ExecutorHasLearnedDecisionAboutOpTemporal(b, idx, opn)) == ExecutorHasLearnedDecisionAboutOp(b[i], idx, opn)
{
  stepmap(imap i :: ExecutorHasLearnedDecisionAboutOp(b[i], idx, opn))
}

function{:opaque} LearnerHas2bFromEveryAcceptorInViewTemporalSet(
  b:Behavior<RslState>,
  live_quorum:set<int>,
  learner_idx:int,
  view:Ballot,
  opn:OperationNumber
  ):set<temporal>
  requires imaptotal(b)
  ensures forall acceptor_idx :: acceptor_idx in live_quorum ==>
            or(LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, view, opn),
               or(ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn),
                  not(NoReplicaBeyondViewTemporal(b, view))))
                in LearnerHas2bFromEveryAcceptorInViewTemporalSet(b, live_quorum, learner_idx, view, opn)
  ensures forall x :: x in LearnerHas2bFromEveryAcceptorInViewTemporalSet(b, live_quorum, learner_idx, view, opn) ==>
                exists acceptor_idx :: && acceptor_idx in live_quorum
                                 && x == or(LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, view, opn),
                                           or(ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn),
                                              not(NoReplicaBeyondViewTemporal(b, view))))
{
  set acceptor_idx | acceptor_idx in live_quorum :: or(LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, view, opn),
                                                     or(ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn),
                                                        not(NoReplicaBeyondViewTemporal(b, view))))
}

lemma lemma_IfNextOperationBeyondThenProposerSent2as(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  i:int
  ) returns (
  step:int,
  ios:seq<RslIo>
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires h.start_step + 1 <= i
  requires opn >= h.log_truncation_point
  requires 0 <= h.view.proposer_id < |b[i].replicas|
  requires b[i].replicas[h.view.proposer_id].replica.proposer.next_operation_number_to_propose > opn
  requires NoReplicaBeyondView(b[i], h.view)
  ensures  h.start_step + 1 <= step < i
  ensures  ProposerSends2asForOperation(b[step], b[step+1], h.view.proposer_id, opn, ios)
{
  var idx := h.view.proposer_id;
  var next_step := earliestStepBetween(h.start_step + 1, i, ProposerExceedsCertainNextOpTemporal(b, idx, opn));
  step := next_step - 1;
  assert h.start_step + 1 <= step < next_step <= i;
  assert !sat(step, ProposerExceedsCertainNextOpTemporal(b, idx, opn));

  lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, step, i, h.view);
  lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, step+1, i, h.view);
  lemma_ProposerStaysInState2InPhase2(b, asp, h, step);
  lemma_ProposerStaysInState2InPhase2(b, asp, h, step+1);
    
  ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, step, idx);

  lemma_ConstantsAllConsistent(b, asp.c, step);
  lemma_ConstantsAllConsistent(b, asp.c, step+1);
}

lemma lemma_IfLiveReplicasReadyForAnOperationThenLearnerEventuallyLearnsItLastStep(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int,
  acceptor_idx:int,
  learner_idx:int,
  v:RequestBatch,
  p:RslPacket,
  third_step:int,
  ios:seq<RslIo>
  ) returns (
  step:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= prev_step
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  requires acceptor_idx in asp.live_quorum
  requires learner_idx in asp.live_quorum
  requires p.src == asp.c.config.replica_ids[acceptor_idx]
  requires p.msg == RslMessage_2b(h.view, opn, v)
  requires PacketProcessedViaIos(b[third_step], b[third_step+1], p, learner_idx, ios)
  requires b[third_step+1].environment.time <= b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp) * 2 + h.processing_bound * 2
  requires h.start_step + 1 <= third_step
  ensures  h.start_step + 1 <= step
  ensures  var f := PaxosTimeMap(b);
           var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp) * 2 + h.processing_bound * 2;
           var w := LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, h.view, opn);
           var x := ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn);
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, beforeabsolutetime(or(w, or(x, or(y, not(z)))), t, f))
{
  var f := PaxosTimeMap(b);
  var w := LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, h.view, opn);
  var x := ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn);
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var z := NoReplicaBeyondViewTemporal(b, h.view);

  if sat(third_step, or(x, not(z)))
  {
    step := third_step;
    lemma_TimeAdvancesBetween(b, asp, third_step, third_step + 1);
    return;
  }

  lemma_ConstantsAllConsistent(b, asp.c, third_step);
  var s3 := b[third_step].replicas[learner_idx].replica;

  lemma_ConstantsAllConsistent(b, asp.c, third_step+1);
  var s3' := b[third_step+1].replicas[learner_idx].replica;
  assert LReplicaNextProcessPacket(s3, s3', ios);
  assert LReplicaNextProcess2b(s3, s3', p, ExtractSentPacketsFromIos(ios));
  var op_learnable := s3.executor.ops_complete < opn || (s3.executor.ops_complete == opn && s3.executor.next_op_to_execute.OutstandingOpUnknown?);
  assert op_learnable;
  assert LLearnerProcess2b(s3.learner, s3'.learner, p);
  lemma_LearnerMaxBallotSeenNeverExceedsViewDuringPhase2(b, asp, h, third_step, learner_idx);
  assert p.src in s3.learner.constants.all.config.replica_ids;
  assert !BalLt(p.msg.bal_2b, s3.learner.max_ballot_seen);
    
  assert s3'.learner.max_ballot_seen == h.view;
  assert opn in s3'.learner.unexecuted_learner_state;
  assert p.src == asp.c.config.replica_ids[acceptor_idx];
  assert p.src in s3'.learner.unexecuted_learner_state[opn].received_2b_message_senders;

  step := third_step + 1;
  assert LearnerHas2bFromAcceptorInView(b[step], acceptor_idx, learner_idx, h.view, opn);
}

lemma lemma_IfLiveReplicasReadyForAnOperationThenLearnerEventuallyLearnsItSecondStep(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int,
  acceptor_idx:int,
  learner_idx:int,
  v:RequestBatch,
  p:RslPacket,
  second_step:int,
  ios:seq<RslIo>
  ) returns (
  step:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= prev_step
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  requires acceptor_idx in asp.live_quorum
  requires learner_idx in asp.live_quorum
  requires p.src == asp.c.config.replica_ids[h.view.proposer_id]
  requires p.msg == RslMessage_2a(h.view, opn, v)
  requires PacketProcessedViaIos(b[second_step], b[second_step+1], p, acceptor_idx, ios)
  requires b[second_step+1].environment.time <= b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp) * 2 + h.processing_bound
  requires h.start_step + 1 <= second_step
  requires LeqUpperBound(opn, asp.c.params.max_integer_val)
  ensures  h.start_step + 1 <= step
  ensures  var f := PaxosTimeMap(b);
           var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp) * 2 + h.processing_bound * 2;
           var w := LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, h.view, opn);
           var x := ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn);
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, beforeabsolutetime(or(w, or(x, or(y, not(z)))), t, f))
{
  var f := PaxosTimeMap(b);
  var w := LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, h.view, opn);
  var x := ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn);
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var z := NoReplicaBeyondViewTemporal(b, h.view);

  if sat(second_step, not(z))
  {
    step := second_step;
    lemma_TimeAdvancesBetween(b, asp, second_step, second_step+1);
    return;
  }

  lemma_ConstantsAllConsistent(b, asp.c, second_step);
  lemma_ConstantsAllConsistent(b, asp.c, second_step+1);
  var s2 := b[second_step].replicas[acceptor_idx].replica;
  var s2' := b[second_step+1].replicas[acceptor_idx].replica;

  lemma_MaxBalNeverExceedsViewDuringPhase2(b, asp, h, second_step, acceptor_idx);
  assert LBroadcastToEveryone(asp.c.config, acceptor_idx, RslMessage_2b(h.view, opn, v), ExtractSentPacketsFromIos(ios));
  var p2 := LPacket(asp.c.config.replica_ids[learner_idx], asp.c.config.replica_ids[acceptor_idx], RslMessage_2b(h.view, opn, v));
  assert p2 in ExtractSentPacketsFromIos(ios);

  var third_step, ios3 := lemma_PacketSentToIndexProcessedByIt(b, asp, h.start_step, h.processing_bound, second_step, learner_idx, p2);
  assert f[third_step+1] <= f[prev_step] + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp) * 2 + h.processing_bound * 2;
  step := lemma_IfLiveReplicasReadyForAnOperationThenLearnerEventuallyLearnsItLastStep(b, asp, h, opn, prev_step, acceptor_idx, learner_idx, v, p2, third_step, ios3);
}

lemma lemma_IfLiveReplicasReadyForAnOperationThenLearnerEventuallyLearnsIt(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int,
  acceptor_idx:int,
  learner_idx:int
  ) returns (
  step:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= prev_step
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  requires acceptor_idx in asp.live_quorum
  requires learner_idx in asp.live_quorum
  ensures  h.start_step + 1 <= step
  ensures  var f := PaxosTimeMap(b);
           var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp) * 2 + h.processing_bound * 2;
           var w := LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, h.view, opn);
           var x := ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn);
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, beforeabsolutetime(or(w, or(x, or(y, not(z)))), t, f))
{
  var f := PaxosTimeMap(b);
  var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp) * 2 + h.processing_bound * 2;
  var w := LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, h.view, opn);
  var x := ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn);
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var z := NoReplicaBeyondViewTemporal(b, h.view);

  var later_step := lemma_IfLiveReplicasReadyForAnOperationThenProposerEventuallyAdvancesNextOp(b, asp, h, opn, prev_step);
  assert f[later_step] <= f[prev_step] + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp) * 2;
  lemma_ConstantsAllConsistent(b, asp.c, later_step);
  if sat(later_step, or(y, not(z)))
  {
    step := later_step;
    return;
  }

  var first_step, ios := lemma_IfNextOperationBeyondThenProposerSent2as(b, asp, h, opn, later_step);
  lemma_TimeAdvancesBetween(b, asp, first_step + 1, later_step);
  if sat(first_step, not(z))
  {
    step := first_step;
    lemma_TimeAdvancesBetween(b, asp, step, first_step + 1);
    return;
  }

  assert f[first_step+1] <= f[prev_step] + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp) * 2;

  lemma_ConstantsAllConsistent(b, asp.c, first_step);
  var s1 := b[first_step].replicas[h.view.proposer_id].replica;
  var v :| LBroadcastToEveryone(asp.c.config, h.view.proposer_id, RslMessage_2a(s1.proposer.max_ballot_i_sent_1a, opn, v), ExtractSentPacketsFromIos(ios));
  lemma_ProposerStaysInState2InPhase2(b, asp, h, first_step);
  assert s1.proposer.max_ballot_i_sent_1a == h.view;

  var p := LPacket(asp.c.config.replica_ids[acceptor_idx], asp.c.config.replica_ids[h.view.proposer_id], RslMessage_2a(h.view, opn, v));
  assert p in ExtractSentPacketsFromIos(ios);

  var second_step, ios2 := lemma_PacketSentToIndexProcessedByIt(b, asp, h.start_step, h.processing_bound, first_step, acceptor_idx, p);
  assert f[second_step+1] <= f[prev_step] + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp) * 2 + h.processing_bound;
  step := lemma_IfLiveReplicasReadyForAnOperationThenLearnerEventuallyLearnsItSecondStep(b, asp, h, opn, prev_step, acceptor_idx, learner_idx, v, p, second_step, ios2);
}

lemma lemma_IfLearnerHas2bFromAcceptorItKeepsItHelper(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  acceptor_idx:int,
  learner_idx:int,
  j:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires h.start_step + 1 <= j
  requires 0 <= learner_idx < |asp.c.config.replica_ids|
  requires ExecutorHasLearnedDecisionAboutOp(b[j], learner_idx, opn)
  requires !LearnerHas2bFromAcceptorInView(b[j+1], acceptor_idx, learner_idx, h.view, opn)
  requires !ExecutorHasLearnedDecisionAboutOp(b[j+1], learner_idx, opn)
  requires NoReplicaBeyondView(b[j+1], h.view)
  ensures  false
{
  lemma_ConstantsAllConsistent(b, asp.c, j);
  lemma_ConstantsAllConsistent(b, asp.c, j+1);
  lemma_AssumptionsMakeValidTransition(b, asp.c, j);
  var s := b[j].replicas[learner_idx].replica;
  var s' := b[j+1].replicas[learner_idx].replica;

  assert NoReplicaBeyondView(b[j+1], h.view);
  lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, j, j+1, h.view);
  assert NoReplicaBeyondView(b[j], h.view);
  lemma_ProposerStaysInState2InPhase2(b, asp, h, j);
  lemma_ProposerStaysInState2InPhase2(b, asp, h, j+1);
  assert s'.executor.ops_complete != s.executor.ops_complete || s'.executor.next_op_to_execute != s.executor.next_op_to_execute;
  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, j, learner_idx);
}

lemma lemma_IfLearnerHas2bFromAcceptorItKeepsItHelper2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  acceptor_idx:int,
  learner_idx:int,
  j:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires h.start_step + 1 <= j
  requires 0 <= learner_idx < |asp.c.config.replica_ids|
  requires !ExecutorHasLearnedDecisionAboutOp(b[j], learner_idx, opn)
  requires LearnerHas2bFromAcceptorInView(b[j], acceptor_idx, learner_idx, h.view, opn)
  requires !LearnerHas2bFromAcceptorInView(b[j+1], acceptor_idx, learner_idx, h.view, opn)
  requires !ExecutorHasLearnedDecisionAboutOp(b[j+1], learner_idx, opn)
  requires NoReplicaBeyondView(b[j+1], h.view)
  ensures  false
{
  lemma_ConstantsAllConsistent(b, asp.c, j);
  lemma_ConstantsAllConsistent(b, asp.c, j+1);
  lemma_AssumptionsMakeValidTransition(b, asp.c, j);
  var s := b[j].replicas[learner_idx].replica;
  var s' := b[j+1].replicas[learner_idx].replica;

  assert NoReplicaBeyondView(b[j+1], h.view);
  lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, j, j+1, h.view);
  assert NoReplicaBeyondView(b[j], h.view);
  lemma_ProposerStaysInState2InPhase2(b, asp, h, j);
  lemma_ProposerStaysInState2InPhase2(b, asp, h, j+1);
  lemma_LearnerMaxBallotSeenNeverExceedsViewDuringPhase2(b, asp, h, j, learner_idx);
  lemma_LearnerMaxBallotSeenNeverExceedsViewDuringPhase2(b, asp, h, j+1, learner_idx);
  assert s'.learner.max_ballot_seen != s.learner.max_ballot_seen || s'.learner.unexecuted_learner_state != s.learner.unexecuted_learner_state;
  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, j, learner_idx);
  assert BalLeq(s.learner.max_ballot_seen, s'.learner.max_ballot_seen);
  assert s'.learner.max_ballot_seen == s.learner.max_ballot_seen;
}

lemma lemma_IfLearnerHas2bFromAcceptorItKeepsIt(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  acceptor_idx:int,
  learner_idx:int,
  i:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires h.start_step + 1 <= i
  requires 0 <= learner_idx < |asp.c.config.replica_ids|
  requires sat(i, or(LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, h.view, opn),
                     or(ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn),
                        not(NoReplicaBeyondViewTemporal(b, h.view)))))
  ensures  sat(i, always(or(LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, h.view, opn),
                            or(ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn),
                               not(NoReplicaBeyondViewTemporal(b, h.view))))));
{
  var x := or(LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, h.view, opn),
              or(ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn),
                 not(NoReplicaBeyondViewTemporal(b, h.view))));

  forall j | i <= j
    ensures sat(j, imply(x, next(x)))
  {
    if sat(j, x) && !sat(j+1, x)
    {
      if sat(j, ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn))
      {
        lemma_IfLearnerHas2bFromAcceptorItKeepsItHelper(b, asp, h, opn, acceptor_idx, learner_idx, j);
      }
      else if sat(j, LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, h.view, opn))
      {
        lemma_IfLearnerHas2bFromAcceptorItKeepsItHelper2(b, asp, h, opn, acceptor_idx, learner_idx, j);
      }
      else
      {
        assert NoReplicaBeyondView(b[j+1], h.view);
        lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, j, j+1, h.view);
        assert NoReplicaBeyondView(b[j], h.view);
        assert false;
      }
    }
    reveal imply();
    reveal next();
  }
  TemporalInductionNext(i, x);
}

lemma lemma_IfLiveReplicasReadyForAnOperationThenLearnerEventuallyLearnsItFromAll(
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
           var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp) * 2 + h.processing_bound * 2;
           var x := always(andset(LearnerHas2bFromEveryAcceptorInViewTemporalSet(b, asp.live_quorum, learner_idx, h.view, opn)));
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           sat(step, beforeabsolutetime(or(x, y), t, f))
{
  var t := b[prev_step].environment.time - b[h.start_step + 1].environment.time
           + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp) * 2 + h.processing_bound * 2;
  var f := PaxosTimeMap(b);
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var x2 := ExecutorHasLearnedDecisionAboutOpTemporal(b, learner_idx, opn);
  var z := NoReplicaBeyondViewTemporal(b, h.view);
  lemma_TimeAdvancesBetween(b, asp, h.start_step + 1, prev_step);

  if sat(h.start_step + 1, eventuallywithin(y, t, f))
  {
    step := TemporalDeduceFromEventual(h.start_step + 1, beforeabsolutetime(y, f[h.start_step + 1] + t, f));
    return;
  }
    
  forall acceptor_idx | acceptor_idx in asp.live_quorum
    ensures var a := or(LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, h.view, opn), or(x2, not(z)));
            sat(h.start_step + 1, eventuallywithin(always(a), t, f))
  {
    var learn_step := lemma_IfLiveReplicasReadyForAnOperationThenLearnerEventuallyLearnsIt(b, asp, h, opn, prev_step, acceptor_idx, learner_idx);
    assert f[learn_step] <= f[h.start_step+1] + t;
    var x1 := LearnerHas2bFromAcceptorInViewTemporal(b, acceptor_idx, learner_idx, h.view, opn);
    var a := or(x1, or(x2, not(z)));
    assert sat(learn_step, or(x1, or(x2, or(y, not(z)))));
    if sat(learn_step, y)
    {
      TemporalEventually(h.start_step + 1, learn_step, beforeabsolutetime(y, f[h.start_step + 1] + t, f));
      assert sat(h.start_step + 1, eventuallywithin(y, t, f));
      assert false;
    }
    else
    {
      lemma_IfLearnerHas2bFromAcceptorItKeepsIt(b, asp, h, opn, acceptor_idx, learner_idx, learn_step);
      TemporalEventually(h.start_step + 1, learn_step, beforeabsolutetime(always(a), f[h.start_step + 1] + t, f));
      assert sat(h.start_step + 1, eventuallywithin(always(a), t, f));
    }
  }

  var xs := LearnerHas2bFromEveryAcceptorInViewTemporalSet(b, asp.live_quorum, learner_idx, h.view, opn);
  Lemma_EventuallyAlwaysWithinEachImpliesEventuallyAlwaysWithinAll(h.start_step + 1, xs, t, f);
  step := TemporalDeduceFromEventuallyWithin(h.start_step + 1, always(andset(xs)), t, f);
}

}
