include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "StablePeriod.i.dfy"
include "Catchup.i.dfy"
include "WF1.i.dfy"

module LivenessProof__NextOp_i {

import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Catchup_i
import opened LivenessProof__Environment_i
import opened LivenessProof__GenericInvariants_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__Phase2Invariants_i
import opened LivenessProof__RoundRobin_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__WF1_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened CommonProof__LogTruncationPoint_i
import opened Temporal__Rules_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Temporal__WF1_i
import opened Environment_s
import opened Collections__Maps2_s

predicate AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmpty(
  ps:RslState,
  live_quorum:set<int>,
  view:Ballot,
  opn:OperationNumber
  )
{
  && 0 <= view.proposer_id < |ps.replicas|
  && var s := ps.replicas[view.proposer_id].replica.proposer;
    && |s.request_queue| == 0
    && AllLiveReplicasReadyForNextOperation(ps, live_quorum, view, s.next_operation_number_to_propose)
    && s.next_operation_number_to_propose <= opn
}

function{:opaque} AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(
  b:Behavior<RslState>,
  live_quorum:set<int>,
  view:Ballot,
  opn:OperationNumber
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, live_quorum, view, opn))} ::
             sat(i, AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, live_quorum, view, opn)) ==
             AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmpty(b[i], live_quorum, view, opn)
{
  stepmap(imap i :: AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmpty(b[i], live_quorum, view, opn))
}

predicate ProposerStartsBatchTimer(
  ps:RslState,
  idx:int
  )
{
  && 0 <= idx < |ps.replicas|
  && ps.replicas[idx].replica.proposer.incomplete_batch_timer.IncompleteBatchTimerOn?
}

function{:opaque} ProposerStartsBatchTimerTemporal(
  b:Behavior<RslState>,
  idx:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, ProposerStartsBatchTimerTemporal(b, idx))} ::
             sat(i, ProposerStartsBatchTimerTemporal(b, idx)) ==
             ProposerStartsBatchTimer(b[i], idx)
{
  stepmap(imap i :: ProposerStartsBatchTimer(b[i], idx))
}

predicate ProposerExceedsCertainNextOp(
  ps:RslState,
  idx:int,
  opn:int
  )
{
  && 0 <= idx < |ps.replicas|
  && ps.replicas[idx].replica.proposer.next_operation_number_to_propose > opn
}

function{:opaque} ProposerExceedsCertainNextOpTemporal(
  b:Behavior<RslState>,
  idx:int,
  opn:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, ProposerExceedsCertainNextOpTemporal(b, idx, opn))} ::
             sat(i, ProposerExceedsCertainNextOpTemporal(b, idx, opn)) == ProposerExceedsCertainNextOp(b[i], idx, opn)
{
  stepmap(imap i :: ProposerExceedsCertainNextOp(b[i], idx, opn))
}

predicate ProposerHasCertainNextOpAndNonemptyRequestQueue(
  ps:RslState,
  idx:int,
  opn:int
  )
{
  && 0 <= idx < |ps.replicas|
  && var s := ps.replicas[idx].replica;
     && s.proposer.next_operation_number_to_propose == opn
     && |s.proposer.request_queue| > 0
     && s.acceptor.log_truncation_point >= opn
}

function{:opaque} ProposerHasCertainNextOpAndNonemptyRequestQueueTemporal(
  b:Behavior<RslState>,
  idx:int,
  opn:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, ProposerHasCertainNextOpAndNonemptyRequestQueueTemporal(b, idx, opn))} ::
             sat(i, ProposerHasCertainNextOpAndNonemptyRequestQueueTemporal(b, idx, opn)) == ProposerHasCertainNextOpAndNonemptyRequestQueue(b[i], idx, opn)
{
  stepmap(imap i :: ProposerHasCertainNextOpAndNonemptyRequestQueue(b[i], idx, opn))
}

predicate ProposerHasCertainNextOpAndNonemptyRequestQueueAndBatchTimer(
  ps:RslState,
  idx:int,
  opn:int,
  timerExpiration:int
  )
{
  && 0 <= idx < |ps.replicas|
  && var s := ps.replicas[idx].replica;
     && s.proposer.next_operation_number_to_propose == opn
     && |s.proposer.request_queue| > 0
     && s.acceptor.log_truncation_point >= opn
     && s.proposer.incomplete_batch_timer == IncompleteBatchTimerOn(timerExpiration)
}

function{:opaque} ProposerHasCertainNextOpAndNonemptyRequestQueueAndBatchTimerTemporal(
  b:Behavior<RslState>,
  idx:int,
  opn:int,
  timerExpiration:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, ProposerHasCertainNextOpAndNonemptyRequestQueueAndBatchTimerTemporal(b, idx, opn, timerExpiration))} ::
             sat(i, ProposerHasCertainNextOpAndNonemptyRequestQueueAndBatchTimerTemporal(b, idx, opn, timerExpiration)) == ProposerHasCertainNextOpAndNonemptyRequestQueueAndBatchTimer(b[i], idx, opn, timerExpiration)
{
  stepmap(imap i :: ProposerHasCertainNextOpAndNonemptyRequestQueueAndBatchTimer(b[i], idx, opn, timerExpiration))
}

lemma lemma_IfProposerHasCertainNextOpAndNonemptyRequestQueueThenProposerEventuallyStartsBatchTimerHelper(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int,
  i:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires prev_step <= i
  requires h.start_step + 1 <= prev_step
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  requires ProposerHasCertainNextOpAndNonemptyRequestQueue(b[prev_step], h.view.proposer_id, opn)
  requires && ProposerHasCertainNextOpAndNonemptyRequestQueue(b[i], h.view.proposer_id, opn)
           && AllLiveReplicasReadyForNextOperation(b[i], asp.live_quorum, h.view, opn)
  requires !(&& ProposerHasCertainNextOpAndNonemptyRequestQueue(b[i+1], h.view.proposer_id, opn)
             && AllLiveReplicasReadyForNextOperation(b[i+1], asp.live_quorum, h.view, opn))
  requires !(&& ProposerStartsBatchTimer(b[i], h.view.proposer_id)
             && AllLiveReplicasReadyForNextOperation(b[i], asp.live_quorum, h.view, opn))
  requires !(&& ProposerExceedsCertainNextOp(b[i], h.view.proposer_id, opn)
             && AllLiveReplicasReadyForNextOperation(b[i], asp.live_quorum, h.view, opn))
  requires NoReplicaBeyondView(b[i], h.view)
  requires !(&& ProposerStartsBatchTimer(b[i+1], h.view.proposer_id)
             && AllLiveReplicasReadyForNextOperation(b[i+1], asp.live_quorum, h.view, opn))
  requires !(&& ProposerExceedsCertainNextOp(b[i+1], h.view.proposer_id, opn)
             && AllLiveReplicasReadyForNextOperation(b[i+1], asp.live_quorum, h.view, opn))
  requires NoReplicaBeyondView(b[i+1], h.view)
  ensures  false
{
  var idx := h.view.proposer_id;
  lemma_ProposerStaysInState2InPhase2(b, asp, h, i);
  lemma_ProposerStaysInState2InPhase2(b, asp, h, i+1);
  lemma_AssumptionsMakeValidTransition(b, asp.c, i);
  lemma_IfAllLiveReplicasReadyForNextOperationThenSoLaterInPhase2(b, asp, h, opn, prev_step, i+1);
  lemma_LogTruncationPointMonotonicOneStep(b, asp.c, i, idx);
  lemma_IfAllLiveReplicasReadyForNextOperationThenSoLaterInPhase2(b, asp, h, opn, prev_step, i+1);
  lemma_LogTruncationPointMonotonicOneStep(b, asp.c, i, idx);
  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, idx);
}

lemma lemma_IfProposerHasCertainNextOpAndNonemptyRequestQueueThenProposerEventuallyStartsBatchTimer(
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
  requires ProposerHasCertainNextOpAndNonemptyRequestQueue(b[prev_step], h.view.proposer_id, opn)
  ensures  h.start_step + 1 <= step
  ensures  var f := PaxosTimeMap(b);
           var t := TimeToPerformGenericAction(asp);
           var w := and(ProposerStartsBatchTimerTemporal(b, h.view.proposer_id), AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn));
           var x := and(ProposerExceedsCertainNextOpTemporal(b, h.view.proposer_id, opn), AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn));
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, beforeabsolutetime(or(w, or(x, or(y, not(z)))), b[prev_step].environment.time + t, f))
{
  var f := PaxosTimeMap(b);
  var t := TimeToPerformGenericAction(asp);
  var w := and(ProposerStartsBatchTimerTemporal(b, h.view.proposer_id), AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn));
  var x := and(ProposerExceedsCertainNextOpTemporal(b, h.view.proposer_id, opn), AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn));
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var z := NoReplicaBeyondViewTemporal(b, h.view);
  
  var idx := h.view.proposer_id;
    
  var P := and(ProposerHasCertainNextOpAndNonemptyRequestQueueTemporal(b, h.view.proposer_id, opn), AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn));
  var Q := or(w, or(x, not(z)));
  var Action := MakeRslActionTemporalFromReadClockReplicaFunction(b, LReplicaNextReadClockMaybeNominateValueAndSend2a, idx);

  forall i | prev_step <= i
    ensures sat(i, TemporalWF1Req1(P, Q))
    ensures sat(i, TemporalWF1Req2(P, Q, Action))
  {
    if sat(i, P) && !sat(i, Q) && !sat(i+1, Q)
    {
      lemma_ProposerStaysInState2InPhase2(b, asp, h, i);
      lemma_ProposerStaysInState2InPhase2(b, asp, h, i+1);
      lemma_AssumptionsMakeValidTransition(b, asp.c, i);
      if !sat(i+1, P)
      {
        lemma_IfProposerHasCertainNextOpAndNonemptyRequestQueueThenProposerEventuallyStartsBatchTimerHelper(b, asp, h, opn, prev_step, i);
      }
      if sat(i, Action)
      {
        assert SpecificClockReadingRslActionOccurs(b[i], b[i+1], LReplicaNextReadClockMaybeNominateValueAndSend2a, idx);
        var ios:seq<RslIo> :| && RslNextOneReplica(b[i], b[i+1], idx, ios)
                              && SpontaneousIos(ios, 1)
                              && LReplicaNextReadClockMaybeNominateValueAndSend2a(b[i].replicas[idx].replica,
                                                                                 b[i+1].replicas[idx].replica,
                                                                                 SpontaneousClock(ios),
                                                                                 ExtractSentPacketsFromIos(ios));
        if sat(i, not(z))
        {
          assert sat(i, Q);
          assert false;
        }
        else
        {
          lemma_ProposerCanNominateInPhase2(b, asp, h, i);
          var s := b[i].replicas[idx].replica;
          assert s.acceptor.log_truncation_point >= s.proposer.next_operation_number_to_propose;
          assert s.proposer.next_operation_number_to_propose < s.acceptor.log_truncation_point + asp.c.params.max_log_length;
          assert LProposerCanNominateUsingOperationNumber(s.proposer, s.acceptor.log_truncation_point,
                                                          s.proposer.next_operation_number_to_propose);
          lemma_IfAllLiveReplicasReadyForNextOperationThenSoLaterInPhase2(b, asp, h, opn, prev_step, i+1);
          assert LProposerNominateNewValueAndSend2a(s.proposer, b[i+1].replicas[idx].replica.proposer, ios[0].t,
                                                    s.acceptor.log_truncation_point, ExtractSentPacketsFromIos(ios));
          assert ProposerStartsBatchTimer(b[i+1], h.view.proposer_id);
          assert sat(i+1, ProposerStartsBatchTimerTemporal(b, h.view.proposer_id));
          assert false;
        }
      }
    }
  }
  TemporalAlways(prev_step, TemporalWF1Req1(P, Q));
  TemporalAlways(prev_step, TemporalWF1Req2(P, Q, Action));
  lemma_ReplicaNextPerformsSubactionPeriodically(b, asp, idx, 3);
  lemma_EstablishRequirementsForWF1RealTime(b, asp, prev_step, Action, t);
  TemporalWF1RealTime(prev_step, P, Q, Action, t, f);

  TemporalDeduceFromAlways(prev_step, prev_step, imply(P, eventuallywithin(Q, t, f)));
  assert sat(prev_step, P);
  step := TemporalDeduceFromEventual(prev_step, beforeabsolutetime(Q, b[prev_step].environment.time + t, f));
}

lemma lemma_IfLiveReplicasReadyForAnOperationThenProposerEventuallyStartsBatchTimer(
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
           var t := b[prev_step].environment.time + TimeToPerformGenericAction(asp);
           var w := and(ProposerStartsBatchTimerTemporal(b, h.view.proposer_id), AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn));
           var x := and(ProposerExceedsCertainNextOpTemporal(b, h.view.proposer_id, opn), AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn));
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, beforeabsolutetime(or(w, or(x, or(y, not(z)))), t, f))
{
  var f := PaxosTimeMap(b);
  var t := b[prev_step].environment.time + TimeToPerformGenericAction(asp);
  var w := and(ProposerStartsBatchTimerTemporal(b, h.view.proposer_id), AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn));
  var x := and(ProposerExceedsCertainNextOpTemporal(b, h.view.proposer_id, opn), AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn));
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var z := NoReplicaBeyondViewTemporal(b, h.view);
    
  var idx := h.view.proposer_id;
  lemma_ConstantsAllConsistent(b, asp.c, prev_step);
  var s := b[prev_step].replicas[idx].replica.proposer;

  if !sat(prev_step, z)
  {
    step := prev_step;
    assert sat(step, beforeabsolutetime(not(z), t, f));
    return;
  }
    
  if s.next_operation_number_to_propose > opn
  {
    step := prev_step;
    assert sat(step, beforeabsolutetime(x, t, f));
    return;
  }

  if |s.request_queue| == 0
  {
    step := prev_step;
    assert sat(step, y);
    return;
  }

  step := lemma_IfProposerHasCertainNextOpAndNonemptyRequestQueueThenProposerEventuallyStartsBatchTimer(b, asp, h, opn, prev_step);
}

lemma lemma_IfProposerHasCertainNextOpAndNonemptyRequestQueueAndBatchTimerThenProposerEventuallyAdvancesNextOpHelper(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int,
  timerExpiration:int,
  i:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= prev_step
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  requires ProposerHasCertainNextOpAndNonemptyRequestQueueAndBatchTimer(b[prev_step], h.view.proposer_id, opn, timerExpiration)
  requires prev_step <= i
  requires ProposerHasCertainNextOpAndNonemptyRequestQueueAndBatchTimer(b[i], h.view.proposer_id, opn, timerExpiration)
  requires !ProposerHasCertainNextOpAndNonemptyRequestQueueAndBatchTimer(b[i+1], h.view.proposer_id, opn, timerExpiration)
  requires !(&& ProposerExceedsCertainNextOp(b[i], h.view.proposer_id, opn)
             && AllLiveReplicasReadyForNextOperation(b[i], asp.live_quorum, h.view, opn))
  requires NoReplicaBeyondView(b[i], h.view)
  requires !(&& ProposerExceedsCertainNextOp(b[i+1], h.view.proposer_id, opn)
             && AllLiveReplicasReadyForNextOperation(b[i+1], asp.live_quorum, h.view, opn))
  requires NoReplicaBeyondView(b[i+1], h.view)
  ensures  false
{
  var idx := h.view.proposer_id;

  lemma_ProposerBatchTimerNeverTooFarInFuture(b, asp, prev_step, idx);
  lemma_ConstantsAllConsistent(b, asp.c, prev_step);
  assert timerExpiration <= b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity;
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ProposerStaysInState2InPhase2(b, asp, h, i);
  lemma_ProposerStaysInState2InPhase2(b, asp, h, i+1);
  lemma_IfAllLiveReplicasReadyForNextOperationThenSoLaterInPhase2(b, asp, h, opn, prev_step, i+1);
  lemma_LogTruncationPointMonotonicOneStep(b, asp.c, i, idx);
  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, idx);
}

lemma lemma_IfProposerHasCertainNextOpAndNonemptyRequestQueueAndBatchTimerThenProposerEventuallyAdvancesNextOp(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  opn:OperationNumber,
  prev_step:int,
  timerExpiration:int
  ) returns (
  step:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires opn >= h.log_truncation_point
  requires h.start_step + 1 <= prev_step
  requires AllLiveReplicasReadyForNextOperation(b[prev_step], asp.live_quorum, h.view, opn)
  requires ProposerHasCertainNextOpAndNonemptyRequestQueueAndBatchTimer(b[prev_step], h.view.proposer_id, opn, timerExpiration)
  ensures  h.start_step + 1 <= step
  ensures  var f := PaxosTimeMap(b);
           var t := asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp);
           var x := and(ProposerExceedsCertainNextOpTemporal(b, h.view.proposer_id, opn), AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn));
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, beforeabsolutetime(or(x, not(z)), b[prev_step].environment.time + t, f))
{
  var f := PaxosTimeMap(b);
  var t := asp.c.params.max_batch_delay + TimeToPerformGenericAction(asp);
  var x := and(ProposerExceedsCertainNextOpTemporal(b, h.view.proposer_id, opn), AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn));
  var z := NoReplicaBeyondViewTemporal(b, h.view);
    
  var idx := h.view.proposer_id;

  lemma_ProposerBatchTimerNeverTooFarInFuture(b, asp, prev_step, idx);
  lemma_ConstantsAllConsistent(b, asp.c, prev_step);
  assert timerExpiration <= b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity;
    
  var P := ProposerHasCertainNextOpAndNonemptyRequestQueueAndBatchTimerTemporal(b, h.view.proposer_id, opn, timerExpiration);
  assert sat(prev_step, P);
  var Q := or(x, not(z));
  var Action := MakeRslActionTemporalFromReadClockReplicaFunction(b, LReplicaNextReadClockMaybeNominateValueAndSend2a, idx);

  forall i | prev_step <= i
    ensures sat(i, TemporalWF1Req1(P, Q))
    ensures sat(i, TemporalWF1RealTimeDelayedReq2(P, Q, Action, timerExpiration + asp.max_clock_ambiguity, f))
  {
    if sat(i, P) && !sat(i, Q) && !sat(i+1, Q)
    {
      lemma_ConstantsAllConsistent(b, asp.c, i);
      lemma_ProposerStaysInState2InPhase2(b, asp, h, i);
      lemma_ProposerStaysInState2InPhase2(b, asp, h, i+1);
      if !sat(i+1, P)
      {
        lemma_IfProposerHasCertainNextOpAndNonemptyRequestQueueAndBatchTimerThenProposerEventuallyAdvancesNextOpHelper(
          b, asp, h, opn, prev_step, timerExpiration, i);
      }
      if sat(i, nextafter(Action, timerExpiration + asp.max_clock_ambiguity, f))
      {
        assert SpecificClockReadingRslActionOccurs(b[i], b[i+1], LReplicaNextReadClockMaybeNominateValueAndSend2a, idx);
        var ios:seq<RslIo> :| && RslNextOneReplica(b[i], b[i+1], idx, ios)
                              && SpontaneousIos(ios, 1)
                              && LReplicaNextReadClockMaybeNominateValueAndSend2a(b[i].replicas[idx].replica,
                                                                                 b[i+1].replicas[idx].replica,
                                                                                 SpontaneousClock(ios),
                                                                                 ExtractSentPacketsFromIos(ios));
        if sat(i, not(z))
        {
          assert sat(i, Q);
          assert false;
        }
        else
        {
          lemma_ProposerCanNominateInPhase2(b, asp, h, i);
          var s := b[i].replicas[idx].replica;
          assert s.acceptor.log_truncation_point >= s.proposer.next_operation_number_to_propose;
          assert s.proposer.next_operation_number_to_propose < s.acceptor.log_truncation_point + asp.c.params.max_log_length;
          assert LProposerCanNominateUsingOperationNumber(s.proposer, s.acceptor.log_truncation_point, s.proposer.next_operation_number_to_propose);
          assert ios[0].LIoOpReadClock?;
          lemma_ClockAmbiguityLimitApplies(b, asp, i, idx, ios[0]);
          assert ios[0].t >= b[i+1].environment.time - asp.max_clock_ambiguity;
          assert ios[0].t >= timerExpiration;
          assert false;
        }
      }
    }
  }
  TemporalAlways(prev_step, TemporalWF1Req1(P, Q));
  TemporalAlways(prev_step, TemporalWF1RealTimeDelayedReq2(P, Q, Action, timerExpiration + asp.max_clock_ambiguity, f));
  lemma_ReplicaNextPerformsSubactionPeriodically(b, asp, idx, 3);
  lemma_EstablishRequirementsForWF1RealTimeDelayed(b, asp, prev_step, Action, TimeToPerformGenericAction(asp));
  step := TemporalWF1RealTimeDelayed(prev_step, P, Q, Action, TimeToPerformGenericAction(asp), timerExpiration + asp.max_clock_ambiguity, f);
}

lemma lemma_IfLiveReplicasReadyForAnOperationThenProposerEventuallyAdvancesNextOp(
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
           var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp) * 2;
           var x := and(ProposerExceedsCertainNextOpTemporal(b, h.view.proposer_id, opn), AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn));
           var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
           var z := NoReplicaBeyondViewTemporal(b, h.view);
           sat(step, beforeabsolutetime(or(x, or(y, not(z))), t, f))
{
  var f := PaxosTimeMap(b);
  var t := b[prev_step].environment.time + asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 2 + TimeToPerformGenericAction(asp) * 2;
  var x := and(ProposerExceedsCertainNextOpTemporal(b, h.view.proposer_id, opn), AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, opn));
  var y := AllLiveReplicasCaughtUpWithEarlierOperationWithRequestQueueEmptyTemporal(b, asp.live_quorum, h.view, opn + 1);
  var z := NoReplicaBeyondViewTemporal(b, h.view);
  var idx := h.view.proposer_id;

  var first_step := lemma_IfLiveReplicasReadyForAnOperationThenProposerEventuallyStartsBatchTimer(b, asp, h, opn, prev_step);
  assert sat(first_step, before(t, f));

  lemma_ConstantsAllConsistent(b, asp.c, first_step);
  var s := b[first_step].replicas[idx].replica.proposer;

  if !sat(first_step, z)
  {
    step := first_step;
    assert sat(step, beforeabsolutetime(not(z), t, f));
    return;
  }
    
  if s.next_operation_number_to_propose > opn
  {
    step := first_step;
    assert sat(step, x);
    return;
  }

  if |s.request_queue| == 0
  {
    step := first_step;
    assert sat(step, y);
    return;
  }

  step := lemma_IfProposerHasCertainNextOpAndNonemptyRequestQueueAndBatchTimerThenProposerEventuallyAdvancesNextOp(b, asp, h, opn, first_step, s.incomplete_batch_timer.when);
}

}
