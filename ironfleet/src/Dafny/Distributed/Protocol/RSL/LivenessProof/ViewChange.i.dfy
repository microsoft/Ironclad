include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "RequestsReceived.i.dfy"
include "RoundRobin.i.dfy"
include "StablePeriod.i.dfy"
include "WF1.i.dfy"
include "../CommonProof/Constants.i.dfy"
include "../CommonProof/Actions.i.dfy"

module LivenessProof__ViewChange_i {

import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Election_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Environment_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__PacketHandling_i
import opened LivenessProof__RequestsReceived_i
import opened LivenessProof__RoundRobin_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__WF1_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened Temporal__LeadsTo_i
import opened Temporal__Rules_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Temporal__WF1_i
import opened Collections__Maps2_s
import opened Common__UpperBound_s

datatype ViewPlus = ViewPlus(view:Ballot, suspected:bool)

predicate ViewPlusLt(vp1:ViewPlus, vp2:ViewPlus)
{
  BalLt(vp1.view, vp2.view) || (vp1.view == vp2.view && !vp1.suspected && vp2.suspected)
}

predicate ViewPlusLe(vp1:ViewPlus, vp2:ViewPlus)
{
  BalLt(vp1.view, vp2.view) || (vp1.view == vp2.view && (vp1.suspected ==> vp2.suspected))
}

function CurrentViewPlusOfHost(
  ps:RslState,
  replica_index:int
  ):ViewPlus
  requires 0 <= replica_index < |ps.replicas|
{
  var es := ps.replicas[replica_index].replica.proposer.election_state;
  ViewPlus(es.current_view, es.constants.my_index in es.current_view_suspectors)
}

predicate HostInView(
  ps:RslState,
  replica_index:int,
  view:Ballot
  )
{
  0 <= replica_index < |ps.replicas| && CurrentViewOfHost(ps, replica_index) == view
}

function{:opaque} HostInViewTemporal(b:Behavior<RslState>, replica_index:int, view:Ballot):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, HostInViewTemporal(b, replica_index, view))} ::
               sat(i, HostInViewTemporal(b, replica_index, view)) <==> HostInView(b[i], replica_index, view)
{
  stepmap(imap i :: HostInView(b[i], replica_index, view))
}

predicate HostSuspectsOrInLaterView(
  ps:RslState,
  replica_index:int,
  view:Ballot
  )
{
  && 0 <= replica_index < |ps.replicas|
  && ViewPlusLe(ViewPlus(view, true), CurrentViewPlusOfHost(ps, replica_index))
}

function{:opaque} HostSuspectsOrInLaterViewTemporal(b:Behavior<RslState>, replica_index:int, view:Ballot):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, HostSuspectsOrInLaterViewTemporal(b, replica_index, view))} ::
               sat(i, HostSuspectsOrInLaterViewTemporal(b, replica_index, view)) <==> HostSuspectsOrInLaterView(b[i], replica_index, view)
{
  stepmap(imap i :: HostSuspectsOrInLaterView(b[i], replica_index, view))
}

predicate HostReadyToSuspectView(
  ps:RslState,
  idx:int,
  view:Ballot,
  req:Request,
  epoch_end_time:int
  )
{
  && 0 <= idx < |ps.replicas|
  && var es := ps.replicas[idx].replica.proposer.election_state;
    && es.current_view == view
    && !(es.constants.my_index in es.current_view_suspectors)
    && es.epoch_end_time == epoch_end_time
    && req in es.requests_received_prev_epochs
}

function{:opaque} HostReadyToSuspectViewTemporal(
  b:Behavior<RslState>,
  idx:int,
  view:Ballot,
  req:Request,
  epoch_end_time:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, HostReadyToSuspectViewTemporal(b, idx, view, req, epoch_end_time))} ::
               sat(i, HostReadyToSuspectViewTemporal(b, idx, view, req, epoch_end_time))
               <==> HostReadyToSuspectView(b[i], idx, view, req, epoch_end_time)
{
  stepmap(imap i :: HostReadyToSuspectView(b[i], idx, view, req, epoch_end_time))
}


lemma lemma_ViewPlusLeTransitive(vp1:ViewPlus, vp2:ViewPlus, vp3:ViewPlus)
  ensures ViewPlusLe(vp1, vp2) && ViewPlusLe(vp2, vp3) ==> ViewPlusLe(vp1, vp3)
{
  lemma_BalLtProperties();
}

lemma lemma_ViewPlusLeTransitiveDefinite(vp1:ViewPlus, vp2:ViewPlus, vp3:ViewPlus)
  requires ViewPlusLe(vp1, vp2)
  requires ViewPlusLe(vp2, vp3)
  ensures  ViewPlusLe(vp1, vp3)
{
  lemma_ViewPlusLeTransitive(vp1, vp2, vp3);
}

lemma lemma_ComputeSuccessorViewStrictlyIncreases(view:Ballot, constants:LConstants)
  requires LtUpperBound(view.seqno, constants.params.max_integer_val)
  ensures BalLt(view, ComputeSuccessorView(view, constants))
{
  lemma_BalLtProperties();
}

lemma lemma_ViewPlusOfHostMonotonic(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  idx:int,
  i:int,
  j:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i <= j
  requires 0 <= idx < |asp.c.config.replica_ids|
  ensures  0 <= idx < |b[i].replicas|
  ensures  0 <= idx < |b[j].replicas|
  ensures  ViewPlusLe(CurrentViewPlusOfHost(b[i], idx), CurrentViewPlusOfHost(b[j], idx))
  decreases j-i
{
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, j);
  lemma_BalLtProperties();

  var vp1 := CurrentViewPlusOfHost(b[i], idx);
  var vp2 := CurrentViewPlusOfHost(b[j], idx);
    
  if j == i + 1
  {
    lemma_AssumptionsMakeValidTransition(b, asp.c, i);
    if !ViewPlusLe(vp1, vp2)
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, idx);
      lemma_OverflowProtectionNotUsedForReplica(b, asp, i, idx);
      assert false;
    }
  }
  else if j > i + 1
  {
    lemma_ViewPlusOfHostMonotonic(b, asp, idx, i, i+1);
    lemma_ViewPlusOfHostMonotonic(b, asp, idx, i+1, j);
    lemma_ViewPlusLeTransitive(vp1, CurrentViewPlusOfHost(b[i+1], idx), vp2);
  }
}

lemma lemma_ViewOfHostMonotonic(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  idx:int,
  i:int,
  j:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i <= j
  requires 0 <= idx < |asp.c.config.replica_ids|
  ensures  0 <= idx < |b[i].replicas|
  ensures  0 <= idx < |b[j].replicas|
  ensures  BalLeq(CurrentViewOfHost(b[i], idx), CurrentViewOfHost(b[j], idx))
{
  lemma_ViewPlusOfHostMonotonic(b, asp, idx, i, j);
}

lemma lemma_HostReadyToSuspectViewEventuallyDoesWF1Req1(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  idx:int,
  view:Ballot,
  epoch_end_time:int,
  start_step:int
  )
  requires LivenessAssumptions(b, asp)
  requires idx in asp.live_quorum
  requires 0 <= start_step
  requires sat(start_step, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx)))
  ensures  var P := HostReadyToSuspectViewTemporal(b, idx, view, asp.persistent_request, epoch_end_time);
           var Q := HostSuspectsOrInLaterViewTemporal(b, idx, view);
           sat(start_step, always(TemporalWF1Req1(P, Q)))
{
  var P := HostReadyToSuspectViewTemporal(b, idx, view, asp.persistent_request, epoch_end_time);
  var Q := HostSuspectsOrInLaterViewTemporal(b, idx, view);

  forall i | start_step <= i
    ensures sat(i, TemporalWF1Req1(P, Q))
  {
    if sat(i, P) && !sat(i, Q) && !sat(i+1, P) && !sat(i+1, Q)
    {
      lemma_ConstantsAllConsistent(b, asp.c, i);
      lemma_ConstantsAllConsistent(b, asp.c, i+1);
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, idx);
      lemma_OverflowProtectionNotUsedForReplica(b, asp, i, idx);
      TemporalDeduceFromAlways(start_step, i+1, RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx));
      assert false;
    }
  }

  TemporalAlways(start_step, TemporalWF1Req1(P, Q));
}

lemma lemma_HostReadyToSuspectViewEventuallyDoesWF1Req2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  idx:int,
  view:Ballot,
  epoch_end_time:int,
  start_step:int
  )
  requires LivenessAssumptions(b, asp)
  requires idx in asp.live_quorum
  requires asp.synchrony_start <= start_step
  requires sat(start_step, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx)))
  ensures  var P := HostReadyToSuspectViewTemporal(b, idx, view, asp.persistent_request, epoch_end_time);
           var Q := HostSuspectsOrInLaterViewTemporal(b, idx, view);
           var Action := ReplicaSchedule(b, idx)[7];
           sat(start_step, always(TemporalWF1RealTimeDelayedReq2(P, Q, Action, epoch_end_time + asp.max_clock_ambiguity, PaxosTimeMap(b))))
{
  var epochEndTimePlus := epoch_end_time + asp.max_clock_ambiguity;
  var P := HostReadyToSuspectViewTemporal(b, idx, view, asp.persistent_request, epoch_end_time);
  var Q := HostSuspectsOrInLaterViewTemporal(b, idx, view);
  var Action := ReplicaSchedule(b, idx)[7];
  var x := TemporalWF1RealTimeDelayedReq2(P, Q, Action, epochEndTimePlus, PaxosTimeMap(b));

  forall i | start_step <= i
    ensures sat(i, x)
  {
    if sat(i, P) && sat(i, nextafter(Action, epochEndTimePlus, PaxosTimeMap(b))) && !sat(i, Q) && !sat(i+1, Q)
    {
      lemma_ConstantsAllConsistent(b, asp.c, i);
      lemma_ConstantsAllConsistent(b, asp.c, i+1);
      assert SpecificClockReadingRslActionOccurs(b[i], b[i+1], LReplicaNextReadClockCheckForViewTimeout, idx);
      var ios:seq<RslIo> :| && RslNextOneReplica(b[i], b[i+1], idx, ios)
                            && SpontaneousIos(ios, 1)
                            && LReplicaNextReadClockCheckForViewTimeout(b[i].replicas[idx].replica, b[i+1].replicas[idx].replica,
                                                                       SpontaneousClock(ios), ExtractSentPacketsFromIos(ios));
      lemma_ClockAmbiguityLimitApplies(b, asp, i, idx, ios[0]);
      lemma_OverflowProtectionNotUsedForReplica(b, asp, i, idx);
      var es := b[i].replicas[idx].replica.proposer.election_state;
      var es' := b[i+1].replicas[idx].replica.proposer.election_state;
      assert ElectionStateCheckForViewTimeout(es, es', ios[0].t);
      assert es' == es.(current_view_suspectors := es.current_view_suspectors + {es.constants.my_index},
                        epoch_end_time := UpperBoundedAddition(ios[0].t, es.epoch_length, es.constants.all.params.max_integer_val),
                        requests_received_prev_epochs := BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val),
                        requests_received_this_epoch := []);
      assert false;
    }
  }

  TemporalAlways(start_step, x);
}

lemma lemma_HostReadyToSuspectViewEventuallyDoes(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  idx:int,
  view:Ballot,
  epoch_end_time:int,
  start_step:int
  )
  requires LivenessAssumptions(b, asp)
  requires idx in asp.live_quorum
  requires asp.synchrony_start <= start_step
  requires sat(start_step, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx)))
  ensures  var P := HostReadyToSuspectViewTemporal(b, idx, view, asp.persistent_request, epoch_end_time);
           var Q := HostSuspectsOrInLaterViewTemporal(b, idx, view);
           sat(start_step, leadsto(P, Q))
{
  var epochEndTimePlus := epoch_end_time + asp.max_clock_ambiguity;
  var P := HostReadyToSuspectViewTemporal(b, idx, view, asp.persistent_request, epoch_end_time);
  var Q := HostSuspectsOrInLaterViewTemporal(b, idx, view);
  var Action := ReplicaSchedule(b, idx)[7];

  forall i | start_step <= i
    ensures sat(i, imply(P, eventual(Q)))
  {
    if sat(i, P)
    {
      Lemma_AlwaysImpliesLaterAlways(start_step, i, RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx));
      lemma_HostReadyToSuspectViewEventuallyDoesWF1Req1(b, asp, idx, view, epoch_end_time, i);
      lemma_HostReadyToSuspectViewEventuallyDoesWF1Req2(b, asp, idx, view, epoch_end_time, i);
      lemma_ReplicaNextPerformsSubactionPeriodically(b, asp, idx, 7);
      lemma_EstablishRequirementsForWF1RealTimeDelayed(b, asp, i, Action, TimeToPerformGenericAction(asp));
      var step := TemporalWF1RealTimeDelayed(i, P, Q, Action, TimeToPerformGenericAction(asp), epochEndTimePlus, PaxosTimeMap(b));
      TemporalEventually(i, step, Q);
    }
  }
  TemporalAlways(start_step, imply(P, eventual(Q)));
}

lemma lemma_ReplicaEventuallySuspectsViewOrIsInDifferentView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  idx:int,
  start_step:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires idx in asp.live_quorum
  requires processing_sync_start <= start_step
  requires 0 <= idx < |b[start_step].replicas|
  ensures  start_step <= step
  ensures  HostSuspectsOrInLaterView(b[step], idx, CurrentViewOfHost(b[start_step], idx))
  ensures  sat(step, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx)))
{
  var initialView := CurrentViewOfHost(b[start_step], idx);
  var i := lemma_EventuallyPersistentRequestAlwaysInRequestsReceivedPrevEpochs(b, asp, processing_sync_start, processing_bound, idx);
  if i < start_step
  {
    Lemma_AlwaysImpliesLaterAlways(i, start_step, RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx));
    i := start_step;
  }
  assert sat(i, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx)));
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ViewPlusOfHostMonotonic(b, asp, idx, start_step, i);
  if HostSuspectsOrInLaterView(b[i], idx, initialView)
  {
    TemporalEventually(start_step, i, HostSuspectsOrInLaterViewTemporal(b, idx, initialView));
    step := i;
  }
  else
  {
    var epoch_end_time := b[i].replicas[idx].replica.proposer.election_state.epoch_end_time;
    var P := HostReadyToSuspectViewTemporal(b, idx, initialView, asp.persistent_request, epoch_end_time);
    var Q := HostSuspectsOrInLaterViewTemporal(b, idx, initialView);
    lemma_HostReadyToSuspectViewEventuallyDoes(b, asp, idx, initialView, epoch_end_time, i);
    TemporalDeduceFromAlways(i, i, RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx));
    assert HostReadyToSuspectView(b[i], idx, initialView, asp.persistent_request, epoch_end_time);
    TemporalDeduceFromAlways(i, i, imply(P, eventual(Q)));
    step := TemporalDeduceFromEventual(i, Q);
    Lemma_AlwaysImpliesLaterAlways(i, step, RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx));
  }
}

}
