include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "ViewChange.i.dfy"
include "ViewPropagation.i.dfy"
include "WF1.i.dfy"
include "../CommonProof/Actions.i.dfy"
include "../CommonProof/CanonicalizeBallot.i.dfy"
include "../CommonProof/PacketSending.i.dfy"
include "../CommonProof/Quorum.i.dfy"

module LivenessProof__ViewPropagation2_i {

import opened LiveRSL__Broadcast_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Message_i
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
import opened LivenessProof__ViewChange_i
import opened LivenessProof__ViewPropagation_i
import opened LivenessProof__WF1_i
import opened CommonProof__Actions_i
import opened CommonProof__CanonicalizeBallot_i
import opened CommonProof__Constants_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Quorum_i
import opened Temporal__Rules_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Temporal__WF1_i
import opened Environment_s

lemma lemma_ReplicaEventuallySendsSuspicionOrLeavesViewWF1Req1(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  suspector_idx:int,
  observer_idx:int,
  view:Ballot,
  nextHeartbeatTime:int,
  start_step:int
  )
  requires LivenessAssumptions(b, asp)
  requires suspector_idx in asp.live_quorum
  requires 0 <= observer_idx < |asp.c.config.replica_ids|
  requires 0 <= start_step
  requires sat(start_step, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, suspector_idx)))
  ensures  var P := HostSuspectsOrInLaterViewWithSpecificNextHeartbeatTimeTemporal(b, suspector_idx, view, nextHeartbeatTime);
           var Q := HostSentSuspicionOrInLaterViewTemporal(b, suspector_idx, observer_idx, view);
           sat(start_step, always(TemporalWF1Req1(P, Q)))
{
  var P := HostSuspectsOrInLaterViewWithSpecificNextHeartbeatTimeTemporal(b, suspector_idx, view, nextHeartbeatTime);
  var Q := HostSentSuspicionOrInLaterViewTemporal(b, suspector_idx, observer_idx, view);

  forall i | start_step <= i
    ensures sat(i, TemporalWF1Req1(P, Q))
  {
    if sat(i, P) && !sat(i, Q) && !sat(i+1, P) && !sat(i+1, Q)
    {
      lemma_ConstantsAllConsistent(b, asp.c, i);
      lemma_ConstantsAllConsistent(b, asp.c, i+1);
      lemma_ViewPlusOfHostMonotonic(b, asp, suspector_idx, i, i+1);
      lemma_AssumptionsMakeValidTransition(b, asp.c, i);
            
      var ps := b[i];
      var ps' := b[i+1];
      var s := ps.replicas[suspector_idx].replica;
      var s' := ps'.replicas[suspector_idx].replica;
      assert s'.nextHeartbeatTime != s.nextHeartbeatTime;

      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, suspector_idx);
      var sent_packets := ExtractSentPacketsFromIos(ios);
      assert |ios| > 0;
      assert ios[0].LIoOpReadClock?;
      assert LReplicaNextReadClockMaybeSendHeartbeat(s, s', SpontaneousClock(ios), sent_packets);
      assert ios[0].t >= s.nextHeartbeatTime;
      var sid := ps.constants.config.replica_ids[suspector_idx];
      var oid := ps.constants.config.replica_ids[observer_idx];
      var p := LPacket(oid, sid, RslMessage_Heartbeat(view, true, s.executor.ops_complete));
      assert p in sent_packets;
      assert p in ps'.environment.sentPackets;
      assert HostSentSuspicion(ps, sid, oid, view, p);
      assert false;
    }
  }

  TemporalAlways(start_step, TemporalWF1Req1(P, Q));
}

lemma {:timeLimitMultiplier 2} lemma_ReplicaEventuallySendsSuspicionOrLeavesViewWF1Req2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  suspector_idx:int,
  observer_idx:int,
  view:Ballot,
  nextHeartbeatTime:int,
  start_step:int
  )
  requires LivenessAssumptions(b, asp)
  requires suspector_idx in asp.live_quorum
  requires 0 <= observer_idx < |asp.c.config.replica_ids|
  requires asp.synchrony_start <= start_step
  requires sat(start_step, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, suspector_idx)))
  ensures  var P := HostSuspectsOrInLaterViewWithSpecificNextHeartbeatTimeTemporal(b, suspector_idx, view, nextHeartbeatTime);
           var Q := HostSentSuspicionOrInLaterViewTemporal(b, suspector_idx, observer_idx, view);
           var Action := ReplicaSchedule(b, suspector_idx)[9];
           sat(start_step, always(TemporalWF1RealTimeDelayedReq2(P, Q, Action, nextHeartbeatTime + asp.max_clock_ambiguity, PaxosTimeMap(b))))
{
  var P := HostSuspectsOrInLaterViewWithSpecificNextHeartbeatTimeTemporal(b, suspector_idx, view, nextHeartbeatTime);
  var Q := HostSentSuspicionOrInLaterViewTemporal(b, suspector_idx, observer_idx, view);
  var Action := ReplicaSchedule(b, suspector_idx)[9];
  var x := TemporalWF1RealTimeDelayedReq2(P, Q, Action, nextHeartbeatTime + asp.max_clock_ambiguity, PaxosTimeMap(b));

  forall i | start_step <= i
    ensures sat(i, x)
  {
    if sat(i, P) && sat(i, nextafter(Action, nextHeartbeatTime + asp.max_clock_ambiguity, PaxosTimeMap(b))) && !sat(i, Q) && !sat(i+1, Q)
    {
      lemma_ConstantsAllConsistent(b, asp.c, i);
      lemma_ConstantsAllConsistent(b, asp.c, i+1);
      assert SpecificClockReadingRslActionOccurs(b[i], b[i+1], LReplicaNextReadClockMaybeSendHeartbeat, suspector_idx);
      var ios :| && RslNextOneReplica(b[i], b[i+1], suspector_idx, ios)
                 && SpontaneousIos(ios, 1)
                 && LReplicaNextReadClockMaybeSendHeartbeat(b[i].replicas[suspector_idx].replica, b[i+1].replicas[suspector_idx].replica,
                                                           SpontaneousClock(ios), ExtractSentPacketsFromIos(ios));
      var ps := b[i];
      var ps' := b[i+1];
      var s := ps.replicas[suspector_idx].replica;
      var s' := ps'.replicas[suspector_idx].replica;
      var sid := ps.constants.config.replica_ids[suspector_idx];
      var oid := ps.constants.config.replica_ids[observer_idx];
      var p := LPacket(oid, sid, RslMessage_Heartbeat(view, true, s.executor.ops_complete));
      lemma_ClockAmbiguityLimitApplies(b, asp, i, suspector_idx, ios[0]);
      assert LBroadcastToEveryone(s.constants.all.config, s.constants.my_index,
                                  RslMessage_Heartbeat(s.proposer.election_state.current_view,
                                                       s.constants.my_index in s.proposer.election_state.current_view_suspectors,
                                                       s.executor.ops_complete),
                                  ExtractSentPacketsFromIos(ios));
      assert p in ExtractSentPacketsFromIos(ios);
      assert p in ps'.environment.sentPackets;
      assert HostSentSuspicion(ps, sid, oid, view, p);
      assert false;
    }
  }

  TemporalAlways(start_step, x);
}

lemma lemma_ReplicaEventuallySendsSuspicionOrLeavesView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  suspector_idx:int,
  observer_idx:int,
  start_step:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires suspector_idx in asp.live_quorum
  requires processing_sync_start <= start_step
  requires 0 <= suspector_idx < |b[start_step].replicas|
  requires 0 <= observer_idx < |b[start_step].replicas|
  ensures  start_step <= step
  ensures  HostSentSuspicionOrInLaterView(b[step], suspector_idx, observer_idx, CurrentViewOfHost(b[start_step], suspector_idx))
{
  lemma_ConstantsAllConsistent(b, asp.c, start_step);
  var view := CurrentViewOfHost(b[start_step], suspector_idx);
  var i := lemma_ReplicaEventuallySuspectsViewOrIsInDifferentView(b, asp, processing_sync_start, processing_bound, suspector_idx, start_step);
  lemma_ConstantsAllConsistent(b, asp.c, i);
  var nextHeartbeatTime := b[i].replicas[suspector_idx].replica.nextHeartbeatTime;
  var P := HostSuspectsOrInLaterViewWithSpecificNextHeartbeatTimeTemporal(b, suspector_idx, view, nextHeartbeatTime);
  var Q := HostSentSuspicionOrInLaterViewTemporal(b, suspector_idx, observer_idx, view);
  var Action := ReplicaSchedule(b, suspector_idx)[9];

  Lemma_AlwaysImpliesLaterAlways(start_step, i, RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, suspector_idx));
  lemma_ReplicaEventuallySendsSuspicionOrLeavesViewWF1Req1(b, asp, suspector_idx, observer_idx, view, nextHeartbeatTime, i);
  lemma_ReplicaEventuallySendsSuspicionOrLeavesViewWF1Req2(b, asp, suspector_idx, observer_idx, view, nextHeartbeatTime, i);
  lemma_ReplicaNextPerformsSubactionPeriodically(b, asp, suspector_idx, 9);

  lemma_EstablishRequirementsForWF1RealTimeDelayed(b, asp, i, Action, TimeToPerformGenericAction(asp));
  step := TemporalWF1RealTimeDelayed(i, P, Q, Action, TimeToPerformGenericAction(asp), nextHeartbeatTime + asp.max_clock_ambiguity, PaxosTimeMap(b));
}

lemma lemma_ReplicaEventuallyPropagatesSuspicionOrLeavesView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  suspector_idx:int,
  observer_idx:int,
  start_step:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires suspector_idx in asp.live_quorum
  requires observer_idx in asp.live_quorum
  requires processing_sync_start <= start_step
  requires 0 <= suspector_idx < |b[start_step].replicas|
  ensures  start_step <= step
  ensures  0 <= suspector_idx < |b[step].replicas|
  ensures  0 <= observer_idx < |b[step].replicas|
  ensures  var view := CurrentViewOfHost(b[start_step], suspector_idx);
           SuspicionPropagatedToObserver(b[step], suspector_idx, observer_idx, view)
{
  lemma_ConstantsAllConsistent(b, asp.c, start_step);
  var view := CurrentViewOfHost(b[start_step], suspector_idx);
  var sid := asp.c.config.replica_ids[suspector_idx];
  var oid := asp.c.config.replica_ids[observer_idx];

  var i := lemma_ReplicaEventuallySendsSuspicionOrLeavesView(b, asp, processing_sync_start, processing_bound, suspector_idx, observer_idx, start_step);
  lemma_ConstantsAllConsistent(b, asp.c, i);
  assert HostSentSuspicionOrInLaterView(b[i], suspector_idx, observer_idx, view);
  if BalLt(view, CurrentViewOfHost(b[i], suspector_idx))
  {
    step := i;
    return;
  }
  var p :| HostSentSuspicion(b[i], sid, oid, view, p);
  var processing_step, ios := lemma_PacketSentToIndexProcessedByIt(b, asp, processing_sync_start, processing_bound, i, observer_idx, p);
  lemma_ConstantsAllConsistent(b, asp.c, processing_step);
  lemma_ConstantsAllConsistent(b, asp.c, processing_step+1);
  var s := b[processing_step].replicas[observer_idx].replica;
  var s' := b[processing_step+1].replicas[observer_idx].replica;
  var es := s.proposer.election_state;
  var es' := s'.proposer.election_state;
  assert LProposerProcessHeartbeat(s.proposer, s'.proposer, p, ios[1].t);
  step := processing_step + 1;
  assert ReplicasDistinct(asp.c.config.replica_ids, suspector_idx, GetReplicaIndex(p.src, es.constants.all.config));
  if es.current_view == view
  {
    assert suspector_idx in es'.current_view_suspectors;
  }
  else if BalLt(es.current_view, view)
  {
    assert suspector_idx in es'.current_view_suspectors;
  }
  else
  {
    lemma_BalLtProperties();
    assert BalLt(view, es.current_view);
  }
}

lemma lemma_SuspicionPropagatedToObserverStableOneStep(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  suspector_idx:int,
  observer_idx:int,
  view:Ballot,
  i:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= observer_idx < |asp.c.config.replica_ids|
  requires 0 <= suspector_idx < |asp.c.config.replica_ids|
  requires 0 <= i
  requires SuspicionPropagatedToObserver(b[i], suspector_idx, observer_idx, view)
  ensures  SuspicionPropagatedToObserver(b[i+1], suspector_idx, observer_idx, view)
{
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i+1);
  lemma_AssumptionsMakeValidTransition(b, asp.c, i);
  lemma_ViewPlusOfHostMonotonic(b, asp, suspector_idx, i, i+1);
  lemma_ViewPlusOfHostMonotonic(b, asp, observer_idx, i, i+1);
}

lemma lemma_SuspicionPropagatedToObserverStableMultipleSteps(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  suspector_idx:int,
  observer_idx:int,
  view:Ballot,
  i:int,
  j:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= observer_idx < |asp.c.config.replica_ids|
  requires 0 <= suspector_idx < |asp.c.config.replica_ids|
  requires 0 <= i <= j
  requires SuspicionPropagatedToObserver(b[i], suspector_idx, observer_idx, view)
  ensures  SuspicionPropagatedToObserver(b[j], suspector_idx, observer_idx, view)
  decreases j-i
{
  if j > i + 1
  {
    lemma_SuspicionPropagatedToObserverStableMultipleSteps(b, asp, suspector_idx, observer_idx, view, i, j-1);
    lemma_SuspicionPropagatedToObserverStableMultipleSteps(b, asp, suspector_idx, observer_idx, view, j-1, j);
  }
  else if j == i + 1
  {
    lemma_ConstantsAllConsistent(b, asp.c, i);
    lemma_ConstantsAllConsistent(b, asp.c, i+1);
    lemma_AssumptionsMakeValidTransition(b, asp.c, i);
    lemma_ViewPlusOfHostMonotonic(b, asp, observer_idx, i, i+1);
    lemma_ViewPlusOfHostMonotonic(b, asp, suspector_idx, i, i+1);
  }
}

lemma lemma_SuspicionPropagatedToObserverStable(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  suspector_idx:int,
  observer_idx:int,
  view:Ballot,
  i:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= observer_idx < |asp.c.config.replica_ids|
  requires 0 <= suspector_idx < |asp.c.config.replica_ids|
  requires 0 <= i
  requires SuspicionPropagatedToObserver(b[i], suspector_idx, observer_idx, view)
  ensures  sat(i, always(SuspicionPropagatedToObserverTemporal(b, suspector_idx, observer_idx, view)))
{
  forall j | i <= j
    ensures sat(j, SuspicionPropagatedToObserverTemporal(b, suspector_idx, observer_idx, view))
  {
    lemma_SuspicionPropagatedToObserverStableMultipleSteps(b, asp, suspector_idx, observer_idx, view, i, j);
  }

  TemporalAlways(i, SuspicionPropagatedToObserverTemporal(b, suspector_idx, observer_idx, view));
}

lemma lemma_SuspicionEventuallyPropagatedToObserverForever(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  suspector_idx:int,
  observer_idx:int,
  start_step:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires suspector_idx in asp.live_quorum
  requires observer_idx in asp.live_quorum
  requires processing_sync_start <= start_step
  requires 0 <= suspector_idx < |b[start_step].replicas|
  ensures  start_step <= step
  ensures  0 <= suspector_idx < |b[step].replicas|
  ensures  0 <= observer_idx < |b[step].replicas|
  ensures  var view := CurrentViewOfHost(b[start_step], suspector_idx);
           sat(step, always(SuspicionPropagatedToObserverTemporal(b, suspector_idx, observer_idx, view)))
{
  lemma_ConstantsAllConsistent(b, asp.c, start_step);
  var view := CurrentViewOfHost(b[start_step], suspector_idx);
  step := lemma_ReplicaEventuallyPropagatesSuspicionOrLeavesView(b, asp, processing_sync_start, processing_bound, suspector_idx, observer_idx, start_step);
  lemma_SuspicionPropagatedToObserverStable(b, asp, suspector_idx, observer_idx, view, step);
}

lemma lemma_SuspicionOfLiveReplicasEventuallyPropagatedToObserverForever(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  observer_idx:int,
  suspector_indices:set<int>,
  view:Ballot,
  start_step:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires suspector_indices <= asp.live_quorum
  requires observer_idx in asp.live_quorum
  requires processing_sync_start <= start_step
  requires forall suspector_idx :: suspector_idx in suspector_indices ==> 0 <= suspector_idx < |b[start_step].replicas| && CurrentViewOfHost(b[start_step], suspector_idx) == view
  ensures  start_step <= step
  ensures  forall suspector_idx :: suspector_idx in suspector_indices ==> sat(step, always(SuspicionPropagatedToObserverTemporal(b, suspector_idx, observer_idx, view)))
  decreases |suspector_indices|
{
  if |suspector_indices| == 0
  {
    step := start_step;
  }
  else
  {
    var suspector_idx :| suspector_idx in suspector_indices;
    var other_indices := suspector_indices - { suspector_idx };
    var first_step := lemma_SuspicionOfLiveReplicasEventuallyPropagatedToObserverForever(b, asp, processing_sync_start, processing_bound, observer_idx, other_indices, view, start_step);
    var second_step := lemma_SuspicionEventuallyPropagatedToObserverForever(b, asp, processing_sync_start, processing_bound, suspector_idx, observer_idx, start_step);
    if second_step >= first_step
    {
      step := second_step;
      forall sidx | sidx in suspector_indices
        ensures sat(step, always(SuspicionPropagatedToObserverTemporal(b, sidx, observer_idx, view)))
      {
        if sidx != suspector_idx
        {
          Lemma_AlwaysImpliesLaterAlways(first_step, step, SuspicionPropagatedToObserverTemporal(b, sidx, observer_idx, view));
        }
      }
    }
    else
    {
      step := first_step;
      forall sidx | sidx in suspector_indices
        ensures sat(step, always(SuspicionPropagatedToObserverTemporal(b, sidx, observer_idx, view)))
      {
        if sidx == suspector_idx
        {
          Lemma_AlwaysImpliesLaterAlways(second_step, step, SuspicionPropagatedToObserverTemporal(b, sidx, observer_idx, view));
        }
      }
    }
  }
}

}
