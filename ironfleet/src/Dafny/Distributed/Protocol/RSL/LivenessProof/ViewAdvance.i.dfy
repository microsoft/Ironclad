include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "ViewPropagation.i.dfy"
include "ViewPropagation2.i.dfy"
include "WF1.i.dfy"
include "../CommonProof/Constants.i.dfy"

module LivenessProof__ViewAdvance_i {

import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Election_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Message_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Environment_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__PacketHandling_i
import opened LivenessProof__RealTime_i
import opened LivenessProof__RoundRobin_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__ViewChange_i
import opened LivenessProof__ViewPropagation_i
import opened LivenessProof__ViewPropagation2_i
import opened LivenessProof__WF1_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened Temporal__Rules_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Temporal__Time_i
import opened Temporal__WF1_i
import opened Environment_s
import opened Collections__Maps2_s

function TimeForOneReplicaToSendHeartbeat(asp:AssumptionParameters):int
  requires asp.host_period > 0
  requires asp.max_clock_ambiguity >= 0
  requires asp.c.params.heartbeat_period >= 0
  ensures  TimeForOneReplicaToSendHeartbeat(asp) >= 0
{
  asp.max_clock_ambiguity * 2 + asp.c.params.heartbeat_period + TimeToPerformGenericAction(asp)
}

function TimeForOneReplicaToAdvanceAnother(asp:AssumptionParameters, processing_bound:int):int
  requires asp.host_period > 0
  requires asp.max_clock_ambiguity >= 0
  requires asp.c.params.heartbeat_period >= 0
  requires processing_bound >= 0
  ensures  TimeForOneReplicaToAdvanceAnother(asp, processing_bound) >= 0
{
  TimeForOneReplicaToSendHeartbeat(asp) + processing_bound
}

predicate HostReachedView(
  ps:RslState,
  replica_index:int,
  view:Ballot
  )
{
  0 <= replica_index < |ps.replicas| && BalLeq(view, CurrentViewOfHost(ps, replica_index))
}

function{:opaque} HostReachedViewTemporal(b:Behavior<RslState>, replica_index:int, view:Ballot):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, HostReachedViewTemporal(b, replica_index, view))} ::
               sat(i, HostReachedViewTemporal(b, replica_index, view)) <==> HostReachedView(b[i], replica_index, view)
{
  stepmap(imap i :: HostReachedView(b[i], replica_index, view))
}

predicate NextHeartbeatTimeInv(ps:RslState, idx:int, max_clock_ambiguity:int)
{
  && 0 <= idx < |ps.replicas|
  && ps.replicas[idx].replica.nextHeartbeatTime <= ps.environment.time + max_clock_ambiguity + ps.constants.params.heartbeat_period
}

predicate ReplicaHasSpecificNextHeartbeatTime(
  ps:RslState,
  replica_index:int,
  nextHeartbeatTime:int
  )
{
  && 0 <= replica_index < |ps.replicas|
  && ps.replicas[replica_index].replica.nextHeartbeatTime == nextHeartbeatTime
}

function{:opaque} ReplicaHasSpecificNextHeartbeatTimeTemporal(
  b:Behavior<RslState>,
  replica_index:int,
  nextHeartbeatTime:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, ReplicaHasSpecificNextHeartbeatTimeTemporal(b, replica_index, nextHeartbeatTime))} ::
             sat(i, ReplicaHasSpecificNextHeartbeatTimeTemporal(b, replica_index, nextHeartbeatTime)) <==>
             ReplicaHasSpecificNextHeartbeatTime(b[i], replica_index, nextHeartbeatTime)
{
  stepmap(imap i :: ReplicaHasSpecificNextHeartbeatTime(b[i], replica_index, nextHeartbeatTime))
}


predicate ReplicaSentHeartbeat(
  ps:RslState,
  ps':RslState,
  sender_idx:int,
  receiver_idx:int,
  p:RslPacket
  )
{
  && 0 <= receiver_idx < |ps.constants.config.replica_ids|
  && 0 <= sender_idx < |ps.constants.config.replica_ids|
  && 0 <= sender_idx < |ps.replicas|
  && p.dst == ps.constants.config.replica_ids[receiver_idx]
  && p.src == ps.constants.config.replica_ids[sender_idx]
  && p.msg.RslMessage_Heartbeat?
  && p.msg.bal_heartbeat == ps.replicas[sender_idx].replica.proposer.election_state.current_view
  && ps.environment.nextStep.LEnvStepHostIos?
  && ps.environment.nextStep.actor == p.src
  && LIoOpSend(p) in ps.environment.nextStep.ios
  && RslNext(ps, ps')
  && RslNextOneReplica(ps, ps', sender_idx, ps.environment.nextStep.ios)
}

function{:opaque} ReplicaSentHeartbeatTemporal(
  b:Behavior<RslState>,
  sender_idx:int,
  receiver_idx:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, ReplicaSentHeartbeatTemporal(b, sender_idx, receiver_idx))} ::
             sat(i, ReplicaSentHeartbeatTemporal(b, sender_idx, receiver_idx)) <==>
             exists p {:trigger ReplicaSentHeartbeat(b[i], b[nextstep(i)], sender_idx, receiver_idx, p)} ::
               ReplicaSentHeartbeat(b[i], b[nextstep(i)], sender_idx, receiver_idx, p)
{
  stepmap(imap i :: exists p {:trigger ReplicaSentHeartbeat(b[i], b[nextstep(i)], sender_idx, receiver_idx, p)} :: ReplicaSentHeartbeat(b[i], b[nextstep(i)], sender_idx, receiver_idx, p))
}
    
lemma lemma_NextHeartbeatTimeInv(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires idx in asp.live_quorum
  ensures  NextHeartbeatTimeInv(b[i], idx, asp.max_clock_ambiguity)
{
  lemma_ConstantsAllConsistent(b, asp.c, i);

  if i > 0
  {
    lemma_ConstantsAllConsistent(b, asp.c, i-1);
    lemma_AssumptionsMakeValidTransition(b, asp.c, i-1);
    lemma_TimeAdvancesBetween(b, asp, i-1, i);
    lemma_NextHeartbeatTimeInv(b, asp, i-1, idx);
    var ps := b[i-1];
    var ps' := b[i];
    var s := ps.replicas[idx].replica;
    var s' := ps'.replicas[idx].replica;
    if !NextHeartbeatTimeInv(b[i], idx, asp.max_clock_ambiguity)
    {
      assert s'.nextHeartbeatTime > s.nextHeartbeatTime;
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i-1, idx);
      lemma_ClockAmbiguityLimitApplies(b, asp, i-1, idx, ios[0]);
      assert false;
    }
  }
}

lemma lemma_ReplicaEventuallySendsHeartbeatForViewWithinWF1Req1(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  sender_idx:int,
  receiver_idx:int,
  start_step:int,
  nextHeartbeatTime:int
  )
  requires LivenessAssumptions(b, asp)
  requires sender_idx in asp.live_quorum
  requires 0 <= receiver_idx < |asp.c.config.replica_ids|
  requires 0 <= start_step
  ensures  var P := ReplicaHasSpecificNextHeartbeatTimeTemporal(b, sender_idx, nextHeartbeatTime);
           var Q := ReplicaSentHeartbeatTemporal(b, sender_idx, receiver_idx);
           sat(start_step, always(imply(P, or(Q, next(P)))))
{
  var P := ReplicaHasSpecificNextHeartbeatTimeTemporal(b, sender_idx, nextHeartbeatTime);
  var Q := ReplicaSentHeartbeatTemporal(b, sender_idx, receiver_idx);
  var t := imply(P, or(Q, next(P)));

  forall i | start_step <= i
    ensures sat(i, t)
  {
    if sat(i, P) && !sat(i, Q) && !sat(i+1, P)
    {
      lemma_ConstantsAllConsistent(b, asp.c, i);
      lemma_ConstantsAllConsistent(b, asp.c, i+1);
      lemma_AssumptionsMakeValidTransition(b, asp.c, i);

      var ps := b[i];
      var ps' := b[i+1];
      var s := ps.replicas[sender_idx].replica;
      var s' := ps'.replicas[sender_idx].replica;
      var es := s.proposer.election_state;
      assert s'.nextHeartbeatTime != s.nextHeartbeatTime;

      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, sender_idx);
      var sent_packets := ExtractSentPacketsFromIos(ios);
      assert |ios| > 0;
      assert ios[0].LIoOpReadClock?;
      assert LReplicaNextReadClockMaybeSendHeartbeat(s, s', SpontaneousClock(ios), sent_packets);
      assert ios[0].t >= s.nextHeartbeatTime;
      var p := LPacket(ps.constants.config.replica_ids[receiver_idx],
                       ps.constants.config.replica_ids[sender_idx],
                       RslMessage_Heartbeat(es.current_view, es.constants.my_index in es.current_view_suspectors, s.executor.ops_complete));
      assert p in sent_packets;
      assert p in ps'.environment.sentPackets;
      assert ReplicaSentHeartbeat(ps, ps', sender_idx, receiver_idx, p);
      assert false;
    }
  }

  TemporalAlways(start_step, t);
}

lemma lemma_ReplicaEventuallySendsHeartbeatForViewWithinWF1Req2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  sender_idx:int,
  receiver_idx:int,
  start_step:int,
  nextHeartbeatTime:int
  )
  requires LivenessAssumptions(b, asp)
  requires sender_idx in asp.live_quorum
  requires 0 <= receiver_idx < |asp.c.config.replica_ids|
  requires 0 <= start_step
  ensures  var P := ReplicaHasSpecificNextHeartbeatTimeTemporal(b, sender_idx, nextHeartbeatTime);
           var Q := ReplicaSentHeartbeatTemporal(b, sender_idx, receiver_idx);
           var Action := ReplicaSchedule(b, sender_idx)[9];
           sat(start_step, always(TemporalWF1RealTimeDelayedImmediateQReq2(P, Q, Action, nextHeartbeatTime + asp.max_clock_ambiguity, PaxosTimeMap(b))))
{
  var P := ReplicaHasSpecificNextHeartbeatTimeTemporal(b, sender_idx, nextHeartbeatTime);
  var Q := ReplicaSentHeartbeatTemporal(b, sender_idx, receiver_idx);
  var Action := ReplicaSchedule(b, sender_idx)[9];
  var t := TemporalWF1RealTimeDelayedImmediateQReq2(P, Q, Action, nextHeartbeatTime + asp.max_clock_ambiguity, PaxosTimeMap(b));

  forall i | start_step <= i
    ensures sat(i, t)
  {
    if sat(i, P) && sat(i, nextafter(Action, nextHeartbeatTime + asp.max_clock_ambiguity, PaxosTimeMap(b))) && !sat(i, Q)
    {
      lemma_ConstantsAllConsistent(b, asp.c, i);
      lemma_ConstantsAllConsistent(b, asp.c, i+1);
      assert SpecificClockReadingRslActionOccurs(b[i], b[i+1], LReplicaNextReadClockMaybeSendHeartbeat, sender_idx);
      var ios:seq<RslIo> :| && RslNextOneReplica(b[i], b[i+1], sender_idx, ios)
                            && SpontaneousIos(ios, 1)
                            && LReplicaNextReadClockMaybeSendHeartbeat(b[i].replicas[sender_idx].replica,
                                                                      b[i+1].replicas[sender_idx].replica,
                                                                      SpontaneousClock(ios), ExtractSentPacketsFromIos(ios));
      lemma_ClockAmbiguityLimitApplies(b, asp, i, sender_idx, ios[0]);
      calc {
        ios[0].t;
        >= b[i+1].environment.time - asp.max_clock_ambiguity;
        >= nextHeartbeatTime;
      }
      var ps := b[i];
      var ps' := b[i+1];
      var s := ps.replicas[sender_idx].replica;
      var s' := ps'.replicas[sender_idx].replica;
      var es := s.proposer.election_state;
      var p := LPacket(ps.constants.config.replica_ids[receiver_idx],
                       ps.constants.config.replica_ids[sender_idx],
                       RslMessage_Heartbeat(es.current_view, es.constants.my_index in es.current_view_suspectors, s.executor.ops_complete));
      assert p in ExtractSentPacketsFromIos(ios);
      assert p in ps'.environment.sentPackets;
      assert ReplicaSentHeartbeat(ps, ps', sender_idx, receiver_idx, p);
      assert false;
    }
  }

  TemporalAlways(start_step, t);
}

lemma lemma_ReplicaEventuallySendsHeartbeatForViewWithin(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  sender_idx:int,
  receiver_idx:int,
  start_step:int
  ) returns (
  step:int,
  p:RslPacket
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires 0 <= processing_sync_start <= start_step
  requires sender_idx in asp.live_quorum
  requires receiver_idx in asp.live_quorum
  ensures  start_step <= step
  ensures  ReplicaSentHeartbeat(b[step], b[step+1], sender_idx, receiver_idx, p)
  ensures  b[step+1].environment.time <= b[start_step].environment.time + TimeForOneReplicaToSendHeartbeat(asp)
{
  lemma_ConstantsAllConsistent(b, asp.c, start_step);
  var nextHeartbeatTime := b[start_step].replicas[sender_idx].replica.nextHeartbeatTime;
  var P := ReplicaHasSpecificNextHeartbeatTimeTemporal(b, sender_idx, nextHeartbeatTime);
  var Q := ReplicaSentHeartbeatTemporal(b, sender_idx, receiver_idx);
  var Action := ReplicaSchedule(b, sender_idx)[9];
  var span := TimeToPerformGenericAction(asp);
  var timefun := PaxosTimeMap(b);

  lemma_ReplicaEventuallySendsHeartbeatForViewWithinWF1Req1(b, asp, sender_idx, receiver_idx, start_step, nextHeartbeatTime);
  lemma_ReplicaEventuallySendsHeartbeatForViewWithinWF1Req2(b, asp, sender_idx, receiver_idx, start_step, nextHeartbeatTime);
  lemma_ReplicaNextPerformsSubactionPeriodically(b, asp, sender_idx, 9);
  lemma_EstablishRequirementsForWF1RealTimeDelayed(b, asp, start_step, Action, span);
  assume TimeNotZeno(timefun);
  step := TemporalWF1RealTimeDelayedImmediateQ(start_step, P, Q, Action, span, nextHeartbeatTime + asp.max_clock_ambiguity, timefun);
  assert start_step <= step;
  p :| ReplicaSentHeartbeat(b[step], b[step+1], sender_idx, receiver_idx, p);
  lemma_NextHeartbeatTimeInv(b, asp, start_step, sender_idx);
  lemma_ConstantsAllConsistent(b, asp.c, step);
  lemma_AssumptionsMakeValidTransition(b, asp.c, step);
  lemma_ClockAmbiguityLimitApplies(b, asp, step, sender_idx, b[step].environment.nextStep.ios[0]);
}

lemma lemma_ProcessingHeartbeatBringsViewUp(
  ps:RslState,
  ps':RslState,
  p:RslPacket,
  idx:int,
  ios:seq<RslIo>
  )
  requires PacketProcessedViaIos(ps, ps', p, idx, ios)
  requires p.msg.RslMessage_Heartbeat?
  requires p.src in ps.replicas[idx].replica.proposer.election_state.constants.all.config.replica_ids
  ensures  BalLeq(p.msg.bal_heartbeat, ps'.replicas[idx].replica.proposer.election_state.current_view)
{
  var s := ps.replicas[idx].replica;
  var s' := ps'.replicas[idx].replica;
  var es := s.proposer.election_state;
  var es' := s'.proposer.election_state;
  assert LProposerProcessHeartbeat(s.proposer, s'.proposer, p, ios[1].t);
  assert ElectionStateProcessHeartbeat(es, es', p, ios[1].t);
  lemma_BalLtProperties();
}
    
lemma lemma_OneLiveReplicaSoonAdvancesAnother(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  start_step:int,
  ahead_idx:int,
  moved_idx:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires 0 <= processing_sync_start <= start_step
  requires ahead_idx in asp.live_quorum
  requires moved_idx in asp.live_quorum
  ensures  0 <= ahead_idx < |b[start_step].replicas|
  ensures  0 <= moved_idx < |b[step].replicas|
  ensures  start_step <= step
  ensures  BalLeq(CurrentViewOfHost(b[start_step], ahead_idx), CurrentViewOfHost(b[step], moved_idx))
  ensures  b[step].environment.time <= b[start_step].environment.time + TimeForOneReplicaToAdvanceAnother(asp, processing_bound)
{
  lemma_ConstantsAllConsistent(b, asp.c, start_step);
  var nextHeartbeatTime := b[start_step].replicas[ahead_idx].replica.nextHeartbeatTime;
  var send_step, p := lemma_ReplicaEventuallySendsHeartbeatForViewWithin(b, asp, processing_sync_start, processing_bound, ahead_idx, moved_idx, start_step);
  lemma_ConstantsAllConsistent(b, asp.c, send_step);
  var view := CurrentViewOfHost(b[send_step], ahead_idx);
  lemma_ViewOfHostMonotonic(b, asp, ahead_idx, start_step, send_step);
  var s := b[send_step].replicas[ahead_idx].replica;
  assert BalLeq(CurrentViewOfHost(b[start_step], ahead_idx), view);
  assert p.msg.bal_heartbeat == view;
  var processing_step, ios := lemma_PacketSentToIndexProcessedByIt(b, asp, processing_sync_start, processing_bound, send_step, moved_idx, p);
  lemma_ConstantsAllConsistent(b, asp.c, processing_step);
  lemma_ProcessingHeartbeatBringsViewUp(b[processing_step], b[processing_step+1], p, moved_idx, ios);
  lemma_BalLtProperties();
  step := processing_step + 1;
}

lemma lemma_OneLiveReplicaSoonAdvancesAnotherForever(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  start_step:int,
  ahead_idx:int,
  moved_idx:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires 0 <= processing_sync_start <= start_step
  requires ahead_idx in asp.live_quorum
  requires moved_idx in asp.live_quorum
  ensures  0 <= ahead_idx < |b[start_step].replicas|
  ensures  0 <= moved_idx < |b[step].replicas|
  ensures  BalLeq(CurrentViewOfHost(b[start_step], ahead_idx), CurrentViewOfHost(b[step], moved_idx))
  ensures  start_step <= step
  ensures  b[step].environment.time <= b[start_step].environment.time + TimeForOneReplicaToAdvanceAnother(asp, processing_bound)
  ensures  sat(step, always(HostReachedViewTemporal(b, moved_idx, CurrentViewOfHost(b[start_step], ahead_idx))))
{
  step := lemma_OneLiveReplicaSoonAdvancesAnother(b, asp, processing_sync_start, processing_bound, start_step, ahead_idx, moved_idx);
  forall j | step <= j
    ensures sat(j, HostReachedViewTemporal(b, moved_idx, CurrentViewOfHost(b[start_step], ahead_idx)))
  {
    lemma_ConstantsAllConsistent(b, asp.c, j);
    lemma_ViewOfHostMonotonic(b, asp, moved_idx, step, j);
  }
  TemporalAlways(step, HostReachedViewTemporal(b, moved_idx, CurrentViewOfHost(b[start_step], ahead_idx)));
}

lemma lemma_OneLiveReplicaSoonAdvancesSomeForever(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  start_step:int,
  ahead_idx:int,
  moved_indices:set<int>
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires 0 <= processing_sync_start <= start_step
  requires ahead_idx in asp.live_quorum
  requires moved_indices <= asp.live_quorum
  ensures  0 <= ahead_idx < |b[start_step].replicas|
  ensures  start_step <= step
  ensures  forall moved_idx :: moved_idx in moved_indices
                       ==> sat(step, always(HostReachedViewTemporal(b, moved_idx, CurrentViewOfHost(b[start_step], ahead_idx))))
  ensures  b[step].environment.time <= b[start_step].environment.time + TimeForOneReplicaToAdvanceAnother(asp, processing_bound)
  decreases |moved_indices|
{
  lemma_ConstantsAllConsistent(b, asp.c, start_step);
  if |moved_indices| == 0
  {
    step := start_step;
  }
  else
  {
    var moved_idx :| moved_idx in moved_indices;
    var other_indices := moved_indices - {moved_idx};
    var first_step := lemma_OneLiveReplicaSoonAdvancesSomeForever(b, asp, processing_sync_start, processing_bound, start_step, ahead_idx, other_indices);
    var second_step := lemma_OneLiveReplicaSoonAdvancesAnotherForever(b, asp, processing_sync_start, processing_bound, start_step, ahead_idx, moved_idx);
    var view := CurrentViewOfHost(b[start_step], ahead_idx);
    if second_step >= first_step
    {
      step := second_step;
      forall midx | midx in moved_indices
        ensures sat(step, always(HostReachedViewTemporal(b, midx, view)))
      {
        if midx != moved_idx
        {
          Lemma_AlwaysImpliesLaterAlways(first_step, step, HostReachedViewTemporal(b, midx, view));
        }
      }
    }
    else
    {
      step := first_step;
      forall midx | midx in moved_indices
        ensures sat(step, always(HostReachedViewTemporal(b, midx, view)))
      {
        if midx == moved_idx
        {
          Lemma_AlwaysImpliesLaterAlways(second_step, step, HostReachedViewTemporal(b, midx, view));
        }
      }
    }
  }
}
    
lemma lemma_OneLiveReplicaSoonAdvancesAllForever(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  start_step:int,
  ahead_idx:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires 0 <= processing_sync_start <= start_step
  requires ahead_idx in asp.live_quorum
  ensures  0 <= ahead_idx < |b[start_step].replicas|
  ensures  start_step <= step
  ensures  forall moved_idx :: moved_idx in asp.live_quorum
                       ==> sat(step, always(HostReachedViewTemporal(b, moved_idx, CurrentViewOfHost(b[start_step], ahead_idx))))
  ensures  b[step].environment.time <= b[start_step].environment.time + TimeForOneReplicaToAdvanceAnother(asp, processing_bound)
{
  step := lemma_OneLiveReplicaSoonAdvancesSomeForever(b, asp, processing_sync_start, processing_bound, start_step, ahead_idx, asp.live_quorum);
}

}
