include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "ViewPersistence.i.dfy"
include "Phase1bCont.i.dfy"
include "RequestQueue.i.dfy"
include "../CommonProof/Constants.i.dfy"
include "../CommonProof/Actions.i.dfy"
include "../CommonProof/LogTruncationPoint.i.dfy"
include "../../../../Libraries/Math/mul.i.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"

module LivenessProof__Phase2Start_i {

import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__PacketHandling_i
import opened LivenessProof__Phase1b_i
import opened LivenessProof__Phase1bCont_i
import opened LivenessProof__RealTime_i
import opened LivenessProof__RequestQueue_i
import opened LivenessProof__RoundRobin_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__ViewAdvance_i
import opened LivenessProof__ViewPersistence_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened CommonProof__LogTruncationPoint_i
import opened Math__mul_i
import opened Temporal__Rules_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Temporal__Time_i
import opened Environment_s
import opened Collections__Maps2_s
import opened Common__UpperBound_s

lemma lemma_EventuallyPhase2StableWithRequestHelper(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  primary_idx:int,
  base_duration:int,
  per_request_duration:int
  ) returns (
  start_step:int,
  ahead_idx:int,
  step:int,
  view:Ballot,
  num_requests:int,
  duration:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires primary_idx in asp.live_quorum
  requires base_duration >= 0
  requires per_request_duration >= 0
  ensures  processing_sync_start <= step
  ensures  view.proposer_id == primary_idx
  ensures  LeqUpperBound(view.seqno, asp.c.params.max_integer_val)
  ensures  num_requests > 0
  ensures  duration == base_duration + num_requests * per_request_duration
  ensures  processing_sync_start <= start_step <= step
  ensures  sat(start_step, StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx))
  ensures  sat(start_step, always(RequestInFirstNTemporal(b, view.proposer_id, asp.persistent_request, num_requests)))
  ensures  sat(step, always(untilabsolutetime(NoReplicaBeyondViewTemporal(b, view), b[step+1].environment.time + duration, PaxosTimeMap(b))))
  ensures  !PrimaryInState2(b[step], view)
  ensures  PrimaryInState2(b[step+1], view)
{
  var t := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp) * 2 + processing_bound * 2;
  var f := PaxosTimeMap(b);
  var full_duration:int;

  view, start_step, ahead_idx, num_requests, full_duration := lemma_EventuallyBallotStableWithRequest(b, asp, processing_sync_start, processing_bound, primary_idx, t + base_duration, per_request_duration);

  lemma_mul_nonnegative(num_requests, per_request_duration);

  var x := StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx);
  var y := PrimaryInState2Temporal(b, view);
  var z := NoReplicaBeyondViewTemporal(b, view);
  duration := base_duration + num_requests * per_request_duration;

  lemma_IfPacketProcessingSynchronousThenAlways(b, asp, processing_sync_start, start_step, processing_bound);
  lemma_StablePeriodStartedLeadsToPrimaryEnteringPhase2(b, asp, start_step, processing_bound, view, ahead_idx);
  TemporalDeduceFromAlways(start_step, start_step, imply(x, or(eventuallynextwithin(and(not(y), next(y)), t, f), eventuallywithin(not(z), t, f))));
  assert sat(start_step, x);
  assert sat(start_step, or(eventuallynextwithin(and(not(y), next(y)), t, f), eventuallywithin(not(z), t, f)));

  if sat(start_step, eventuallywithin(not(z), t, f))
  {
    var i := TemporalDeduceFromEventual(start_step, beforeabsolutetime(not(z), f[start_step] + t, f));
    TemporalDeduceFromAlways(start_step, i, untilabsolutetime(z, f[start_step] + full_duration, f));
    assert full_duration >= t;
    assert false;
  }

  assert sat(start_step, eventuallynextwithin(and(not(y), next(y)), t, f));
  step := TemporalDeduceFromEventual(start_step, nextbefore(and(not(y), next(y)), f[start_step]+t, f));
  Lemma_AlwaysImpliesLaterAlways(start_step, step, untilabsolutetime(z, f[start_step] + full_duration, f));

  assert f[step+1] + duration <= f[start_step] + full_duration;
  lemma_TimeMonotonicFromInvariantHolds(b, asp, step);
  Lemma_AlwaysUntilAbsoluteTimeImpliesAlwaysUntilEarlierTime(step, z, f[start_step] + full_duration, f[step+1] + duration, f);
}

lemma lemma_EventuallyPhase2StableWithRequest(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  primary_idx:int,
  base_duration:int,
  per_request_duration:int
  ) returns (
  h:Phase2Params
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires primary_idx in asp.live_quorum
  requires base_duration >= 0
  requires per_request_duration >= 0
  ensures  h.view.proposer_id == primary_idx
  ensures  LeqUpperBound(h.view.seqno, asp.c.params.max_integer_val)
  ensures  h.base_duration == base_duration
  ensures  h.per_request_duration == per_request_duration
  ensures  h.processing_bound == processing_bound
  ensures  Phase2StableWithRequest(b, asp, h)
{
  var stable_start_step, ahead_idx, start_step, view, num_requests, duration := lemma_EventuallyPhase2StableWithRequestHelper(b, asp, processing_sync_start, processing_bound, primary_idx, base_duration, per_request_duration);

  lemma_ConstantsAllConsistent(b, asp.c, start_step);

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, start_step, primary_idx);
  var log_truncation_point := b[start_step].replicas[primary_idx].replica.acceptor.log_truncation_point;
  var king_idx := lemma_AlwaysSomeReplicaInQuorumBeyondLogTruncationPoint(b, asp.c, start_step+1, primary_idx, asp.live_quorum);

  lemma_RequestInFirstNOfRequestQueueDuringPhase1(b, asp, start_step, stable_start_step, view, ahead_idx, asp.persistent_request, num_requests);

  h := Phase2Params(start_step, duration, base_duration, per_request_duration, processing_bound, view, log_truncation_point, king_idx, num_requests, ios);
  lemma_IfPacketProcessingSynchronousThenAlways(b, asp, processing_sync_start, start_step, processing_bound);

  Lemma_AlwaysImpliesLaterAlways(start_step, start_step + 1, untilabsolutetime(NoReplicaBeyondViewTemporal(b, view), b[h.start_step + 1].environment.time + h.duration, PaxosTimeMap(b)));
}
    
}
