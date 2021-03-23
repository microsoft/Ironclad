include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "StablePeriod.i.dfy"
include "PacketHandling.i.dfy"
include "MaxBalReflected.i.dfy"
include "Phase2Invariants.i.dfy"
include "../CommonProof/LogTruncationPoint.i.dfy"
include "../CommonProof/Actions.i.dfy"
include "../../../Common/Logic/Temporal/Sets.i.dfy"

module LivenessProof__Catchup_i {

import opened LiveRSL__Broadcast_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Message_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__PacketHandling_i
import opened LivenessProof__MaxBalReflected_i
import opened LivenessProof__Phase2Invariants_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened CommonProof__LogTruncationPoint_i
import opened Temporal__Rules_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Temporal__Sets_i
import opened Environment_s
import opened Collections__Maps2_s

lemma{:timeLimitMultiplier 2} lemma_EventuallySpecificLiveReplicaCaughtUp(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  idx:int,
  h:Phase2Params
  ) returns (
  step:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires idx in asp.live_quorum
  ensures  h.start_step + 1 <= step
  ensures  sat(step, beforeabsolutetime(or(ReplicaCaughtUpTemporal(b, idx, h.log_truncation_point), not(NoReplicaBeyondViewTemporal(b, h.view))),
                                        b[h.start_step+1].environment.time + h.processing_bound * 3, PaxosTimeMap(b)))
{
  var f := PaxosTimeMap(b);
  var x := ReplicaCaughtUpTemporal(b, idx, h.log_truncation_point);
  var z := NoReplicaBeyondViewTemporal(b, h.view);
  var deadline := b[h.start_step+1].environment.time + h.processing_bound * 3;

  lemma_ConstantsAllConsistent(b, asp.c, h.start_step);
  var s1 := b[h.start_step].replicas[h.view.proposer_id].replica.proposer;
  assert s1.current_state == 1;
  assert LBroadcastToEveryone(b[h.start_step].constants.config, h.view.proposer_id, RslMessage_StartingPhase2(h.view, h.log_truncation_point), ExtractSentPacketsFromIos(h.ios));
    
  var p := LPacket(asp.c.config.replica_ids[idx], asp.c.config.replica_ids[h.view.proposer_id], RslMessage_StartingPhase2(s1.max_ballot_i_sent_1a, h.log_truncation_point));
  assert p in ExtractSentPacketsFromIos(h.ios);
  var first_step, ios2 := lemma_PacketSentToIndexProcessedByIt(b, asp, h.start_step, h.processing_bound, h.start_step, idx, p);

  lemma_ConstantsAllConsistent(b, asp.c, first_step);
  var s2 := b[first_step].replicas[idx].replica.executor;
  if s2.ops_complete >= h.log_truncation_point
  {
    step := first_step;
    assert sat(step, beforeabsolutetime(x, deadline, f));
    return;
  }

  assert LBroadcastToEveryone(s2.constants.all.config, s2.constants.my_index, RslMessage_AppStateRequest(p.msg.bal_2, h.log_truncation_point), ExtractSentPacketsFromIos(ios2));
  var p2 := LPacket(asp.c.config.replica_ids[h.king_idx], asp.c.config.replica_ids[idx], RslMessage_AppStateRequest(p.msg.bal_2, h.log_truncation_point));
  assert p2 in ExtractSentPacketsFromIos(ios2);

  var second_step, ios3 := lemma_PacketSentToIndexProcessedByIt(b, asp, h.start_step, h.processing_bound, first_step, h.king_idx, p2);
  lemma_ConstantsAllConsistent(b, asp.c, second_step);
  var s3 := b[second_step].replicas[h.king_idx].replica.executor;
  lemma_OpsCompleteMonotonic(b, asp.c, h.start_step+1, second_step, h.king_idx);
  assert s3.ops_complete >= h.log_truncation_point;

  assert p.msg.bal_2 == h.view;

  if sat(second_step, not(NoReplicaBeyondViewTemporal(b, h.view)))
  {
    step := second_step;
    assert sat(step, beforeabsolutetime(not(z), deadline, f));
    return;
  }

  lemma_MaxBalReflectedLeqCurrentView(b, asp, second_step, h.view, h.king_idx);
  assert BalLeq(s3.max_bal_reflected, h.view);
  var p3 := LPacket(asp.c.config.replica_ids[idx], asp.c.config.replica_ids[h.king_idx], RslMessage_AppStateSupply(s3.max_bal_reflected, s3.ops_complete, s3.app, s3.reply_cache));
  assert p3 in ExtractSentPacketsFromIos(ios3);

  var third_step, ios4 := lemma_PacketSentToIndexProcessedByIt(b, asp, h.start_step, h.processing_bound, second_step, idx, p3);
  lemma_ConstantsAllConsistent(b, asp.c, third_step);
  var s4' := b[third_step+1].replicas[idx].replica.executor;
  assert s4'.ops_complete >= h.log_truncation_point;

  step := third_step+1;
}

lemma lemma_ReplicaCaughtUpIsStable(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int,
  opn:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  ensures  sat(i, imply(ReplicaCaughtUpTemporal(b, idx, opn), always(ReplicaCaughtUpTemporal(b, idx, opn))))
{
  if sat(i, ReplicaCaughtUpTemporal(b, idx, opn))
  {
    forall j | i <= j
      ensures sat(j, ReplicaCaughtUpTemporal(b, idx, opn))
    {
      lemma_OpsCompleteMonotonic(b, asp.c, i, j, idx);
    }
    TemporalAlways(i, ReplicaCaughtUpTemporal(b, idx, opn));
  }
}

lemma lemma_EventuallyAllLiveReplicasCaughtUp(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params
  )
  requires Phase2StableWithRequest(b, asp, h)
  ensures  sat(h.start_step+1, eventuallywithin(or(always(andset(AllReplicasCaughtUpTemporalSet(b, asp.live_quorum, h.log_truncation_point))),
                                                not(NoReplicaBeyondViewTemporal(b, h.view))),
                                                h.processing_bound * 3, PaxosTimeMap(b)))
{
  var xs := AllReplicasCaughtUpTemporalSet(b, asp.live_quorum, h.log_truncation_point);
  var y := not(NoReplicaBeyondViewTemporal(b, h.view));
  var t := h.processing_bound * 3;
  var f := PaxosTimeMap(b);
  forall x | x in xs
    ensures sat(h.start_step + 1, eventuallywithin(or(always(x), y), t, f))
  {
    var idx :| idx in asp.live_quorum && x == ReplicaCaughtUpTemporal(b, idx, h.log_truncation_point);
    var step := lemma_EventuallySpecificLiveReplicaCaughtUp(b, asp, idx, h);
    assert sat(step, or(x, y));
    lemma_ReplicaCaughtUpIsStable(b, asp, step, idx, h.log_truncation_point);
    assert sat(step, or(always(x), y));
    TemporalEventually(h.start_step+1, step, beforeabsolutetime(or(always(x), y), f[h.start_step+1] + t, f));
  }
  Lemma_EventuallyAlwaysWithinEachOrAlternativeImpliesEventuallyAlwaysWithinAllOrAlternative(h.start_step + 1, xs, y, t, f);
}

lemma lemma_EventuallyAllLiveReplicasReadyForFirstOperation(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params
  ) returns (
  step:int
  )
  requires Phase2StableWithRequest(b, asp, h)
  ensures  h.start_step + 1 <= step
  ensures  b[step].environment.time <= b[h.start_step + 1].environment.time + h.processing_bound * 3
  ensures  sat(step, or(AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, h.log_truncation_point),
                        not(NoReplicaBeyondViewTemporal(b, h.view))))
{
  var t := h.processing_bound * 3;
  var f := PaxosTimeMap(b);
  var xs := AllReplicasCaughtUpTemporalSet(b, asp.live_quorum, h.log_truncation_point);
  var y := AllLiveReplicasReadyForNextOperationTemporal(b, asp.live_quorum, h.view, h.log_truncation_point);
  var z := NoReplicaBeyondViewTemporal(b, h.view);
  lemma_EventuallyAllLiveReplicasCaughtUp(b, asp, h);
  step := TemporalDeduceFromEventual(h.start_step + 1, beforeabsolutetime(or(always(andset(xs)), not(NoReplicaBeyondViewTemporal(b, h.view))),
                                                                          f[h.start_step + 1] + t, f));
  lemma_ConstantsAllConsistent(b, asp.c, step);
  if sat(step, z)
  {
    forall idx | idx in asp.live_quorum
      ensures ReplicaCaughtUp(b[step], idx, h.log_truncation_point)
    {
      var x := ReplicaCaughtUpTemporal(b, idx, h.log_truncation_point);
      assert x in xs;
      assert sat(step, or(always(andset(xs)), not(z)));
      assert sat(step, always(andset(xs)));
      TemporalDeduceFromAlways(step, step, andset(xs));
      assert sat(step, x);
    }
    var s := b[step].replicas[h.view.proposer_id].replica;
    lemma_LogTruncationPointMonotonic(b, asp.c, h.start_step + 1, step, h.view.proposer_id);
    assert s.acceptor.log_truncation_point >= h.log_truncation_point;
    lemma_NextOperationNumberToProposeIncreasesInPhase2(b, asp, h, h.start_step + 1, step);
    assert s.proposer.next_operation_number_to_propose >= h.log_truncation_point;
    assert sat(step, y);
  }
  assert sat(step, or(y, not(z)));
}
    
}
