include "Invariants.i.dfy"
include "RealTime.i.dfy"
include "../CommonProof/Actions.i.dfy"

module LivenessProof__GenericInvariants_i {
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Environment_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__RealTime_i
import opened CommonProof__Actions_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened Temporal__Temporal_s
import opened Environment_s
import opened Collections__Maps2_s
import opened Common__UpperBound_s

lemma lemma_ProposerBatchTimerNeverTooFarInFuture(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires idx in asp.live_quorum
  ensures  0 <= idx < |b[i].replicas|
  ensures  var s := b[i].replicas[idx].replica.proposer;
           s.incomplete_batch_timer.IncompleteBatchTimerOn?
           ==> s.incomplete_batch_timer.when <= b[i].environment.time + asp.max_clock_ambiguity + asp.c.params.max_batch_delay
  decreases i
{
  lemma_ConstantsAllConsistent(b, asp.c, i);
    
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, asp.c, i-1);
    lemma_ConstantsAllConsistent(b, asp.c, i);

    var s := b[i-1].replicas[idx].replica.proposer;
    var s' := b[i].replicas[idx].replica.proposer;

    lemma_ProposerBatchTimerNeverTooFarInFuture(b, asp, i-1, idx);

    if s'.incomplete_batch_timer.IncompleteBatchTimerOn?
    {
      if s'.incomplete_batch_timer == s.incomplete_batch_timer
      {
        lemma_TimeAdvancesBetween(b, asp, i-1, i);
      }
      else
      {
        var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i-1, idx);
        assert LReplicaNextReadClockMaybeNominateValueAndSend2a(b[i-1].replicas[idx].replica, b[i].replicas[idx].replica,
                                                                SpontaneousClock(ios), ExtractSentPacketsFromIos(ios));
        assert ios[0].LIoOpReadClock?;
        lemma_ClockAmbiguityLimitApplies(b, asp, i-1, idx, ios[0]);
        assert ios[0].t <= b[i].environment.time + asp.max_clock_ambiguity;
        assert s'.incomplete_batch_timer.when == UpperBoundedAddition(ios[0].t, asp.c.params.max_batch_delay, asp.c.params.max_integer_val);
      }
    }
  }
}

lemma lemma_HeartbeatTimerNeverTooFarInFuture(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires idx in asp.live_quorum
  ensures  0 <= idx < |b[i].replicas|
  ensures  var s := b[i].replicas[idx].replica;
           s.nextHeartbeatTime <= b[i].environment.time + asp.max_clock_ambiguity + asp.c.params.heartbeat_period
  decreases i
{
  lemma_ConstantsAllConsistent(b, asp.c, i);
    
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, asp.c, i-1);
    lemma_ConstantsAllConsistent(b, asp.c, i);

    var s := b[i-1].replicas[idx].replica;
    var s' := b[i].replicas[idx].replica;

    lemma_HeartbeatTimerNeverTooFarInFuture(b, asp, i-1, idx);

    if s'.nextHeartbeatTime == s.nextHeartbeatTime
    {
      lemma_TimeAdvancesBetween(b, asp, i-1, i);
    }
    else
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i-1, idx);
      assert ios[0].LIoOpReadClock?;
      lemma_ClockAmbiguityLimitApplies(b, asp, i-1, idx, ios[0]);
      assert ios[0].t <= b[i].environment.time + asp.max_clock_ambiguity;
      assert s'.nextHeartbeatTime == UpperBoundedAddition(ios[0].t, asp.c.params.heartbeat_period, asp.c.params.max_integer_val);
    }
  }
}

lemma lemma_NextCheckpointedOperationAlwaysSizeOfReplicas(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  ensures  |b[i].replicas[idx].replica.acceptor.last_checkpointed_operation| == |c.config.replica_ids|
{
  if i == 0
  {
    return;
  }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_NextCheckpointedOperationAlwaysSizeOfReplicas(b, c, i-1, idx);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);
}

}
