include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "ViewChange.i.dfy"
include "MaxBallot.i.dfy"
include "../CommonProof/Actions.i.dfy"
include "../CommonProof/PacketSending.i.dfy"
include "../CommonProof/MaxBallotISent1a.i.dfy"

module LivenessProof__MaxBalReflected_i {

import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Executor_i
import opened LiveRSL__Message_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__MaxBallot_i
import opened LivenessProof__MaxBallotISent1a_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__ViewChange_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened CommonProof__PacketSending_i
import opened CommonProof__MaxBallotISent1a_i
import opened Temporal__Temporal_s
import opened Collections__Seqs_i
import opened Environment_s

predicate MaxBalReflectedInvariant(
    ps:RslState
    )
{
  && (forall idx {:trigger PrimaryHasReachedState2OfBallot(ps, ps.replicas[idx].replica.executor.max_bal_reflected)}
       :: 0 <= idx < |ps.replicas| ==> PrimaryHasReachedState2OfBallot(ps, ps.replicas[idx].replica.executor.max_bal_reflected))
  && (forall p {:trigger p.msg.RslMessage_AppStateSupply?}
       :: p in ps.environment.sentPackets && p.src in ps.constants.config.replica_ids && p.msg.RslMessage_AppStateSupply?
         ==> PrimaryHasReachedState2OfBallot(ps, p.msg.bal_state_supply))
}

lemma lemma_IfMaxBalReflectedChangedThenInvariantStillHolds(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires MaxBalReflectedInvariant(b[i])
  requires 0 <= idx < |b[i].replicas|
  requires 0 <= idx < |b[i+1].replicas|
  requires b[i+1].replicas[idx].replica.executor.max_bal_reflected != b[i].replicas[idx].replica.executor.max_bal_reflected
  ensures  PrimaryHasReachedState2OfBallot(b[i+1], b[i+1].replicas[idx].replica.executor.max_bal_reflected)
{
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i+1);
  lemma_AssumptionsMakeValidTransition(b, asp.c, i);

  var max_bal_reflected := b[i].replicas[idx].replica.executor.max_bal_reflected;
  var max_bal_reflected' := b[i+1].replicas[idx].replica.executor.max_bal_reflected;
  assert max_bal_reflected' != max_bal_reflected;

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, idx);
  var nextActionIndex := b[i].replicas[idx].nextActionIndex;
  if nextActionIndex == 0
  {
    assert LExecutorProcessAppStateSupply(b[i].replicas[idx].replica.executor, b[i+1].replicas[idx].replica.executor, ios[0].r);
    var p := ios[0].r;
    lemma_PacketProcessedImpliesPacketSent(b[i], b[i+1], idx, ios, p);
    assert p in b[i].environment.sentPackets && p.src in b[i].constants.config.replica_ids && p.msg.RslMessage_AppStateSupply?;
    assert PrimaryHasReachedState2OfBallot(b[i], p.msg.bal_state_supply);
    lemma_PrimaryHasReachedState2OfBallotMaintainedByOneStep(b, asp.c, i, p.msg.bal_state_supply);
    assert PrimaryHasReachedState2OfBallot(b[i+1], p.msg.bal_state_supply);
    assert max_bal_reflected' == p.msg.bal_state_supply;
    assert PrimaryHasReachedState2OfBallot(b[i+1], max_bal_reflected');
  }
  else if nextActionIndex == 6
  {
    assert LReplicaNextSpontaneousMaybeExecute(b[i].replicas[idx].replica, b[i+1].replicas[idx].replica, ExtractSentPacketsFromIos(ios));
    assert b[i].replicas[idx].replica.executor.next_op_to_execute.OutstandingOpKnown?;
    lemma_ExecutorNextOpToExecuteBallotShowsPrimaryReachedState2(b, asp.c, i, idx);
    lemma_PrimaryHasReachedState2OfBallotMaintainedByOneStep(b, asp.c, i, b[i].replicas[idx].replica.executor.next_op_to_execute.bal);
    assert max_bal_reflected' == b[i].replicas[idx].replica.executor.next_op_to_execute.bal;
    assert PrimaryHasReachedState2OfBallot(b[i+1], max_bal_reflected');
  }
  else
  {
    assert false;
  }
}

lemma lemma_MaxBalReflectedInvariantHolds(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  ensures  MaxBalReflectedInvariant(b[i])
{
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, asp.c, i-1);
    lemma_ConstantsAllConsistent(b, asp.c, i);
    lemma_AssumptionsMakeValidTransition(b, asp.c, i-1);
    lemma_MaxBalReflectedInvariantHolds(b, asp, i-1);

    forall idx | 0 <= idx < |b[i].replicas|
      ensures PrimaryHasReachedState2OfBallot(b[i], b[i].replicas[idx].replica.executor.max_bal_reflected)
    {
      var max_bal_reflected := b[i-1].replicas[idx].replica.executor.max_bal_reflected;
      var max_bal_reflected' := b[i].replicas[idx].replica.executor.max_bal_reflected;

      if max_bal_reflected' == max_bal_reflected
      {
        assert 0 <= idx < |b[i-1].replicas|;
        assert PrimaryHasReachedState2OfBallot(b[i-1], max_bal_reflected);
        lemma_PrimaryHasReachedState2OfBallotMaintainedByOneStep(b, asp.c, i-1, max_bal_reflected);
      }
      else
      {
        lemma_IfMaxBalReflectedChangedThenInvariantStillHolds(b, asp, i-1, idx);
      }
    }
    
    forall p | p in b[i].environment.sentPackets && p.src in b[i].constants.config.replica_ids && p.msg.RslMessage_AppStateSupply?
      ensures PrimaryHasReachedState2OfBallot(b[i], p.msg.bal_state_supply)
    {
      if p in b[i-1].environment.sentPackets
      {
        assert PrimaryHasReachedState2OfBallot(b[i-1], p.msg.bal_state_supply);
        lemma_PrimaryHasReachedState2OfBallotMaintainedByOneStep(b, asp.c, i-1, p.msg.bal_state_supply);
      }
      else
      {
        var idx, ios := lemma_ActionThatSendsAppStateSupplyIsProcessAppStateRequest(b[i-1], b[i], p);
        var s := b[i-1].replicas[idx].replica.executor;
        assert LExecutorProcessAppStateRequest(b[i-1].replicas[idx].replica.executor, b[i].replicas[idx].replica.executor, ios[0].r, [p]);
        Lemma_IdenticalSingletonSequencesHaveIdenticalElement(p, LPacket(ios[0].r.src, asp.c.config.replica_ids[idx], RslMessage_AppStateSupply(s.max_bal_reflected, s.ops_complete, s.app, s.reply_cache)));
        assert 0 <= idx < |b[i-1].replicas|;
        assert PrimaryHasReachedState2OfBallot(b[i-1], s.max_bal_reflected);
        assert p.msg.bal_state_supply == s.max_bal_reflected;
        lemma_PrimaryHasReachedState2OfBallotMaintainedByOneStep(b, asp.c, i-1, p.msg.bal_state_supply);
      }
      }
  }
}

lemma lemma_MaxBalReflectedLeqCurrentView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  view:Ballot,
  idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires sat(i, NoReplicaBeyondViewTemporal(b, view))
  requires 0 <= idx < |b[i].replicas|
  ensures  BalLeq(b[i].replicas[idx].replica.executor.max_bal_reflected, view)
{
  lemma_NoReplicaBeyondViewImpliesNoMaxBallotISent1aBeyondView(b, asp, i, view);
  lemma_MaxBalReflectedInvariantHolds(b, asp, i);
  var max_bal_reflected := b[i].replicas[idx].replica.executor.max_bal_reflected;
  assert PrimaryHasReachedState2OfBallot(b[i], max_bal_reflected);
}

}
