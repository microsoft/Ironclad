include "../DistributedSystem.i.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"
include "Assumptions.i.dfy"

module CommonProof__Constants_i {
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Constants_i
import opened Temporal__Temporal_s
import opened Temporal__Rules_i
import opened Temporal__Heuristics_i
import opened CommonProof__Assumptions_i

///////////////////////////////
// INVARIANTS
///////////////////////////////

predicate ConstantsAllConsistentInv(ps:RslState)
{
  && |ps.constants.config.replica_ids| == |ps.replicas|
  && forall idx :: 0 <= idx < |ps.constants.config.replica_ids| ==>
        var s := ps.replicas[idx].replica;
        && s.constants.my_index == idx
        && s.constants.all == ps.constants
        && s.proposer.constants == s.constants
        && s.proposer.election_state.constants == s.constants
        && s.acceptor.constants == s.constants
        && s.learner.constants == s.constants
        && s.executor.constants == s.constants
}

///////////////////////////////
// INVARIANT LEMMAS
///////////////////////////////

lemma lemma_AssumptionsMakeValidTransition(
  b:Behavior<RslState>,
  c:LConstants,
  i:int
  )
  requires IsValidBehaviorPrefix(b, c, i+1)
  requires 0 <= i
  ensures  RslNext(b[i], b[i+1])
{
}

lemma lemma_ReplicasSize(
  b:Behavior<RslState>,
  c:LConstants,
  i:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  ensures  |c.config.replica_ids| == |b[i].replicas|
{
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);
    lemma_ReplicasSize(b, c, i-1);
  }
}

lemma lemma_ReplicaInState(
  b:Behavior<RslState>,
  c:LConstants,
  replica_index:int,
  i:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= replica_index < |c.config.replica_ids|
  ensures  0 <= replica_index < |b[i].replicas|
{
  lemma_ReplicasSize(b, c, i);
}

lemma lemma_ConstantsAllConsistent(
  b:Behavior<RslState>,
  c:LConstants,
  i:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  ensures  b[i].constants == c
  ensures  ConstantsAllConsistentInv(b[i])
{
  TemporalAssist();

  if i > 0
  {
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);
  }
}

lemma lemma_ReplicaConstantsAllConsistent(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas| || 0 <= idx < |c.config.replica_ids| || 0 <= idx < |b[i].constants.config.replica_ids|
  ensures  b[i].constants == c
  ensures  |b[i].constants.config.replica_ids| == |b[i].replicas|
  ensures  var s := b[i].replicas[idx].replica;
           && s.constants.my_index == idx
           && s.constants.all == b[i].constants
           && s.proposer.constants == s.constants
           && s.proposer.election_state.constants == s.constants
           && s.acceptor.constants == s.constants
           && s.learner.constants == s.constants
           && s.executor.constants == s.constants
{
  lemma_ConstantsAllConsistent(b, c, i);
}

}
