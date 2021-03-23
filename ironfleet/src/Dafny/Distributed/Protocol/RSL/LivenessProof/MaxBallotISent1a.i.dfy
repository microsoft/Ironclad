include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "ViewChange.i.dfy"
include "../CommonProof/Actions.i.dfy"

module LivenessProof__MaxBallotISent1a_i {

import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Environment_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__ViewChange_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened Temporal__Temporal_s

lemma lemma_MaxBallotISent1aLeqView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  ensures  BalLeq(b[i].replicas[idx].replica.proposer.max_ballot_i_sent_1a, b[i].replicas[idx].replica.proposer.election_state.current_view)
  decreases i
{
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, asp.c, i-1);
    lemma_ConstantsAllConsistent(b, asp.c, i);
    lemma_MaxBallotISent1aLeqView(b, asp, i-1, idx);
    lemma_AssumptionsMakeValidTransition(b, asp.c, i-1);
    lemma_BalLtProperties();

    if b[i].replicas[idx].replica.proposer.max_ballot_i_sent_1a != b[i-1].replicas[idx].replica.proposer.max_ballot_i_sent_1a
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i-1, idx);
    }
    else
    {
      lemma_ViewOfHostMonotonic(b, asp, idx, i-1, i);
    }
  }
}

lemma lemma_NoReplicaBeyondViewImpliesNoMaxBallotISent1aBeyondView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires NoReplicaBeyondView(b[i], view)
  ensures  NoMaxBallotISent1aBeyondView(b[i], view)
{
  forall idx | 0 <= idx < |b[i].replicas|
    ensures BalLeq(b[i].replicas[idx].replica.proposer.max_ballot_i_sent_1a, view)
  {
    assert BalLeq(CurrentViewOfHost(b[i], idx), view);
    lemma_MaxBallotISent1aLeqView(b, asp, i, idx);
  }
}

}
