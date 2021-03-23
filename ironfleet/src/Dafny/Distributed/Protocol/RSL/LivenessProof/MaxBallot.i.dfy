include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "ViewChange.i.dfy"
include "MaxBallotISent1a.i.dfy"
include "../CommonProof/Actions.i.dfy"
include "../CommonProof/MaxBallot.i.dfy"
include "../CommonProof/PacketSending.i.dfy"

module LivenessProof__MaxBallot_i {

import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__MaxBallotISent1a_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__ViewChange_i
import opened CommonProof__Actions_i
import opened CommonProof__MaxBallot_i
import opened CommonProof__PacketSending_i
import opened Temporal__Temporal_s

lemma lemma_WhenStablePeriodStartsEveryMaxBalPrecedesView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int,
  ahead_idx:int,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  requires StablePeriodStarted(b[i], asp.live_quorum, view, ahead_idx)
  ensures  BalLt(b[i].replicas[idx].replica.acceptor.max_bal, view)
{
  var max_bal := b[i].replicas[idx].replica.acceptor.max_bal;
  lemma_MaxBalLeqMaxBallotPrimarySent1a(b, asp.c, i, idx);
  assert BalLt(b[i].replicas[max_bal.proposer_id].replica.proposer.max_ballot_i_sent_1a, view); // TRIGGER
}

lemma lemma_DuringStablePeriodNoMaxBalBeyondView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  requires NoMaxBallotISent1aBeyondView(b[i], view)
  ensures  BalLeq(b[i].replicas[idx].replica.acceptor.max_bal, view)
{
  var max_bal := b[i].replicas[idx].replica.acceptor.max_bal;
  lemma_MaxBalLeqMaxBallotPrimarySent1a(b, asp.c, i, idx);
  assert BalLeq(b[i].replicas[max_bal.proposer_id].replica.proposer.max_ballot_i_sent_1a, view); // TRIGGER
}

}
