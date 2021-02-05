include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"
include "MaxBallotISent1a.i.dfy"

module CommonProof__MaxBallot_i {
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Constants_i
import opened LiveRSL__Types_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened CommonProof__PacketSending_i
import opened CommonProof__MaxBallotISent1a_i
import opened Temporal__Temporal_s

lemma lemma_MaxBalLeqMaxBallotPrimarySent1a(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  ensures  0 <= b[i].replicas[idx].replica.acceptor.max_bal.proposer_id < |b[i].replicas|
  ensures  var max_bal := b[i].replicas[idx].replica.acceptor.max_bal;
           BalLeq(max_bal, b[i].replicas[max_bal.proposer_id].replica.proposer.max_ballot_i_sent_1a)
  decreases i
{
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    var s := b[i-1].replicas[idx].replica;
    var s' := b[i].replicas[idx].replica;
    var max_bal := s.acceptor.max_bal;
    var max_bal' := s'.acceptor.max_bal;

    if max_bal == max_bal'
    {
      lemma_MaxBalLeqMaxBallotPrimarySent1a(b, c, i-1, idx);
      lemma_MaxBallotISent1aMonotonicOneStep(b, c, i-1, max_bal.proposer_id);
    }
    else
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
      var nextActionIndex := b[i-1].replicas[idx].nextActionIndex;
      assert nextActionIndex == 0;
      var p := ios[0].r;
      lemma_PacketProcessedImpliesPacketSent(b[i-1], b[i], idx, ios, p);
      assert p in b[i-1].environment.sentPackets;
      if p.msg.RslMessage_1a?
      {
        lemma_Message1aLeqMaxBallotSenderSent1a(b, c, i-1, p);
      }
      else if p.msg.RslMessage_2a?
      {
        lemma_Message2aLeqMaxBallotSenderSent1a(b, c, i-1, p);
      }
      else
      {
        assert false;
      }
    }
  }
}

lemma lemma_VotePrecedesMaxBal(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int,
  opn:OperationNumber
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  requires opn in b[i].replicas[idx].replica.acceptor.votes
  ensures  BalLeq(b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal, b[i].replicas[idx].replica.acceptor.max_bal)
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
  lemma_ReplicaConstantsAllConsistent(b, c, i-1, idx);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);

  var s := b[i-1].replicas[idx].replica.acceptor;
  var s' := b[i].replicas[idx].replica.acceptor;

  if s' == s
  {
    lemma_VotePrecedesMaxBal(b, c, i-1, idx, opn);
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  if opn in s.votes
  {
    lemma_VotePrecedesMaxBal(b, c, i-1, idx, opn);
  }
}

}
