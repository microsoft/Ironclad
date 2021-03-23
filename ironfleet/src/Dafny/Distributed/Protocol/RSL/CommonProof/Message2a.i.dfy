include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"
include "Environment.i.dfy"
include "MaxBallotISent1a.i.dfy"
include "Received1b.i.dfy"

module CommonProof__Message2a_i {
import opened LiveRSL__Configuration_i
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Types_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Environment_i
import opened CommonProof__MaxBallotISent1a_i
import opened CommonProof__Received1b_i
import opened Temporal__Temporal_s
import opened Environment_s

lemma lemma_2aMessageImplicationsForProposerState(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p:RslPacket
  ) returns (
  proposer_idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_2a?
  ensures  0 <= proposer_idx < |c.config.replica_ids|
  ensures  0 <= proposer_idx < |b[i].replicas|
  ensures  p.src == c.config.replica_ids[proposer_idx]
  ensures  p.msg.bal_2a.proposer_id == proposer_idx
  ensures  var s := b[i].replicas[proposer_idx].replica.proposer;
           || BalLt(p.msg.bal_2a, s.max_ballot_i_sent_1a)
           || (&& s.max_ballot_i_sent_1a == p.msg.bal_2a
              && s.current_state != 1
              && s.next_operation_number_to_propose > p.msg.opn_2a)
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i-1);

  if p in b[i-1].environment.sentPackets
  {
    proposer_idx := lemma_2aMessageImplicationsForProposerState(b, c, i-1, p);
    var s := b[i-1].replicas[proposer_idx].replica.proposer;
    var s' := b[i].replicas[proposer_idx].replica.proposer;
    if s' != s
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, proposer_idx);
    }
    return;
  }

  var ios:seq<RslIo>;
  proposer_idx, ios := lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i-1], b[i], p);
  lemma_MaxBallotISent1aHasMeAsProposer(b, c, i-1, proposer_idx);
}

lemma lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p1:RslPacket,
  p2:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 < i
  requires p1 in b[i].environment.sentPackets
  requires p2 in b[i].environment.sentPackets
  requires p1.src in c.config.replica_ids
  requires p2.src in c.config.replica_ids
  requires p1.msg.RslMessage_2a?
  requires p2.msg.RslMessage_2a?
  requires p1.msg.opn_2a == p2.msg.opn_2a
  requires p1.msg.bal_2a == p2.msg.bal_2a
  requires p2 in b[i-1].environment.sentPackets ==> p1 in b[i-1].environment.sentPackets
  ensures  p1.msg.val_2a == p2.msg.val_2a
  decreases 2 * i
{
  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i-1);

  if p2 in b[i-1].environment.sentPackets
  {
    // Both packets had already been sent by i-1, so we induction.
    lemma_2aMessagesFromSameBallotAndOperationMatch(b, c, i-1, p1, p2);
    return;
  }

  var proposer_idx, ios := lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i-1], b[i], p2);

  if p1 !in b[i-1].environment.sentPackets
  {
    // Both packets were sent in step i-1, so observe that any two packets sent in the same step
    // have the same value.
    assert LIoOpSend(p1) in ios;
    assert LIoOpSend(p2) in ios;
    return;
  }

  // Note the implications on processor state for p1, since once p1 is sent we
  // won't be able to send p2.
  var alt_proposer_idx := lemma_2aMessageImplicationsForProposerState(b, c, i-1, p1);

  // Note the implications on processor state for p2, just to notice that they
  // use the same replica index.
  var alt2_proposer_idx := lemma_2aMessageImplicationsForProposerState(b, c, i, p2);
  assert alt_proposer_idx == alt2_proposer_idx;
  assert ReplicasDistinct(c.config.replica_ids, proposer_idx, alt_proposer_idx);
  assert proposer_idx == alt_proposer_idx;
  assert false;
}

lemma lemma_2aMessagesFromSameBallotAndOperationMatch(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p1:RslPacket,
  p2:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p1 in b[i].environment.sentPackets
  requires p2 in b[i].environment.sentPackets
  requires p1.src in c.config.replica_ids
  requires p2.src in c.config.replica_ids
  requires p1.msg.RslMessage_2a?
  requires p2.msg.RslMessage_2a?
  requires p1.msg.opn_2a == p2.msg.opn_2a
  requires p1.msg.bal_2a == p2.msg.bal_2a
  ensures  p1.msg.val_2a == p2.msg.val_2a
  decreases 2 * i + 1
{
  if i == 0
  {
    return;
  }

  if p2 in b[i-1].environment.sentPackets && p1 !in b[i-1].environment.sentPackets
  {
    lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality(b, c, i, p2, p1);
  }
  else
  {
    lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality(b, c, i, p1, p2);
  }
}

lemma lemma_2aMessageHas1bQuorumPermittingIt(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p:RslPacket
  ) returns (
  q:set<RslPacket>
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_2a?
  ensures  q <= b[i].environment.sentPackets
  ensures  |q| >= LMinQuorumSize(c.config)
  ensures  LIsAfterLogTruncationPoint(p.msg.opn_2a, q)
  ensures  LSetOfMessage1bAboutBallot(q, p.msg.bal_2a)
  ensures  LAllAcceptorsHadNoProposal(q, p.msg.opn_2a) || LValIsHighestNumberedProposal(p.msg.val_2a, q, p.msg.opn_2a)
  ensures  forall p1, p2 :: p1 in q && p2 in q && p1 != p2 ==> p1.src != p2.src
  ensures  forall p1 :: p1 in q ==> p1.src in c.config.replica_ids
{
  if i == 0
  {
    return;
  }

  if p in b[i-1].environment.sentPackets
  {
    q := lemma_2aMessageHas1bQuorumPermittingIt(b, c, i-1, p);
    lemma_PacketSetStaysInSentPackets(b, c, i-1, i, q);
    return;
  }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  var idx, ios := lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i-1], b[i], p);
  q := b[i-1].replicas[idx].replica.proposer.received_1b_packets;

  forall p_1b | p_1b in q
    ensures p_1b in b[i].environment.sentPackets
  {
    lemma_PacketInReceived1bWasSent(b, c, i-1, idx, p_1b);
    lemma_PacketStaysInSentPackets(b, c, i-1, i, p_1b);
  }

  lemma_Received1bPacketsAreFromMaxBallotISent1a(b, c, i-1, idx);
}

lemma lemma_Find2aThatCausedVote(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int,
  opn:OperationNumber
  ) returns (
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  requires opn in b[i].replicas[idx].replica.acceptor.votes
  ensures  p in b[i].environment.sentPackets
  ensures  p.src in c.config.replica_ids
  ensures  p.msg.RslMessage_2a?
  ensures  p.msg.opn_2a == opn
  ensures  p.msg.val_2a == b[i].replicas[idx].replica.acceptor.votes[opn].max_val
  ensures  p.msg.bal_2a == b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal
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

  if opn in s.votes && s'.votes[opn] == s.votes[opn]
  {
    p := lemma_Find2aThatCausedVote(b, c, i-1, idx, opn);
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  p := ios[0].r;
}

lemma lemma_2aMessageHasValidBallot(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_2a?
  ensures  p.msg.bal_2a.seqno >= 0
  ensures  0 <= p.msg.bal_2a.proposer_id < |c.config.replica_ids|
{
  if i == 0
  {
    return;
  }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);

  if p in b[i-1].environment.sentPackets
  {
    lemma_2aMessageHasValidBallot(b, c, i-1, p);
    return;
  }

  var idx, ios := lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i-1], b[i], p);
  lemma_MaxBallotISent1aHasMeAsProposer(b, c, i-1, idx);
}
    
}
