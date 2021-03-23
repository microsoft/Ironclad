include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"
include "Environment.i.dfy"
include "LearnerState.i.dfy"
include "Quorum.i.dfy"
include "Message1b.i.dfy"

module CommonProof__Chosen_i {

import opened LiveRSL__Configuration_i
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Executor_i
import opened LiveRSL__Message_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Types_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Environment_i
import opened CommonProof__LearnerState_i
import opened CommonProof__Quorum_i
import opened CommonProof__Message1b_i
import opened CommonProof__Message2a_i
import opened CommonProof__Message2b_i
import opened Concrete_NodeIdentity_i
import opened Temporal__Temporal_s
import opened Collections__Sets_i
import opened Environment_s

datatype QuorumOf2bs = QuorumOf2bs(c:LConstants, indices:set<int>, packets:seq<RslPacket>, bal:Ballot, opn:OperationNumber, v:RequestBatch)

predicate IsValidQuorumOf2bs(
  ps:RslState,
  q:QuorumOf2bs
  )
{
  && |q.indices| >= LMinQuorumSize(ps.constants.config)
  && |q.packets| == |ps.constants.config.replica_ids|
  && (forall idx :: idx in q.indices ==> && 0 <= idx < |ps.constants.config.replica_ids|
                                 && var p := q.packets[idx];
                                   && p.src == ps.constants.config.replica_ids[idx]
                                   && p.msg.RslMessage_2b?
                                   && p.msg.opn_2b == q.opn
                                   && p.msg.val_2b == q.v
                                   && p.msg.bal_2b == q.bal
                                   && p in ps.environment.sentPackets)
}

lemma lemma_QuorumOf2bsStaysValid(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  j:int,
  q:QuorumOf2bs
  )
  requires IsValidBehaviorPrefix(b, c, j)
  requires IsValidQuorumOf2bs(b[i], q)
  requires 0 <= i <= j
  ensures  IsValidQuorumOf2bs(b[j], q)
{
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, j);

  forall idx | idx in q.indices
    ensures q.packets[idx] in b[j].environment.sentPackets
  {
    lemma_PacketStaysInSentPackets(b, c, i, j, q.packets[idx]);
  }
}

lemma lemma_ChosenQuorumAnd2aFromLaterBallotMatchValues(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  quorum_of_2bs:QuorumOf2bs,
  packet2a:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires IsValidQuorumOf2bs(b[i], quorum_of_2bs)
  requires packet2a in b[i].environment.sentPackets
  requires packet2a.src in c.config.replica_ids
  requires packet2a.msg.RslMessage_2a?
  requires quorum_of_2bs.opn == packet2a.msg.opn_2a
  requires BalLt(quorum_of_2bs.bal, packet2a.msg.bal_2a)
  ensures  quorum_of_2bs.v == packet2a.msg.val_2a
  decreases packet2a.msg.bal_2a.seqno, packet2a.msg.bal_2a.proposer_id
{
  lemma_ConstantsAllConsistent(b, c, i);

  var opn := quorum_of_2bs.opn;
  var quorum_of_1bs := lemma_2aMessageHas1bQuorumPermittingIt(b, c, i, packet2a);
  var quorum_of_1bs_indices := lemma_GetIndicesFromPackets(quorum_of_1bs, c.config);

  var overlap_idx := lemma_QuorumIndexOverlap(quorum_of_1bs_indices, quorum_of_2bs.indices, |c.config.replica_ids|);
  var packet1b_overlap :| packet1b_overlap in quorum_of_1bs && packet1b_overlap.src == c.config.replica_ids[overlap_idx];
  var packet2b_overlap := quorum_of_2bs.packets[overlap_idx];

  if opn !in packet1b_overlap.msg.votes
  {
    lemma_1bMessageWithoutOpnImplicationsFor2b(b, c, i, opn, packet1b_overlap, packet2b_overlap);
    assert false;
  }

  var highestballot_in_1b_set :| LValIsHighestNumberedProposalAtBallot(packet2a.msg.val_2a, highestballot_in_1b_set, quorum_of_1bs, opn);
  assert BalLeq(packet1b_overlap.msg.votes[opn].max_value_bal, highestballot_in_1b_set);
  var packet1b_highestballot :| && packet1b_highestballot in quorum_of_1bs
                                && opn in packet1b_highestballot.msg.votes
                                && packet1b_highestballot.msg.votes[opn] == Vote(highestballot_in_1b_set, packet2a.msg.val_2a);
  lemma_Vote1bMessageIsFromEarlierBallot(b, c, i, opn, packet1b_highestballot);

  lemma_1bMessageWithOpnImplicationsFor2b(b, c, i, opn, packet1b_overlap, packet2b_overlap);

  var previous_packet2a := lemma_1bMessageWithOpnImplies2aSent(b, c, i, opn, packet1b_highestballot);
  assert BalLt(previous_packet2a.msg.bal_2a, packet2a.msg.bal_2a);

  if quorum_of_2bs.bal == previous_packet2a.msg.bal_2a
  {
    var packet2a_overlap := lemma_2bMessageHasCorresponding2aMessage(b, c, i, packet2b_overlap);
    lemma_2aMessagesFromSameBallotAndOperationMatch(b, c, i, packet2a_overlap, previous_packet2a);
  }
  else
  {
    lemma_2aMessageHasValidBallot(b, c, i, packet2a); // to demonstrate decreases values are >= 0
    lemma_ChosenQuorumAnd2aFromLaterBallotMatchValues(b, c, i, quorum_of_2bs, previous_packet2a);
  }
}

lemma lemma_ChosenQuorumsMatchValue(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  q1:QuorumOf2bs,
  q2:QuorumOf2bs
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires IsValidQuorumOf2bs(b[i], q1)
  requires IsValidQuorumOf2bs(b[i], q2)
  requires q1.opn == q2.opn
  ensures  q1.v == q2.v
{
  lemma_ConstantsAllConsistent(b, c, i);

  var idx1 :| idx1 in q1.indices;
  var idx2 :| idx2 in q2.indices;
  var p1_2b := q1.packets[idx1];
  var p2_2b := q2.packets[idx2];
  var p1_2a := lemma_2bMessageHasCorresponding2aMessage(b, c, i, p1_2b);
  var p2_2a := lemma_2bMessageHasCorresponding2aMessage(b, c, i, p2_2b);

  if q1.bal == q2.bal
  {
    lemma_2aMessagesFromSameBallotAndOperationMatch(b, c, i, p1_2a, p2_2a);
  }
  else if BalLt(q1.bal, q2.bal)
  {
    lemma_ChosenQuorumAnd2aFromLaterBallotMatchValues(b, c, i, q1, p2_2a);
  }
  else
  {
    lemma_ChosenQuorumAnd2aFromLaterBallotMatchValues(b, c, i, q2, p1_2a);
  }
}

lemma lemma_DecidedOperationWasChosen(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int
  ) returns (
  q:QuorumOf2bs
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  requires b[i].replicas[idx].replica.executor.next_op_to_execute.OutstandingOpKnown?
  ensures  IsValidQuorumOf2bs(b[i], q)
  ensures  var s := b[i].replicas[idx].replica.executor;
           q.bal == s.next_op_to_execute.bal && q.opn == s.ops_complete && q.v == s.next_op_to_execute.v
{
  if i == 0
  {
    return;
  }

  lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
  lemma_ReplicaConstantsAllConsistent(b, c, i-1, idx);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);

  var s := b[i-1].replicas[idx].replica;
  var s' := b[i].replicas[idx].replica;

  if s'.executor.next_op_to_execute == s.executor.next_op_to_execute
  {
    q := lemma_DecidedOperationWasChosen(b, c, i-1, idx);
    lemma_QuorumOf2bsStaysValid(b, c, i-1, i, q);
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  assert b[i-1].replicas[idx].nextActionIndex == 5;
  var opn := s.executor.ops_complete;
  var v := s.learner.unexecuted_learner_state[opn].candidate_learned_value;
  var bal := s.learner.max_ballot_seen;
  assert opn in s.learner.unexecuted_learner_state;
  assert |s.learner.unexecuted_learner_state[opn].received_2b_message_senders| >= LMinQuorumSize(c.config);
  assert s'.executor.next_op_to_execute == OutstandingOpKnown(v, bal);
  var senders := s.learner.unexecuted_learner_state[opn].received_2b_message_senders;

  var indices:set<int> := {};
  var packets:seq<RslPacket> := [];
  var sender_idx := 0;
  var dummy_packet := LPacket(c.config.replica_ids[0], c.config.replica_ids[0], RslMessage_1a(Ballot(0, 0)));
  while sender_idx < |c.config.replica_ids|
    invariant 0 <= sender_idx <= |c.config.replica_ids|
    invariant |packets| == sender_idx
    invariant forall sidx :: sidx in indices ==> && 0 <= sidx < sender_idx
                                          && var p := packets[sidx];
                                             && p.src == b[i].constants.config.replica_ids[sidx]
                                             && p.msg.RslMessage_2b?
                                             && p.msg.opn_2b == opn
                                             && p.msg.val_2b == v
                                             && p.msg.bal_2b == bal
                                             && p in b[i].environment.sentPackets
    invariant forall sidx {:trigger c.config.replica_ids[sidx] in senders} ::
                      0 <= sidx < sender_idx && c.config.replica_ids[sidx] in senders ==> sidx in indices
  {
    var sender := c.config.replica_ids[sender_idx];
    if sender in senders
    {
      var sender_idx_unused, p := lemma_GetSent2bMessageFromLearnerState(b, c, i, idx, opn, sender);
      assert ReplicasDistinct(c.config.replica_ids, sender_idx, GetReplicaIndex(p.src, c.config));
      packets := packets + [p];
      indices := indices + {sender_idx};
    }
    else
    {
      packets := packets + [dummy_packet];
    }
    sender_idx := sender_idx + 1;
  }

  lemma_Received2bMessageSendersAlwaysValidReplicas(b, c, i-1, idx, opn);
  var alt_indices := lemma_GetIndicesFromNodes(senders, c.config);
  forall sidx | sidx in alt_indices
    ensures sidx in indices
  {
    assert 0 <= sidx < |c.config.replica_ids|;
    assert c.config.replica_ids[sidx] in senders;
  }
  SubsetCardinality(alt_indices, indices);
    
  q := QuorumOf2bs(c, indices, packets, bal, opn, v);
}

lemma lemma_ExecutedOperationAndAllBeforeItWereChosen(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int
  ) returns (
  qs:seq<QuorumOf2bs>
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  ensures  |qs| == b[i].replicas[idx].replica.executor.ops_complete
  ensures  forall opn :: 0 <= opn < |qs| ==> && IsValidQuorumOf2bs(b[i], qs[opn])
                                      && qs[opn].opn == opn
                                      && BalLeq(qs[opn].bal, b[i].replicas[idx].replica.executor.max_bal_reflected)
  decreases i
{
  if i == 0
  {
    qs := [];
    return;
  }

  lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
  lemma_ReplicaConstantsAllConsistent(b, c, i-1, idx);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);

  var s := b[i-1].replicas[idx].replica.executor;
  var s' := b[i].replicas[idx].replica.executor;

  if s'.ops_complete == s.ops_complete
  {
    qs := lemma_ExecutedOperationAndAllBeforeItWereChosen(b, c, i-1, idx);
    forall opn | 0 <= opn < |qs|
      ensures IsValidQuorumOf2bs(b[i], qs[opn])
    {
      lemma_QuorumOf2bsStaysValid(b, c, i-1, i, qs[opn]);
    }
    if s'.max_bal_reflected != s.max_bal_reflected
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
      assert false;
    }
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  if b[i-1].replicas[idx].nextActionIndex == 0
  {
    var p := ios[0].r;
    qs := lemma_TransferredStateBasedOnChosenOperations(b, c, i-1, p);
    return;
  }

  var prev_qs := lemma_ExecutedOperationAndAllBeforeItWereChosen(b, c, i-1, idx);
  var q := lemma_DecidedOperationWasChosen(b, c, i-1, idx);
  qs := prev_qs + [q];
}

lemma lemma_TransferredStateBasedOnChosenOperations(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p:RslPacket
  ) returns (
  qs:seq<QuorumOf2bs>
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_AppStateSupply?
  ensures  |qs| == p.msg.opn_state_supply
  ensures  forall opn :: 0 <= opn < |qs| ==> && IsValidQuorumOf2bs(b[i], qs[opn])
                                      && qs[opn].opn == opn
                                      && BalLeq(qs[opn].bal, p.msg.bal_state_supply)
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);

  if p in b[i-1].environment.sentPackets
  {
    qs := lemma_TransferredStateBasedOnChosenOperations(b, c, i-1, p);
    forall opn | 0 <= opn < |qs|
      ensures IsValidQuorumOf2bs(b[i], qs[opn])
    {
      lemma_QuorumOf2bsStaysValid(b, c, i-1, i, qs[opn]);
    }
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  var idx, ios := lemma_ActionThatSendsAppStateSupplyIsProcessAppStateRequest(b[i-1], b[i], p);
  qs := lemma_ExecutedOperationAndAllBeforeItWereChosen(b, c, i-1, idx);
}

}
