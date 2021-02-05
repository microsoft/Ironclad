include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"

module CommonProof__MaxBallotISent1a_i {
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Types_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened CommonProof__PacketSending_i
import opened Temporal__Temporal_s

predicate PrimaryHasReachedState2OfBallot(
  ps:RslState,
  bal:Ballot
  )
{
  var proposer_idx := bal.proposer_id;
  && 0 <= proposer_idx < |ps.replicas|
  && var s := ps.replicas[proposer_idx].replica.proposer;
     && BalLeq(bal, s.max_ballot_i_sent_1a)
     && (bal == s.max_ballot_i_sent_1a ==> s.current_state != 1)
}

lemma lemma_MaxBallotISent1aMonotonicOneStep(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i+1)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  ensures  0 <= idx < |b[i+1].replicas|
  ensures  BalLeq(b[i].replicas[idx].replica.proposer.max_ballot_i_sent_1a, b[i+1].replicas[idx].replica.proposer.max_ballot_i_sent_1a)
  ensures  b[i].replicas[idx].replica.proposer.current_state != 1 ==>
             || b[i+1].replicas[idx].replica.proposer.current_state != 1
             || BalLt(b[i].replicas[idx].replica.proposer.max_ballot_i_sent_1a, b[i+1].replicas[idx].replica.proposer.max_ballot_i_sent_1a)
{
  lemma_AssumptionsMakeValidTransition(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i+1);
}

lemma lemma_MaxBallotISent1aMonotonic(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  j:int,
  idx:int
  )
  requires IsValidBehaviorPrefix(b, c, j)
  requires 0 <= i <= j
  requires 0 <= idx < |b[i].replicas|
  ensures  0 <= idx < |b[j].replicas|
  ensures  BalLeq(b[i].replicas[idx].replica.proposer.max_ballot_i_sent_1a, b[j].replicas[idx].replica.proposer.max_ballot_i_sent_1a)
  ensures  b[i].replicas[idx].replica.proposer.current_state != 1 ==>
             || b[j].replicas[idx].replica.proposer.current_state != 1
             || BalLt(b[i].replicas[idx].replica.proposer.max_ballot_i_sent_1a, b[j].replicas[idx].replica.proposer.max_ballot_i_sent_1a)
{
  if j > i
  {
    lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
    lemma_ReplicaConstantsAllConsistent(b, c, j-1, idx);
    lemma_ReplicaConstantsAllConsistent(b, c, j, idx);
    lemma_MaxBallotISent1aMonotonic(b, c, i, j-1, idx);
    lemma_MaxBallotISent1aMonotonicOneStep(b, c, j-1, idx);
  }
}

lemma lemma_MaxBallotISent1aHasMeAsProposer(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  ensures  b[i].replicas[idx].replica.proposer.max_ballot_i_sent_1a.proposer_id == idx
  ensures  b[i].replicas[idx].replica.proposer.max_ballot_i_sent_1a.seqno >= 0
  decreases i
{
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_MaxBallotISent1aHasMeAsProposer(b, c, i-1, idx);

    if b[i].replicas[idx].replica.proposer.max_ballot_i_sent_1a != b[i-1].replicas[idx].replica.proposer.max_ballot_i_sent_1a
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
    }
  }
}

lemma lemma_PrimaryHasReachedState2OfBallotMaintainedByOneStep(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  bal:Ballot
  )
  requires IsValidBehaviorPrefix(b, c, i+1)
  requires 0 <= i
  requires PrimaryHasReachedState2OfBallot(b[i], bal)
  ensures  PrimaryHasReachedState2OfBallot(b[i+1], bal)
{
  lemma_MaxBallotISent1aMonotonicOneStep(b, c, i, bal.proposer_id);
}

lemma lemma_Message1aLeqMaxBallotSenderSent1a(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_1a?
  ensures  0 <= p.msg.bal_1a.proposer_id < |b[i].replicas| == |b[i].constants.config.replica_ids|
  ensures  p.src == b[i].constants.config.replica_ids[p.msg.bal_1a.proposer_id]
  ensures  var proposer_idx := p.msg.bal_1a.proposer_id;
           BalLeq(p.msg.bal_1a, b[i].replicas[proposer_idx].replica.proposer.max_ballot_i_sent_1a)
  decreases i
{
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    if p in b[i-1].environment.sentPackets
    {
      lemma_Message1aLeqMaxBallotSenderSent1a(b, c, i-1, p);
      lemma_MaxBallotISent1aMonotonicOneStep(b, c, i-1, p.msg.bal_1a.proposer_id);
    }
    else
    {
      var idx, ios := lemma_ActionThatSends1aIsMaybeEnterNewViewAndSend1a(b[i-1], b[i], p);
      lemma_MaxBallotISent1aHasMeAsProposer(b, c, i-1, idx);
    }
  }
}

lemma lemma_MessageStartingPhase2LeqMaxBallotSenderSent1a(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_StartingPhase2?
  ensures  0 <= p.msg.bal_2.proposer_id < |b[i].replicas| == |b[i].constants.config.replica_ids|
  ensures  p.src == b[i].constants.config.replica_ids[p.msg.bal_2.proposer_id]
  ensures  var proposer_idx := p.msg.bal_2.proposer_id;
           BalLeq(p.msg.bal_2, b[i].replicas[proposer_idx].replica.proposer.max_ballot_i_sent_1a)
  decreases i
{
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    if p in b[i-1].environment.sentPackets
    {
      lemma_MessageStartingPhase2LeqMaxBallotSenderSent1a(b, c, i-1, p);
      lemma_MaxBallotISent1aMonotonicOneStep(b, c, i-1, p.msg.bal_2.proposer_id);
    }
    else
    {
      var idx, ios := lemma_ActionThatSendsStartingPhase2IsMaybeEnterPhase2(b[i-1], b[i], p);
      lemma_MaxBallotISent1aHasMeAsProposer(b, c, i-1, idx);
    }
  }
}

lemma lemma_Message2aLeqMaxBallotSenderSent1a(
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
  ensures  0 <= p.msg.bal_2a.proposer_id < |b[i].replicas| == |b[i].constants.config.replica_ids|
  ensures  p.src == b[i].constants.config.replica_ids[p.msg.bal_2a.proposer_id]
  ensures  var proposer_idx := p.msg.bal_2a.proposer_id;
           BalLeq(p.msg.bal_2a, b[i].replicas[proposer_idx].replica.proposer.max_ballot_i_sent_1a)
  decreases i
{
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    if p in b[i-1].environment.sentPackets
    {
      lemma_Message2aLeqMaxBallotSenderSent1a(b, c, i-1, p);
      lemma_MaxBallotISent1aMonotonicOneStep(b, c, i-1, p.msg.bal_2a.proposer_id);
    }
    else
    {
      var idx, ios := lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i-1], b[i], p);
      lemma_MaxBallotISent1aHasMeAsProposer(b, c, i-1, idx);
    }
  }
}

lemma lemma_Message2aShowsPrimaryReachedState2(
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
  ensures  PrimaryHasReachedState2OfBallot(b[i], p.msg.bal_2a)
  decreases i
{
  lemma_Message2aLeqMaxBallotSenderSent1a(b, c, i, p);

  if i > 0
  {
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    if p in b[i-1].environment.sentPackets
    {
      lemma_Message2aShowsPrimaryReachedState2(b, c, i-1, p);
      lemma_PrimaryHasReachedState2OfBallotMaintainedByOneStep(b, c, i-1, p.msg.bal_2a);
    }
    else
    {
      var idx, ios := lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i-1], b[i], p);
      lemma_MaxBallotISent1aHasMeAsProposer(b, c, i-1, idx);
    }
  }
}

lemma lemma_Message2bShowsPrimaryReachedState2(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_2b?
  ensures  PrimaryHasReachedState2OfBallot(b[i], p.msg.bal_2b)
  decreases i
{
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    if p in b[i-1].environment.sentPackets
    {
      lemma_Message2bShowsPrimaryReachedState2(b, c, i-1, p);
      lemma_PrimaryHasReachedState2OfBallotMaintainedByOneStep(b, c, i-1, p.msg.bal_2b);
    }
    else
    {
      var idx, ios := lemma_ActionThatSends2bIsProcess2a(b[i-1], b[i], p);
      lemma_PacketProcessedImpliesPacketSent(b[i-1], b[i], idx, ios, ios[0].r);
      lemma_Message2aShowsPrimaryReachedState2(b, c, i-1, ios[0].r);
    }
  }
}

lemma lemma_LearnerMaxBallotSeenShowsPrimaryReachedState2(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  learner_idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= learner_idx < |b[i].replicas|
  ensures  PrimaryHasReachedState2OfBallot(b[i], b[i].replicas[learner_idx].replica.learner.max_ballot_seen)
  decreases i
{
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    var max_ballot_seen := b[i-1].replicas[learner_idx].replica.learner.max_ballot_seen;
    var max_ballot_seen' := b[i].replicas[learner_idx].replica.learner.max_ballot_seen;

    if max_ballot_seen' == max_ballot_seen
    {
      lemma_LearnerMaxBallotSeenShowsPrimaryReachedState2(b, c, i-1, learner_idx);
      lemma_PrimaryHasReachedState2OfBallotMaintainedByOneStep(b, c, i-1, max_ballot_seen);
    }
    else
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, learner_idx);
      lemma_PacketProcessedImpliesPacketSent(b[i-1], b[i], learner_idx, ios, ios[0].r);
      lemma_Message2bShowsPrimaryReachedState2(b, c, i-1, ios[0].r);
    }
  }
}

lemma lemma_ExecutorNextOpToExecuteBallotShowsPrimaryReachedState2(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  executor_idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= executor_idx < |b[i].replicas|
  ensures  var nextOp := b[i].replicas[executor_idx].replica.executor.next_op_to_execute;
           nextOp.OutstandingOpKnown? ==> PrimaryHasReachedState2OfBallot(b[i], nextOp.bal)
  decreases i
{
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    var nextOp := b[i-1].replicas[executor_idx].replica.executor.next_op_to_execute;
    var nextOp' := b[i].replicas[executor_idx].replica.executor.next_op_to_execute;

    if nextOp' == nextOp
    {
      lemma_ExecutorNextOpToExecuteBallotShowsPrimaryReachedState2(b, c, i-1, executor_idx);
      if nextOp.OutstandingOpKnown?
      {
        lemma_PrimaryHasReachedState2OfBallotMaintainedByOneStep(b, c, i-1, nextOp.bal);
      }
    }
    else
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, executor_idx);
      lemma_LearnerMaxBallotSeenShowsPrimaryReachedState2(b, c, i-1, executor_idx);
    }
  }
}

lemma lemma_Received1bPacketsAreFromMaxBallotISent1a(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  ensures  var s := b[i].replicas[idx].replica.proposer;
           forall p :: p in s.received_1b_packets ==> && p.msg.RslMessage_1b?
                                               && p.msg.bal_1b == s.max_ballot_i_sent_1a
                                               && p.src in c.config.replica_ids
                                               && p in b[i].environment.sentPackets
  ensures  var s := b[i].replicas[idx].replica.proposer;
           forall p1, p2 :: p1 in s.received_1b_packets && p2 in s.received_1b_packets ==> p1 == p2 || p1.src != p2.src
{
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);
    lemma_Received1bPacketsAreFromMaxBallotISent1a(b, c, i-1, idx);
    var s := b[i-1].replicas[idx].replica.proposer;
    var s' := b[i].replicas[idx].replica.proposer;
    forall p | p in s'.received_1b_packets
      ensures p.msg.RslMessage_1b?
      ensures p.msg.bal_1b == s.max_ballot_i_sent_1a
      ensures p in b[i].environment.sentPackets
    {
      if p !in s.received_1b_packets
      {
        var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
        lemma_PacketProcessedImpliesPacketSent(b[i-1], b[i], idx, ios, p);
      }
    }
    forall p1, p2 | p1 in s'.received_1b_packets && p2 in s'.received_1b_packets
      ensures p1 == p2 || p1.src != p2.src
    {
      if p1 !in s.received_1b_packets || p2 !in s.received_1b_packets
      {
        var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
      }
      }
  }
}

}
