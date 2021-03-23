include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"
include "Environment.i.dfy"
include "Message2a.i.dfy"

module CommonProof__Message2b_i {
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Types_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Environment_i
import opened CommonProof__Message2a_i
import opened Temporal__Temporal_s

lemma lemma_2bMessageHasCorresponding2aMessage(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p_2b:RslPacket
  ) returns (
  p_2a:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p_2b in b[i].environment.sentPackets
  requires p_2b.src in c.config.replica_ids
  requires p_2b.msg.RslMessage_2b?
  ensures  p_2a in b[i].environment.sentPackets
  ensures  p_2a.src in c.config.replica_ids
  ensures  p_2a.msg.RslMessage_2a?
  ensures  p_2a.msg.opn_2a == p_2b.msg.opn_2b
  ensures  p_2a.msg.bal_2a == p_2b.msg.bal_2b
  ensures  p_2a.msg.val_2a == p_2b.msg.val_2b
  decreases i
{
  if i == 0
  {
    return;
  }

  if p_2b in b[i-1].environment.sentPackets
  {
    p_2a := lemma_2bMessageHasCorresponding2aMessage(b, c, i-1, p_2b);
    lemma_PacketStaysInSentPackets(b, c, i-1, i, p_2a);
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i-1);

  var proposer_idx, ios := lemma_ActionThatSends2bIsProcess2a(b[i-1], b[i], p_2b);
  p_2a := ios[0].r;
}

lemma lemma_CurrentVoteDoesNotExceedMaxBal(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  opn:OperationNumber,
  idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  requires opn in b[i].replicas[idx].replica.acceptor.votes
  ensures  BalLeq(b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal, b[i].replicas[idx].replica.acceptor.max_bal)
{
  if i == 0
  {
    return;
  }
    
  lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
  lemma_ReplicaConstantsAllConsistent(b, c, i-1, idx);

  var s := b[i-1].replicas[idx].replica.acceptor;
  var s' := b[i].replicas[idx].replica.acceptor;
  if s'.votes == s.votes && s'.max_bal == s.max_bal
  {
    lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i-1, opn, idx);
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  if opn in s.votes
  {
    lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i-1, opn, idx);
  }
}

lemma lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  opn:OperationNumber,
  bal:Ballot,
  idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i+1)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  requires 0 <= idx < |b[i+1].replicas|
  requires opn in b[i].replicas[idx].replica.acceptor.votes
  requires opn in b[i+1].replicas[idx].replica.acceptor.votes
  requires b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal == b[i+1].replicas[idx].replica.acceptor.votes[opn].max_value_bal
  ensures  b[i].replicas[idx].replica.acceptor.votes[opn].max_val == b[i+1].replicas[idx].replica.acceptor.votes[opn].max_val
{
  lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
  lemma_ReplicaConstantsAllConsistent(b, c, i+1, idx);
  lemma_AssumptionsMakeValidTransition(b, c, i);
    
  var s := b[i].replicas[idx].replica.acceptor;
  var s' := b[i+1].replicas[idx].replica.acceptor;

  if s'.votes[opn].max_val != s.votes[opn].max_val
  {
    var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i, idx);
    var earlier_2a := lemma_Find2aThatCausedVote(b, c, i, idx, opn);
    lemma_2aMessagesFromSameBallotAndOperationMatch(b, c, i+1, earlier_2a, ios[0].r);
    assert false;
  }
}

lemma lemma_2bMessageImplicationsForAcceptorState(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p:RslPacket
  ) returns (
  acceptor_idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_2b?
  ensures  0 <= acceptor_idx < |c.config.replica_ids|
  ensures  0 <= acceptor_idx < |b[i].replicas|
  ensures  p.src == c.config.replica_ids[acceptor_idx]
  ensures  BalLeq(p.msg.bal_2b, b[i].replicas[acceptor_idx].replica.acceptor.max_bal)
  ensures  var s := b[i].replicas[acceptor_idx].replica.acceptor;
           p.msg.opn_2b >= s.log_truncation_point ==>
             && p.msg.opn_2b in s.votes
             && BalLeq(p.msg.bal_2b, s.votes[p.msg.opn_2b].max_value_bal)
             && (s.votes[p.msg.opn_2b].max_value_bal == p.msg.bal_2b ==> s.votes[p.msg.opn_2b].max_val == p.msg.val_2b)
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i-1);

  var v := p.msg.val_2b;
  var opn := p.msg.opn_2b;
  var bal := p.msg.bal_2b;

  if p in b[i-1].environment.sentPackets
  {
    acceptor_idx := lemma_2bMessageImplicationsForAcceptorState(b, c, i-1, p);
    var s := b[i-1].replicas[acceptor_idx].replica.acceptor;
    var s' := b[i].replicas[acceptor_idx].replica.acceptor;
    if s' != s
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, acceptor_idx);
      if opn >= s'.log_truncation_point
      {
        lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i-1, opn, acceptor_idx);
        if s'.votes[opn].max_value_bal == s.votes[opn].max_value_bal
        {
          lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(b, c, i-1, opn, bal, acceptor_idx);
        }
      }
    }
    return;
  }

  var ios:seq<RslIo>;
  acceptor_idx, ios := lemma_ActionThatSends2bIsProcess2a(b[i-1], b[i], p);
}

lemma lemma_VoteWithOpnImplies2aSent(
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
  ensures  p.msg.bal_2a == b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal
  ensures  p.msg.val_2a == b[i].replicas[idx].replica.acceptor.votes[opn].max_val
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i-1);

  var s := b[i-1].replicas[idx].replica.acceptor;
  var s' := b[i].replicas[idx].replica.acceptor;

  if s'.votes == s.votes
  {
    p := lemma_VoteWithOpnImplies2aSent(b, c, i-1, idx, opn);
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  if opn in s.votes && s'.votes[opn] == s.votes[opn]
  {
    p := lemma_VoteWithOpnImplies2aSent(b, c, i-1, idx, opn);
    return;
  }

  p := ios[0].r;
}
    
}
