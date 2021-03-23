include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"
include "Environment.i.dfy"
include "Message2b.i.dfy"
include "MaxBallot.i.dfy"

module CommonProof__Message1b_i {
import opened LiveRSL__Constants_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Types_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Environment_i
import opened CommonProof__Message2b_i
import opened CommonProof__MaxBallot_i
import opened Environment_s
import opened Temporal__Temporal_s

lemma lemma_1bMessageImplicationsForAcceptorState(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  opn:OperationNumber,
  p:RslPacket
  ) returns (
  acceptor_idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_1b?
  ensures  0 <= acceptor_idx < |c.config.replica_ids|
  ensures  0 <= acceptor_idx < |b[i].replicas|
  ensures  p.src == c.config.replica_ids[acceptor_idx]
  ensures  BalLeq(p.msg.bal_1b, b[i].replicas[acceptor_idx].replica.acceptor.max_bal)
  ensures  var s := b[i].replicas[acceptor_idx].replica.acceptor;
           opn in p.msg.votes && opn >= s.log_truncation_point ==>
             && opn in s.votes
             && (|| BalLeq(p.msg.bal_1b, s.votes[opn].max_value_bal)
                || s.votes[opn] == Vote(p.msg.votes[opn].max_value_bal, p.msg.votes[opn].max_val))
  ensures  var s := b[i].replicas[acceptor_idx].replica.acceptor;
           opn !in p.msg.votes && opn >= s.log_truncation_point ==>
             || opn !in s.votes
             || (opn in s.votes && BalLeq(p.msg.bal_1b, s.votes[opn].max_value_bal));
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
    acceptor_idx := lemma_1bMessageImplicationsForAcceptorState(b, c, i-1, opn, p);
    var s := b[i-1].replicas[acceptor_idx].replica.acceptor;
    var s' := b[i].replicas[acceptor_idx].replica.acceptor;

    if opn < s'.log_truncation_point
    {
      return;
    }
    if s'.log_truncation_point == s.log_truncation_point && s'.votes == s.votes
    {
      return;
    }

    var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, acceptor_idx);
    assert opn >= s'.log_truncation_point >= s.log_truncation_point;
    if opn in p.msg.votes
    {
      lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i-1, opn, acceptor_idx);

      if s'.votes[opn].max_value_bal == s.votes[opn].max_value_bal
      {
        lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(b, c, i-1, opn, s.votes[opn].max_value_bal, acceptor_idx);
      }
    }
    return;
  }

  var ios:seq<RslIo>;
  acceptor_idx, ios := lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p);

  var s := b[i-1].replicas[acceptor_idx].replica.acceptor;
  var s' := b[i].replicas[acceptor_idx].replica.acceptor;
  if opn in s.votes && opn in s'.votes && s'.votes[opn].max_value_bal == s.votes[opn].max_value_bal
  {
    lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(b, c, i-1, opn, s.votes[opn].max_value_bal, acceptor_idx);
  }
}

lemma lemma_1bMessageWithoutOpnImplicationsFor2b(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  opn:OperationNumber,
  p_1b:RslPacket,
  p_2b:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p_1b in b[i].environment.sentPackets
  requires p_2b in b[i].environment.sentPackets
  requires p_1b.src in c.config.replica_ids
  requires p_1b.src == p_2b.src
  requires p_1b.msg.RslMessage_1b?
  requires p_2b.msg.RslMessage_2b?
  requires opn !in p_1b.msg.votes
  requires opn >= p_1b.msg.log_truncation_point
  requires p_2b.msg.opn_2b == opn
  ensures  BalLeq(p_1b.msg.bal_1b, p_2b.msg.bal_2b)
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i-1);

  if p_1b in b[i-1].environment.sentPackets
  {
    if p_2b in b[i-1].environment.sentPackets
    {
      lemma_1bMessageWithoutOpnImplicationsFor2b(b, c, i-1, opn, p_1b, p_2b);
    }
    else
    {
      var acceptor_idx := lemma_1bMessageImplicationsForAcceptorState(b, c, i-1, opn, p_1b);
      var acceptor_idx_alt, ios := lemma_ActionThatSends2bIsProcess2a(b[i-1], b[i], p_2b);
      assert ReplicasDistinct(c.config.replica_ids, acceptor_idx, acceptor_idx_alt);
    }
  }
    else
    {
      if p_2b in b[i-1].environment.sentPackets
      {
        var acceptor_idx := lemma_2bMessageImplicationsForAcceptorState(b, c, i-1, p_2b);
        var acceptor_idx_alt, ios := lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p_1b);
        assert ReplicasDistinct(c.config.replica_ids, acceptor_idx, acceptor_idx_alt);
      }
      else
      {
        var acceptor_idx, ios := lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p_1b);
        assert LIoOpSend(p_1b) in ios;
        assert false;
      }
    }
}

lemma lemma_1bMessageWithOpnImplicationsFor2b(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  opn:OperationNumber,
  p_1b:RslPacket,
  p_2b:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p_1b in b[i].environment.sentPackets
  requires p_2b in b[i].environment.sentPackets
  requires p_1b.src in c.config.replica_ids
  requires p_1b.src == p_2b.src
  requires p_1b.msg.RslMessage_1b?
  requires p_2b.msg.RslMessage_2b?
  requires opn in p_1b.msg.votes
  requires opn >= p_1b.msg.log_truncation_point
  requires p_2b.msg.opn_2b == opn
  ensures  || BalLeq(p_1b.msg.bal_1b, p_2b.msg.bal_2b)
           || (p_2b.msg.bal_2b == p_1b.msg.votes[opn].max_value_bal && p_2b.msg.val_2b == p_1b.msg.votes[opn].max_val)
           || BalLt(p_2b.msg.bal_2b, p_1b.msg.votes[opn].max_value_bal)
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i-1);

  if p_1b in b[i-1].environment.sentPackets
  {
    if p_2b in b[i-1].environment.sentPackets
    {
      lemma_1bMessageWithOpnImplicationsFor2b(b, c, i-1, opn, p_1b, p_2b);
    }
    else
    {
      var acceptor_idx := lemma_1bMessageImplicationsForAcceptorState(b, c, i-1, opn, p_1b);
      var acceptor_idx_alt, ios := lemma_ActionThatSends2bIsProcess2a(b[i-1], b[i], p_2b);
      assert ReplicasDistinct(c.config.replica_ids, acceptor_idx, acceptor_idx_alt);
    }
  }
  else
  {
    if p_2b in b[i-1].environment.sentPackets
    {
      var acceptor_idx := lemma_2bMessageImplicationsForAcceptorState(b, c, i-1, p_2b);
      var acceptor_idx_alt, ios := lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p_1b);
      assert ReplicasDistinct(c.config.replica_ids, acceptor_idx, acceptor_idx_alt);
    }
    else
    {
      var acceptor_idx, ios := lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p_1b);
      assert LIoOpSend(p_1b) in ios;
      assert false;
    }
  }
}

lemma lemma_Vote1bMessageIsFromEarlierBallot(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  opn:OperationNumber,
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_1b?
  requires opn in p.msg.votes
  ensures  BalLt(p.msg.votes[opn].max_value_bal, p.msg.bal_1b)
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
    lemma_Vote1bMessageIsFromEarlierBallot(b, c, i-1, opn, p);
    return;
  }

  var idx, ios := lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p);
  lemma_VotePrecedesMaxBal(b, c, i-1, idx, opn);
}

lemma lemma_1bMessageWithOpnImplies2aSent(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  opn:OperationNumber,
  p_1b:RslPacket
  ) returns (
  p_2a:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p_1b in b[i].environment.sentPackets
  requires p_1b.src in c.config.replica_ids
  requires p_1b.msg.RslMessage_1b?
  requires opn in p_1b.msg.votes
  ensures  p_2a in b[i].environment.sentPackets
  ensures  p_2a.src in c.config.replica_ids
  ensures  p_2a.msg.RslMessage_2a?
  ensures  p_2a.msg.opn_2a == opn
  ensures  p_2a.msg.bal_2a == p_1b.msg.votes[opn].max_value_bal
  ensures  p_2a.msg.val_2a == p_1b.msg.votes[opn].max_val
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i-1);

  if p_1b in b[i-1].environment.sentPackets
  {
    p_2a := lemma_1bMessageWithOpnImplies2aSent(b, c, i-1, opn, p_1b);
    return;
  }

  var idx, ios := lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p_1b);
  p_2a := lemma_VoteWithOpnImplies2aSent(b, c, i-1, idx, opn);
}

}
