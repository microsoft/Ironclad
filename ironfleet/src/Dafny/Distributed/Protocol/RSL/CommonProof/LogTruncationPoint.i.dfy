include "Assumptions.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"
include "MaxBallotISent1a.i.dfy"
include "Quorum.i.dfy"

module CommonProof__LogTruncationPoint_i {

import opened LiveRSL__Configuration_i
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Types_i
import opened LiveRSL__Environment_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened CommonProof__PacketSending_i
import opened CommonProof__MaxBallotISent1a_i
import opened CommonProof__Quorum_i
import opened Temporal__Temporal_s
import opened Collections__CountMatches_i
import opened Collections__Sets_i

predicate QuorumIsWitnessForLogTruncationPoint(
  ps:RslState,
  q:set<int>,
  log_truncation_point:int
  )
{
  && |q| >= LMinQuorumSize(ps.constants.config)
  && forall idx :: idx in q ==> 0 <= idx < |ps.replicas| && ps.replicas[idx].replica.executor.ops_complete >= log_truncation_point    
}

predicate LogTruncationPointInfoValid(
  ps:RslState,
  log_truncation_point:int
  )
{
  exists q:set<int> :: QuorumIsWitnessForLogTruncationPoint(ps, q, log_truncation_point)
}

predicate LogTruncationPointInfoInPacketValid(
  ps:RslState,
  p:RslPacket
  )
{
  && (p.msg.RslMessage_1b? ==> LogTruncationPointInfoValid(ps, p.msg.log_truncation_point))
  && (p.msg.RslMessage_2a? ==> LogTruncationPointInfoValid(ps, p.msg.opn_2a - ps.constants.params.max_log_length + 1))
}

predicate LogTruncationPointInvariant(
  ps:RslState
  )
{
  && (forall idx {:trigger LogTruncationPointInfoValid(ps, ps.replicas[idx].replica.acceptor.log_truncation_point)} ::
       0 <= idx < |ps.replicas| ==> LogTruncationPointInfoValid(ps, ps.replicas[idx].replica.acceptor.log_truncation_point))
  && (forall p {:trigger LogTruncationPointInfoInPacketValid(ps, p)} ::
       p in ps.environment.sentPackets && p.src in ps.constants.config.replica_ids ==> LogTruncationPointInfoInPacketValid(ps, p))
}

lemma lemma_OpsCompleteMonotonicOneStep(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i+1)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  ensures  0 <= idx < |b[i+1].replicas|
  ensures  b[i].replicas[idx].replica.executor.ops_complete <= b[i+1].replicas[idx].replica.executor.ops_complete
{
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i+1);
  if b[i].replicas[idx].replica.executor.ops_complete > b[i+1].replicas[idx].replica.executor.ops_complete
  {
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_ConstantsAllConsistent(b, c, i+1);
    var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i, idx);
    assert false;
  }
}

lemma lemma_OpsCompleteMonotonic(
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
  ensures  b[i].replicas[idx].replica.executor.ops_complete <= b[j].replicas[idx].replica.executor.ops_complete
  decreases j-i
{
  if j == i
  {
  }
  else if j == i + 1
  {
    lemma_OpsCompleteMonotonicOneStep(b, c, i, idx);
  }
  else
  {
    lemma_OpsCompleteMonotonic(b, c, i, j-1, idx);
    lemma_OpsCompleteMonotonicOneStep(b, c, j-1, idx);
  }
}

lemma lemma_LogTruncationPointMonotonicOneStep(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i+1)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  ensures  0 <= idx < |b[i+1].replicas|
  ensures  b[i].replicas[idx].replica.acceptor.log_truncation_point <= b[i+1].replicas[idx].replica.acceptor.log_truncation_point
{
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i+1);
  if b[i].replicas[idx].replica.acceptor.log_truncation_point > b[i+1].replicas[idx].replica.acceptor.log_truncation_point
  {
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_ConstantsAllConsistent(b, c, i+1);
    var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i, idx);
    assert false;
  }
}

lemma lemma_LogTruncationPointMonotonic(
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
  ensures  b[i].replicas[idx].replica.acceptor.log_truncation_point <= b[j].replicas[idx].replica.acceptor.log_truncation_point
  decreases j-i
{
  if j == i
  {
  }
  else if j == i + 1
  {
    lemma_LogTruncationPointMonotonicOneStep(b, c, i, idx);
  }
  else
  {
    lemma_LogTruncationPointMonotonic(b, c, i, j-1, idx);
    lemma_LogTruncationPointMonotonicOneStep(b, c, j-1, idx);
  }
}

lemma lemma_HeartbeatMessagesReflectOpsComplete(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.msg.RslMessage_Heartbeat?
  requires p.src in c.config.replica_ids
  ensures  var sender_index := GetReplicaIndex(p.src, c.config);
           && 0 <= sender_index < |b[i].replicas|
           && p.msg.opn_ckpt <= b[i].replicas[sender_index].replica.executor.ops_complete
{
  if i == 0
  {
    assert false;
  }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  var sender_index := GetReplicaIndex(p.src, c.config);

  if p in b[i-1].environment.sentPackets
  {
    lemma_HeartbeatMessagesReflectOpsComplete(b, c, i-1, p);
    lemma_OpsCompleteMonotonicOneStep(b, c, i-1, sender_index);
  }
  else
  {
    lemma_AssumptionsMakeValidTransition(b, c, i-1);
    var idx, ios := lemma_ActionThatSendsHeartbeatIsMaybeSendHeartbeat(b[i-1], b[i], p);
    assert ReplicasDistinct(c.config.replica_ids, idx, sender_index);
  }
}

lemma lemma_LastCheckpointedOperationSize(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  ensures  |b[i].replicas[idx].replica.acceptor.last_checkpointed_operation| == |b[i].replicas|
  decreases i
{
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);

    lemma_LastCheckpointedOperationSize(b, c, i-1, idx);

    if |b[i].replicas[idx].replica.acceptor.last_checkpointed_operation| != |b[i].replicas|
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
      assert false;
    }
  }
}

lemma lemma_LastCheckpointedOperationReflectsOpsComplete(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  acceptor_idx:int,
  executor_idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= acceptor_idx < |b[i].replicas|
  requires 0 <= executor_idx < |b[i].replicas|
  ensures  0 <= executor_idx < |b[i].replicas[acceptor_idx].replica.acceptor.last_checkpointed_operation|
  ensures  b[i].replicas[acceptor_idx].replica.acceptor.last_checkpointed_operation[executor_idx]
           <= b[i].replicas[executor_idx].replica.executor.ops_complete
{
  lemma_LastCheckpointedOperationSize(b, c, i, acceptor_idx);
    
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);

    lemma_LastCheckpointedOperationReflectsOpsComplete(b, c, i-1, acceptor_idx, executor_idx);
    lemma_OpsCompleteMonotonicOneStep(b, c, i-1, executor_idx);

    if b[i].replicas[acceptor_idx].replica.acceptor.last_checkpointed_operation[executor_idx] >
       b[i].replicas[executor_idx].replica.executor.ops_complete
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, acceptor_idx);
      lemma_PacketProcessedImpliesPacketSent(b[i-1], b[i], acceptor_idx, ios, ios[0].r);
      lemma_HeartbeatMessagesReflectOpsComplete(b, c, i-1, ios[0].r);
      assert false;
    }
  }
}

lemma lemma_LogTruncationPointInfoValidImpliesValidNext(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  log_truncation_point:int
  )
  requires IsValidBehaviorPrefix(b, c, i+1)
  requires 0 <= i
  requires LogTruncationPointInfoValid(b[i], log_truncation_point)
  ensures  LogTruncationPointInfoValid(b[i+1], log_truncation_point)
{
  var q :| QuorumIsWitnessForLogTruncationPoint(b[i], q, log_truncation_point);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i+1);
  forall idx | idx in q
    ensures 0 <= idx < |b[i+1].replicas|
    ensures b[i+1].replicas[idx].replica.executor.ops_complete >= log_truncation_point
  {
    assert 0 <= idx < |b[i].replicas| && b[i].replicas[idx].replica.executor.ops_complete >= log_truncation_point;
    lemma_OpsCompleteMonotonicOneStep(b, c, i, idx);
  }
  assert QuorumIsWitnessForLogTruncationPoint(b[i+1], q, log_truncation_point);
}

lemma lemma_LogTruncationPointInfoValidImpliesSmallerOneValid(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  logTruncationPoint1:int,
  logTruncationPoint2:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires LogTruncationPointInfoValid(b[i], logTruncationPoint1)
  requires logTruncationPoint2 <= logTruncationPoint1
  ensures  LogTruncationPointInfoValid(b[i], logTruncationPoint2)
{
  var q :| QuorumIsWitnessForLogTruncationPoint(b[i], q, logTruncationPoint1);
  lemma_ConstantsAllConsistent(b, c, i);
  forall idx | idx in q
    ensures b[i].replicas[idx].replica.executor.ops_complete >= logTruncationPoint2
  {
    assert 0 <= idx < |b[i].replicas| && b[i].replicas[idx].replica.executor.ops_complete >= logTruncationPoint1;
  }
  assert QuorumIsWitnessForLogTruncationPoint(b[i], q, logTruncationPoint2);
}

lemma lemma_LogTruncationPointStateInvariantMaintainedByStep(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i+1)
  requires 0 <= i
  requires LogTruncationPointInvariant(b[i])
  requires 0 <= idx < |b[i+1].replicas|
  ensures  LogTruncationPointInfoValid(b[i+1], b[i+1].replicas[idx].replica.acceptor.log_truncation_point)
{
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i+1);

  var s := b[i].replicas[idx].replica;
  var s' := b[i+1].replicas[idx].replica;

  if s'.acceptor.log_truncation_point == s.acceptor.log_truncation_point
  {
    lemma_LogTruncationPointInfoValidImpliesValidNext(b, c, i, s.acceptor.log_truncation_point);
  }
  else
  {
    var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i, idx);
    var nextActionIndex := b[i].replicas[idx].nextActionIndex;
    if nextActionIndex == 0
    {
      var p := ios[0].r;
      lemma_PacketProcessedImpliesPacketSent(b[i], b[i+1], idx, ios, p);
      assert LogTruncationPointInfoInPacketValid(b[i], p);
      if p.msg.RslMessage_1b?
      {
        assert LogTruncationPointInfoValid(b[i], p.msg.log_truncation_point);
        assert s'.acceptor.log_truncation_point == p.msg.log_truncation_point;
        lemma_LogTruncationPointInfoValidImpliesValidNext(b, c, i, s'.acceptor.log_truncation_point);
      }
      else if p.msg.RslMessage_2a?
      {
        assert LogTruncationPointInfoValid(b[i], p.msg.opn_2a - b[i].constants.params.max_log_length + 1);
        assert s'.acceptor.log_truncation_point == p.msg.opn_2a - b[i].constants.params.max_log_length + 1;
        lemma_LogTruncationPointInfoValidImpliesValidNext(b, c, i, s'.acceptor.log_truncation_point);
      }
      else
      {
        assert false;
      }
    }
    else if nextActionIndex == 4
    {
      var log_truncation_point := s'.acceptor.log_truncation_point;
      assert IsNthHighestValueInSequence(log_truncation_point, s.acceptor.last_checkpointed_operation,
                                         LMinQuorumSize(s.constants.all.config));
      assert CountMatchesInSeq(s.acceptor.last_checkpointed_operation, x => x >= log_truncation_point)
             >= LMinQuorumSize(s.constants.all.config);
      var q := SetOfIndicesOfMatchesInSeq(s.acceptor.last_checkpointed_operation, x => x >= log_truncation_point);
      assert |q| == CountMatchesInSeq(s.acceptor.last_checkpointed_operation, x => x >= log_truncation_point);
      assert |q| >= LMinQuorumSize(s.constants.all.config);
      forall executor_idx | executor_idx in q
        ensures 0 <= executor_idx < |b[i+1].replicas|
        ensures b[i+1].replicas[executor_idx].replica.executor.ops_complete >= log_truncation_point
      {
        assert s.acceptor.last_checkpointed_operation[executor_idx] >= log_truncation_point;
        lemma_LastCheckpointedOperationSize(b, c, i+1, idx);
        lemma_LastCheckpointedOperationReflectsOpsComplete(b, c, i+1, idx, executor_idx);
      }
      assert QuorumIsWitnessForLogTruncationPoint(b[i+1], q, log_truncation_point);
    }
    else
    {
      assert false;
    }
  }
}

lemma lemma_LogTruncationPointInvariantHolds(
  b:Behavior<RslState>,
  c:LConstants,
  i:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  ensures  LogTruncationPointInvariant(b[i])
{
  if i == 0
  {
    var q := SetOfNumbersInRightExclusiveRange(0, |b[i].constants.config.replica_ids|);
    calc {
      |q|;
      |b[i].constants.config.replica_ids|;
      >= |b[i].constants.config.replica_ids| / 2 + 1;
      LMinQuorumSize(b[i].constants.config);
    }
    assert QuorumIsWitnessForLogTruncationPoint(b[i], q, 0);
    assert LogTruncationPointInfoValid(b[i], 0);
    assert LogTruncationPointInvariant(b[i]);
  }
  else
  {
    lemma_LogTruncationPointInvariantHolds(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);

    forall idx | 0 <= idx < |b[i].replicas|
      ensures LogTruncationPointInfoValid(b[i], b[i].replicas[idx].replica.acceptor.log_truncation_point)
    {
      lemma_LogTruncationPointStateInvariantMaintainedByStep(b, c, i-1, idx);
    }

    forall p | p in b[i].environment.sentPackets && p.src in b[i].constants.config.replica_ids
      ensures LogTruncationPointInfoInPacketValid(b[i], p)
    {
      if p in b[i-1].environment.sentPackets
      {
        assert p.src in b[i-1].constants.config.replica_ids;
        assert LogTruncationPointInfoInPacketValid(b[i-1], p);
        if p.msg.RslMessage_1b?
        {
          lemma_LogTruncationPointInfoValidImpliesValidNext(b, c, i-1, p.msg.log_truncation_point);
        }
        else if p.msg.RslMessage_2a?
        {
          lemma_LogTruncationPointInfoValidImpliesValidNext(b, c, i-1, p.msg.opn_2a - b[i].constants.params.max_log_length + 1);
        }
      }
      else
      {
        lemma_AssumptionsMakeValidTransition(b, c, i-1);
        if p.msg.RslMessage_1b?
        {
          var idx, ios := lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p);
          assert p.msg.log_truncation_point == b[i-1].replicas[idx].replica.acceptor.log_truncation_point;
          lemma_LogTruncationPointInfoValidImpliesValidNext(b, c, i-1, p.msg.log_truncation_point);
        }
        else if p.msg.RslMessage_2a?
        {
          var idx, ios := lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i-1], b[i], p);
          var s := b[i-1].replicas[idx].replica;
          lemma_LogTruncationPointInfoValidImpliesValidNext(b, c, i-1, s.acceptor.log_truncation_point);
          lemma_LogTruncationPointInfoValidImpliesSmallerOneValid(b, c, i, s.acceptor.log_truncation_point,
                                                                  p.msg.opn_2a - s.proposer.constants.all.params.max_log_length + 1);
        }
      }
    }
  }
}

lemma lemma_AlwaysSomeReplicaInQuorumBeyondLogTruncationPoint(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  acceptor_idx:int,
  quorum:set<int>
  ) returns (
  king_idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= acceptor_idx < |b[i].replicas|
  requires forall replica_index :: replica_index in quorum ==> 0 <= replica_index < |c.config.replica_ids|
  requires |quorum| >= LMinQuorumSize(c.config)
  ensures  king_idx in quorum
  ensures  0 <= king_idx < |b[i].replicas|
  ensures  b[i].replicas[king_idx].replica.executor.ops_complete >= b[i].replicas[acceptor_idx].replica.acceptor.log_truncation_point
{
  lemma_LogTruncationPointInvariantHolds(b, c, i);
  var log_truncation_point := b[i].replicas[acceptor_idx].replica.acceptor.log_truncation_point;
  assert LogTruncationPointInfoValid(b[i], log_truncation_point);

  var q :| QuorumIsWitnessForLogTruncationPoint(b[i], q, log_truncation_point);
  lemma_ConstantsAllConsistent(b, c, i);
  king_idx := lemma_QuorumIndexOverlap(q, quorum, |c.config.replica_ids|);
}

lemma lemma_ProposerLogTruncationPointAlwaysBeyondThatOfAllReceived1bs(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  ensures  var s := b[i].replicas[idx].replica;
           forall p{:trigger p in s.proposer.received_1b_packets} ::
               p in s.proposer.received_1b_packets && p.msg.RslMessage_1b?
               ==> s.acceptor.log_truncation_point >= p.msg.log_truncation_point
  decreases i
{
  if i > 0
  {
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);

    var s := b[i-1].replicas[idx].replica;
    var s' := b[i].replicas[idx].replica;
    forall p | p in s'.proposer.received_1b_packets && p.msg.RslMessage_1b?
      ensures s'.acceptor.log_truncation_point >= p.msg.log_truncation_point
    {
      if p in s.proposer.received_1b_packets
      {
        lemma_ProposerLogTruncationPointAlwaysBeyondThatOfAllReceived1bs(b, c, i-1, idx);
        assert s.acceptor.log_truncation_point >= p.msg.log_truncation_point;
        lemma_LogTruncationPointMonotonicOneStep(b, c, i-1, idx);
      }
      else
      {
        var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
        assert s'.acceptor.log_truncation_point >= p.msg.log_truncation_point;
      }
    }
  }
}

lemma lemma_VoteAlwaysWithinLogTruncationPointRange(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  replica_idx:int,
  opn:OperationNumber
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= replica_idx < |b[i].replicas|
  requires opn in b[i].replicas[replica_idx].replica.acceptor.votes
  ensures  var log_truncation_point := b[i].replicas[replica_idx].replica.acceptor.log_truncation_point;
           log_truncation_point <= opn < log_truncation_point + c.params.max_log_length
{
  if i == 0
  {
    return;
  }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);

  var s := b[i-1].replicas[replica_idx].replica;
  var s' := b[i].replicas[replica_idx].replica;

  var log_truncation_point := s.acceptor.log_truncation_point;
  var log_truncation_point' := s'.acceptor.log_truncation_point;
    
  if log_truncation_point' <= opn < log_truncation_point' + c.params.max_log_length
  {
    return;
  }

  if opn in s.acceptor.votes
  {
    lemma_VoteAlwaysWithinLogTruncationPointRange(b, c, i-1, replica_idx, opn);
    if log_truncation_point == log_truncation_point'
    {
      assert false;
    }
    else
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, replica_idx);
      assert false;
    }
  }
  else
  {
    var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, replica_idx);
    assert false;
  }
}

lemma lemma_VoteIn1bMessageAlwaysWithinLogTruncationPointRange(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  opn:OperationNumber,
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.msg.RslMessage_1b?
  requires p.src in c.config.replica_ids
  requires opn in p.msg.votes
  ensures  var log_truncation_point := p.msg.log_truncation_point;
           log_truncation_point <= opn < log_truncation_point + c.params.max_log_length
{
  if i == 0
  {
    return;
  }

  if p in b[i-1].environment.sentPackets
  {
    lemma_VoteIn1bMessageAlwaysWithinLogTruncationPointRange(b, c, i-1, opn, p);
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  var idx, ios := lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p);
  var log_truncation_point := p.msg.log_truncation_point;
  lemma_VoteAlwaysWithinLogTruncationPointRange(b, c, i-1, idx, opn);
  assert log_truncation_point <= opn < log_truncation_point + c.params.max_log_length;
}

lemma lemma_VoteInReceived1bMessageAlwaysWithinLogTruncationPointRange(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int,
  opn:OperationNumber,
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  requires p in b[i].replicas[idx].replica.proposer.received_1b_packets
  requires p.msg.RslMessage_1b?
  requires opn in p.msg.votes
  ensures  var log_truncation_point := b[i].replicas[idx].replica.acceptor.log_truncation_point;
           opn < log_truncation_point + c.params.max_log_length
{
  if i == 0
  {
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);

  var s := b[i-1].replicas[idx].replica;
  var s' := b[i].replicas[idx].replica;
  lemma_LogTruncationPointMonotonicOneStep(b, c, i-1, idx);

  if p in s.proposer.received_1b_packets
  {
    lemma_VoteInReceived1bMessageAlwaysWithinLogTruncationPointRange(b, c, i-1, idx, opn, p);
    lemma_LogTruncationPointMonotonicOneStep(b, c, i-1, idx);
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  lemma_VoteIn1bMessageAlwaysWithinLogTruncationPointRange(b, c, i, opn, p);
}

}
