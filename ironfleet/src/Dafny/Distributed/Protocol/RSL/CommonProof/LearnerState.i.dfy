include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"
include "Environment.i.dfy"
include "Message2b.i.dfy"
include "Message2a.i.dfy"

module CommonProof__LearnerState_i {
import opened LiveRSL__Configuration_i
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Types_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Environment_i
import opened CommonProof__Message2b_i
import opened CommonProof__Message2a_i
import opened Temporal__Temporal_s
import opened Concrete_NodeIdentity_i

lemma lemma_Received2bMessageSendersAlwaysValidReplicas(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  learner_idx:int,
  opn:OperationNumber
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= learner_idx < |b[i].replicas|
  requires opn in b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state
  ensures  forall sender :: sender in b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state[opn].received_2b_message_senders
                      ==> sender in c.config.replica_ids
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);

  var s := b[i-1].replicas[learner_idx].replica.learner;
  var s' := b[i].replicas[learner_idx].replica.learner;

  forall sender | sender in s'.unexecuted_learner_state[opn].received_2b_message_senders
    ensures sender in c.config.replica_ids
  {
    if opn in s.unexecuted_learner_state && sender in s.unexecuted_learner_state[opn].received_2b_message_senders
    {
      lemma_Received2bMessageSendersAlwaysValidReplicas(b, c, i-1, learner_idx, opn);
    }
    else
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, learner_idx);
    }
  }
}

lemma lemma_Received2bMessageSendersAlwaysNonempty(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  learner_idx:int,
  opn:OperationNumber
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= learner_idx < |b[i].replicas|
  requires opn in b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state
  ensures  |b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state[opn].received_2b_message_senders| > 0
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);

  var s := b[i-1].replicas[learner_idx].replica.learner;
  var s' := b[i].replicas[learner_idx].replica.learner;

  if s'.unexecuted_learner_state == s.unexecuted_learner_state
  {
    lemma_Received2bMessageSendersAlwaysNonempty(b, c, i-1, learner_idx, opn);
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, learner_idx);
  if opn in s.unexecuted_learner_state
  {
    lemma_Received2bMessageSendersAlwaysNonempty(b, c, i-1, learner_idx, opn);
  }
}

lemma lemma_GetSent2bMessageFromLearnerState(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  learner_idx:int,
  opn:OperationNumber,
  sender:NodeIdentity
  ) returns (
  sender_idx:int,
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= learner_idx < |b[i].replicas|
  requires opn in b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state
  requires sender in b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state[opn].received_2b_message_senders
  ensures  0 <= sender_idx < |c.config.replica_ids|
  ensures  p in b[i].environment.sentPackets
  ensures  p.src == sender == c.config.replica_ids[sender_idx]
  ensures  p.msg.RslMessage_2b?
  ensures  p.msg.opn_2b == opn
  ensures  p.msg.bal_2b == b[i].replicas[learner_idx].replica.learner.max_ballot_seen
  ensures  p.msg.val_2b == b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state[opn].candidate_learned_value
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_ReplicaConstantsAllConsistent(b, c, i, learner_idx);
  lemma_ReplicaConstantsAllConsistent(b, c, i-1, learner_idx);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);

  var s := b[i-1].replicas[learner_idx].replica.learner;
  var s' := b[i].replicas[learner_idx].replica.learner;

  if s'.max_ballot_seen == s.max_ballot_seen && s'.unexecuted_learner_state == s.unexecuted_learner_state
  {
    sender_idx, p := lemma_GetSent2bMessageFromLearnerState(b, c, i-1, learner_idx, opn, sender);
    lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
    return;
  }

  if && opn in s.unexecuted_learner_state
     && sender in s.unexecuted_learner_state[opn].received_2b_message_senders
     && s'.unexecuted_learner_state[opn].candidate_learned_value == s.unexecuted_learner_state[opn].candidate_learned_value
     && s'.max_ballot_seen == s.max_ballot_seen
  {
    sender_idx, p := lemma_GetSent2bMessageFromLearnerState(b, c, i-1, learner_idx, opn, sender);
    lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, learner_idx);
  assert ios[0].LIoOpReceive?;
  p := ios[0].r;
  sender_idx := GetReplicaIndex(p.src, c.config);

  if p.msg.val_2b != s'.unexecuted_learner_state[opn].candidate_learned_value
  {
    assert p.msg.bal_2b == s.max_ballot_seen;
    assert opn in s.unexecuted_learner_state;
    lemma_Received2bMessageSendersAlwaysNonempty(b, c, i-1, learner_idx, opn);
    var sender2 :| sender2 in s.unexecuted_learner_state[opn].received_2b_message_senders;
    var sender2_idx, p2 := lemma_GetSent2bMessageFromLearnerState(b, c, i-1, learner_idx, opn, sender2);

    var p_2a := lemma_2bMessageHasCorresponding2aMessage(b, c, i, p);
    var p2_2a := lemma_2bMessageHasCorresponding2aMessage(b, c, i, p2);
    lemma_2aMessagesFromSameBallotAndOperationMatch(b, c, i, p_2a, p2_2a);
  }
}
    
}
