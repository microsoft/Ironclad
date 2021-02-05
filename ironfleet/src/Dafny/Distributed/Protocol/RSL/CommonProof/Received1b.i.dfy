include "Assumptions.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"

module CommonProof__Received1b_i {

import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened CommonProof__PacketSending_i
import opened Temporal__Temporal_s

lemma lemma_PacketInReceived1bWasSent(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  replica_idx:int,
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= replica_idx < |b[i].replicas|
  requires p in b[i].replicas[replica_idx].replica.proposer.received_1b_packets
  ensures  p in b[i].environment.sentPackets
  ensures  p.src in c.config.replica_ids
{
  if i == 0
  {
    return;
  }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  var s := b[i-1].replicas[replica_idx].replica.proposer;
  var s' := b[i].replicas[replica_idx].replica.proposer;

  if p in s.received_1b_packets
  {
    lemma_PacketInReceived1bWasSent(b, c, i-1, replica_idx, p);
    assert p in b[i].environment.sentPackets;
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, replica_idx);
}

}
