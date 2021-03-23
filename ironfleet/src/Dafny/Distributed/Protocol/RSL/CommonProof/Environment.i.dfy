include "../DistributedSystem.i.dfy"
include "../../../Common/Logic/Temporal/Heuristics.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"

module CommonProof__Environment_i {
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened Temporal__Temporal_s
import opened Temporal__Heuristics_i
import opened Temporal__Rules_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened Environment_s

lemma lemma_PacketStaysInSentPackets(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  j:int,
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, j)
  requires 0 <= i <= j
  requires p in b[i].environment.sentPackets
  ensures  p in b[j].environment.sentPackets
{
  if j == i
  {
  }
  else
  {
    lemma_PacketStaysInSentPackets(b, c, i, j-1, p);
    lemma_AssumptionsMakeValidTransition(b, c, j-1);
  }
}

lemma lemma_PacketSetStaysInSentPackets(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  j:int,
  packets:set<RslPacket>
  )
  requires IsValidBehaviorPrefix(b, c, j)
  requires 0 <= i <= j
  requires packets <= b[i].environment.sentPackets
  ensures  packets <= b[j].environment.sentPackets
{
  forall p | p in packets
    ensures p in b[j].environment.sentPackets
  {
    lemma_PacketStaysInSentPackets(b, c, i, j, p);
  }
}

}
