include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"

module CommonProof__Actions_i {
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Constants_i
import opened LiveRSL__Message_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Replica_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened Temporal__Temporal_s
import opened Environment_s
import opened Collections__Maps2_s

predicate PacketProcessedViaIos(
  ps:RslState,
  ps':RslState,
  p:RslPacket,
  idx:int,
  ios:seq<RslIo>
  )
{
  && |ios| > 0
  && LIoOpReceive(p) == ios[0]
  && 0 <= idx < |ps.constants.config.replica_ids|
  && p.dst == ps.constants.config.replica_ids[idx]
  && ps.environment.nextStep == LEnvStepHostIos(p.dst, ios)
  && RslNextOneReplica(ps, ps', idx, ios)
  && LReplicaNextProcessPacket(ps.replicas[idx].replica, ps'.replicas[idx].replica, ios)
}

predicate PacketProcessedDuringAction(
  ps:RslState,
  p:RslPacket
  )
{
  ps.environment.nextStep.LEnvStepHostIos? && LIoOpReceive(p) in ps.environment.nextStep.ios
}

function{:opaque} PacketProcessedTemporal(
  b:Behavior<RslState>,
  p:RslPacket
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, PacketProcessedTemporal(b, p))} ::
               sat(i, PacketProcessedTemporal(b, p)) <==> PacketProcessedDuringAction(b[i], p)
{
  stepmap(imap i :: PacketProcessedDuringAction(b[i], p))
}

predicate PacketSentDuringAction(
  ps:RslState,
  p:RslPacket
  )
{
  ps.environment.nextStep.LEnvStepHostIos? && LIoOpSend(p) in ps.environment.nextStep.ios
}

function{:opaque} PacketSentTemporal(
  b:Behavior<RslState>,
  p:RslPacket
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, PacketSentTemporal(b, p))} ::
             sat(i, PacketSentTemporal(b, p)) <==> PacketSentDuringAction(b[i], p)
{
  stepmap(imap i :: PacketSentDuringAction(b[i], p))
}


lemma lemma_ActionThatChangesReplicaIsThatReplicasAction(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  host_index:int
  )
  returns (ios:seq<RslIo>)
  requires IsValidBehaviorPrefix(b, c, i+1)
  requires 0 <= i
  requires 0 <= host_index < |b[i].replicas|
  requires 0 <= host_index < |b[i+1].replicas|
  requires b[i+1].replicas[host_index] != b[i].replicas[host_index]
  ensures  b[i].environment.nextStep.LEnvStepHostIos?
  ensures  0 <= host_index < |c.config.replica_ids|
  ensures  b[i].environment.nextStep.actor == c.config.replica_ids[host_index]
  ensures  ios == b[i].environment.nextStep.ios
  ensures  RslNext(b[i], b[i+1])
  ensures  RslNextOneReplica(b[i], b[i+1], host_index, ios)
{
  lemma_AssumptionsMakeValidTransition(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i);
  assert RslNext(b[i], b[i+1]);
  ios :| RslNextOneReplica(b[i], b[i+1], host_index, ios);
}

lemma lemma_PacketProcessedImpliesPacketSent(
  ps:RslState,
  ps':RslState,
  idx:int,
  ios:seq<RslIo>,
  inp:RslPacket
  )
  requires RslNextOneReplica(ps, ps', idx, ios)
  requires LIoOpReceive(inp) in ios
  ensures  inp in ps.environment.sentPackets
{
  var id := ps.constants.config.replica_ids[idx];
  var e := ps.environment;
  var e' := ps'.environment;

  assert IsValidLIoOp(LIoOpReceive(inp), id, ps.environment);
  assert inp in e.sentPackets;
}

lemma lemma_PacketProcessedImpliesPacketSentAlt(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int,
  inp:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i+1)
  requires 0 <= i
  requires 0 <= idx < |c.config.replica_ids|
  requires b[i].environment.nextStep.LEnvStepHostIos?
  requires b[i].environment.nextStep.actor == c.config.replica_ids[idx]
  requires LIoOpReceive(inp) in b[i].environment.nextStep.ios
  ensures  inp in b[i].environment.sentPackets
{
  var ps := b[i];
  var ps' := b[i+1];

  lemma_AssumptionsMakeValidTransition(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i);

  var id := ps.constants.config.replica_ids[idx];
  var e := ps.environment;
  var e' := ps'.environment;

  assert IsValidLIoOp(LIoOpReceive(inp), id, ps.environment);
  assert inp in e.sentPackets;
}

}
