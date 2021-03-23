include "../DistributedSystem.i.dfy"

module CommonProof__PacketSending_i {

import opened LiveRSL__Acceptor_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Executor_i
import opened LiveRSL__Replica_i
import opened Environment_s

lemma lemma_ActionThatSendsPacketIsActionOfSource(
  ps:RslState,
  ps':RslState,
  p:RslPacket
  ) returns (
  idx:int,
  ios:seq<RslIo>
  )
  requires p.src in ps.constants.config.replica_ids
  requires p in ps'.environment.sentPackets
  requires p !in ps.environment.sentPackets
  requires RslNext(ps, ps')
  ensures  0 <= idx < |ps.constants.config.replica_ids|
  ensures  0 <= idx < |ps'.constants.config.replica_ids|
  ensures  p.src == ps.constants.config.replica_ids[idx]
  ensures  RslNextOneReplica(ps, ps', idx, ios)
  ensures  LIoOpSend(p) in ios
{
  assert ps.environment.nextStep.LEnvStepHostIos?;
  assert LIoOpSend(p) in ps.environment.nextStep.ios;
  idx, ios :| RslNextOneReplica(ps, ps', idx, ios) && LIoOpSend(p) in ios;
}

lemma lemma_ActionThatSends1aIsMaybeEnterNewViewAndSend1a(
  ps:RslState,
  ps':RslState,
  p:RslPacket
  ) returns (
  idx:int,
  ios:seq<RslIo>
  )
  requires p.src in ps.constants.config.replica_ids
  requires p.msg.RslMessage_1a?
  requires p in ps'.environment.sentPackets
  requires p !in ps.environment.sentPackets
  requires RslNext(ps, ps')
  ensures  0 <= idx < |ps.constants.config.replica_ids|
  ensures  0 <= idx < |ps'.constants.config.replica_ids|
  ensures  p.src == ps.constants.config.replica_ids[idx]
  ensures  RslNextOneReplica(ps, ps', idx, ios)
  ensures  LIoOpSend(p) in ios
  ensures  LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(ps.replicas[idx].replica, ps'.replicas[idx].replica,
                                                             ExtractSentPacketsFromIos(ios))
{
  assert ps.environment.nextStep.LEnvStepHostIos?;
  assert LIoOpSend(p) in ps.environment.nextStep.ios;
  idx, ios :| RslNextOneReplica(ps, ps', idx, ios) && LIoOpSend(p) in ios;
  var nextActionIndex := ps.replicas[idx].nextActionIndex;
  if nextActionIndex != 1
  {
    assert false;
  }
}

lemma lemma_ActionThatSends1bIsProcess1a(
  ps:RslState,
  ps':RslState,
  p:RslPacket
  ) returns (
  idx:int,
  ios:seq<RslIo>
  )
  requires p.src in ps.constants.config.replica_ids
  requires p.msg.RslMessage_1b?
  requires p in ps'.environment.sentPackets
  requires p !in ps.environment.sentPackets
  requires RslNext(ps, ps')
  ensures  0 <= idx < |ps.constants.config.replica_ids|
  ensures  0 <= idx < |ps'.constants.config.replica_ids|
  ensures  p.src == ps.constants.config.replica_ids[idx]
  ensures  RslNextOneReplica(ps, ps', idx, ios)
  ensures  |ios| > 0
  ensures  ios[0].LIoOpReceive?
  ensures  ios[0].r.msg.RslMessage_1a?
  ensures  LIoOpSend(p) in ios
  ensures  LReplicaNextProcessPacketWithoutReadingClock(ps.replicas[idx].replica, ps'.replicas[idx].replica, ios)
  ensures  LAcceptorProcess1a(ps.replicas[idx].replica.acceptor, ps'.replicas[idx].replica.acceptor, ios[0].r, [p])
{
  assert ps.environment.nextStep.LEnvStepHostIos?;
  assert LIoOpSend(p) in ps.environment.nextStep.ios;
  idx, ios :| RslNextOneReplica(ps, ps', idx, ios) && LIoOpSend(p) in ios;
}

lemma lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(
  ps:RslState,
  ps':RslState,
  p:RslPacket
  ) returns (
  idx:int,
  ios:seq<RslIo>
  )
  requires p.src in ps.constants.config.replica_ids
  requires p.msg.RslMessage_2a?
  requires p in ps'.environment.sentPackets
  requires p !in ps.environment.sentPackets
  requires RslNext(ps, ps')
  ensures  0 <= idx < |ps.constants.config.replica_ids|
  ensures  0 <= idx < |ps'.constants.config.replica_ids|
  ensures  p.src == ps.constants.config.replica_ids[idx]
  ensures  RslNextOneReplica(ps, ps', idx, ios)
  ensures  LIoOpSend(p) in ios
  ensures  SpontaneousIos(ios, 1)
  ensures  LReplicaNextReadClockMaybeNominateValueAndSend2a(ps.replicas[idx].replica, ps'.replicas[idx].replica,
                                                            SpontaneousClock(ios), ExtractSentPacketsFromIos(ios))
{
  assert ps.environment.nextStep.LEnvStepHostIos?;
  assert LIoOpSend(p) in ps.environment.nextStep.ios;
  idx, ios :| RslNextOneReplica(ps, ps', idx, ios) && LIoOpSend(p) in ios;
  var nextActionIndex := ps.replicas[idx].nextActionIndex;
  if nextActionIndex != 3
  {
    assert false;
  }
}

lemma lemma_ActionThatSends2bIsProcess2a(
  ps:RslState,
  ps':RslState,
  p:RslPacket
  ) returns (
  idx:int,
  ios:seq<RslIo>
  )
  requires p.src in ps.constants.config.replica_ids
  requires p.msg.RslMessage_2b?
  requires p in ps'.environment.sentPackets
  requires p !in ps.environment.sentPackets
  requires RslNext(ps, ps')
  ensures  0 <= idx < |ps.constants.config.replica_ids|
  ensures  0 <= idx < |ps'.constants.config.replica_ids|
  ensures  p.src == ps.constants.config.replica_ids[idx]
  ensures  RslNextOneReplica(ps, ps', idx, ios)
  ensures  |ios| > 0
  ensures  ios[0].LIoOpReceive?
  ensures  LIoOpSend(p) in ios
  ensures  LReplicaNextProcess2a(ps.replicas[idx].replica, ps'.replicas[idx].replica, ios[0].r, ExtractSentPacketsFromIos(ios))
{
  assert ps.environment.nextStep.LEnvStepHostIos?;
  assert LIoOpSend(p) in ps.environment.nextStep.ios;
  idx, ios :| RslNextOneReplica(ps, ps', idx, ios) && LIoOpSend(p) in ios;
}

lemma lemma_ActionThatSendsHeartbeatIsMaybeSendHeartbeat(
  ps:RslState,
  ps':RslState,
  p:RslPacket
  ) returns (
  idx:int,
  ios:seq<RslIo>
  )
  requires p.src in ps.constants.config.replica_ids
  requires p.msg.RslMessage_Heartbeat?
  requires p in ps'.environment.sentPackets
  requires p !in ps.environment.sentPackets
  requires RslNext(ps, ps')
  ensures  0 <= idx < |ps.constants.config.replica_ids|
  ensures  0 <= idx < |ps'.constants.config.replica_ids|
  ensures  p.src == ps.constants.config.replica_ids[idx]
  ensures  RslNextOneReplica(ps, ps', idx, ios)
  ensures  |ios| > 0
  ensures  ios[0].LIoOpReadClock?
  ensures  LIoOpSend(p) in ios
  ensures  SpontaneousIos(ios, 1)
  ensures  LReplicaNextReadClockMaybeSendHeartbeat(ps.replicas[idx].replica, ps'.replicas[idx].replica,
                                                   SpontaneousClock(ios), ExtractSentPacketsFromIos(ios))
{
  assert ps.environment.nextStep.LEnvStepHostIos?;
  assert LIoOpSend(p) in ps.environment.nextStep.ios;
  idx, ios :| RslNextOneReplica(ps, ps', idx, ios) && LIoOpSend(p) in ios;
}

lemma lemma_ActionThatSendsAppStateRequestIsProcessStartingPhase2(
  ps:RslState,
  ps':RslState,
  p:RslPacket
  ) returns (
  idx:int,
  ios:seq<RslIo>
  )
  requires p.src in ps.constants.config.replica_ids
  requires p.msg.RslMessage_AppStateRequest?
  requires p in ps'.environment.sentPackets
  requires p !in ps.environment.sentPackets
  requires RslNext(ps, ps')
  ensures  0 <= idx < |ps.constants.config.replica_ids|
  ensures  0 <= idx < |ps'.constants.config.replica_ids|
  ensures  p.src == ps.constants.config.replica_ids[idx]
  ensures  RslNextOneReplica(ps, ps', idx, ios)
  ensures  |ios| > 0
  ensures  ios[0].LIoOpReceive?
  ensures  ios[0].r.msg.RslMessage_StartingPhase2?
  ensures  LIoOpSend(p) in ios
  ensures  LReplicaNextProcessPacketWithoutReadingClock(ps.replicas[idx].replica, ps'.replicas[idx].replica, ios)
  ensures  LExecutorProcessStartingPhase2(ps.replicas[idx].replica.executor, ps'.replicas[idx].replica.executor,
                                          ios[0].r, ExtractSentPacketsFromIos(ios))
{
  assert ps.environment.nextStep.LEnvStepHostIos?;
  assert LIoOpSend(p) in ps.environment.nextStep.ios;
  idx, ios :| RslNextOneReplica(ps, ps', idx, ios) && LIoOpSend(p) in ios;
}

lemma lemma_ActionThatSendsAppStateSupplyIsProcessAppStateRequest(
  ps:RslState,
  ps':RslState,
  p:RslPacket
  ) returns (
  idx:int,
  ios:seq<RslIo>
  )
  requires p.src in ps.constants.config.replica_ids
  requires p.msg.RslMessage_AppStateSupply?
  requires p in ps'.environment.sentPackets
  requires p !in ps.environment.sentPackets
  requires RslNext(ps, ps')
  ensures  0 <= idx < |ps.constants.config.replica_ids|
  ensures  0 <= idx < |ps'.constants.config.replica_ids|
  ensures  p.src == ps.constants.config.replica_ids[idx]
  ensures  RslNextOneReplica(ps, ps', idx, ios)
  ensures  |ios| > 0
  ensures  ios[0].LIoOpReceive?
  ensures  ios[0].r.msg.RslMessage_AppStateRequest?
  ensures  LIoOpSend(p) in ios
  ensures  LReplicaNextProcessPacketWithoutReadingClock(ps.replicas[idx].replica, ps'.replicas[idx].replica, ios)
  ensures  LExecutorProcessAppStateRequest(ps.replicas[idx].replica.executor, ps'.replicas[idx].replica.executor, ios[0].r, [p])
{
  assert ps.environment.nextStep.LEnvStepHostIos?;
  assert LIoOpSend(p) in ps.environment.nextStep.ios;
  idx, ios :| RslNextOneReplica(ps, ps', idx, ios) && LIoOpSend(p) in ios;
}

lemma lemma_ActionThatSendsStartingPhase2IsMaybeEnterPhase2(
  ps:RslState,
  ps':RslState,
  p:RslPacket
  ) returns (
  idx:int,
  ios:seq<RslIo>
  )
  requires p.src in ps.constants.config.replica_ids
  requires p.msg.RslMessage_StartingPhase2?
  requires p in ps'.environment.sentPackets
  requires p !in ps.environment.sentPackets
  requires RslNext(ps, ps')
  ensures  0 <= idx < |ps.constants.config.replica_ids|
  ensures  0 <= idx < |ps'.constants.config.replica_ids|
  ensures  p.src == ps.constants.config.replica_ids[idx]
  ensures  RslNextOneReplica(ps, ps', idx, ios)
  ensures  LIoOpSend(p) in ios
  ensures  LReplicaNextSpontaneousMaybeEnterPhase2(ps.replicas[idx].replica, ps'.replicas[idx].replica, ExtractSentPacketsFromIos(ios))
{
  assert ps.environment.nextStep.LEnvStepHostIos?;
  assert LIoOpSend(p) in ps.environment.nextStep.ios;
  idx, ios :| RslNextOneReplica(ps, ps', idx, ios) && LIoOpSend(p) in ios;
  var nextActionIndex := ps.replicas[idx].nextActionIndex;
  if nextActionIndex != 2
  {
    assert false;
  }
}
    
}
