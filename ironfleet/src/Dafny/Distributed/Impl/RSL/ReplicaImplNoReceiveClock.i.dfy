include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/RSL/Replica.i.dfy"
include "ReplicaModel.i.dfy"
include "ReplicaImplLemmas.i.dfy"
include "ReplicaImplClass.i.dfy"
include "ReplicaImplDelivery.i.dfy"
include "UdpRSL.i.dfy"
include "CClockReading.i.dfy"

module LiveRSL__ReplicaImplNoReceiveClock_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened LiveRSL__CClockReading_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__Environment_i
import opened LiveRSL__QRelations_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ReplicaModel_i
import opened LiveRSL__ReplicaModel_Part3_i
import opened LiveRSL__ReplicaModel_Part4_i
import opened LiveRSL__ReplicaModel_Part5_i
import opened LiveRSL__ReplicaState_i
import opened LiveRSL__ReplicaImplLemmas_i
import opened LiveRSL__ReplicaImplClass_i
import opened LiveRSL__ReplicaImplDelivery_i
import opened LiveRSL__Types_i
import opened LiveRSL__UdpRSL_i
import opened Common__UdpClient_i
import opened Environment_s

lemma lemma_ReplicaNoReceiveReadClockNextHelper2(
  oldHistory:seq<UdpEvent>,
  preDeliveryHistory:seq<UdpEvent>,
  finalHistory:seq<UdpEvent>,
  log_head:seq<UdpEvent>,
  log_tail:seq<UdpEvent>,
  log_head_and_tail:seq<UdpEvent>
  )
  requires preDeliveryHistory == oldHistory + log_head
  requires finalHistory == preDeliveryHistory + log_tail
  requires log_head_and_tail == log_head + log_tail
  requires forall io :: io in log_head ==> !io.LIoOpSend?
  requires OnlySentMarshallableData(log_tail)
  ensures  finalHistory == oldHistory + log_head_and_tail
  ensures  OnlySentMarshallableData(log_head_and_tail)
{
}

lemma lemma_RevealQFromReplicaNextMaybeNominateValueAndSend2aPostconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  clock:CClockReading,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Preconditions(replica)
  requires Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Postconditions(replica, replica', clock, packets_sent)
  ensures  Q_LReplica_Next_ReadClock_MaybeNominateValueAndSend2a(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                                                 AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
{
  reveal Q_LReplica_Next_ReadClock_MaybeNominateValueAndSend2a();
}

method {:fuel ReplicaStateIsValid,0,0}{:timeLimitMultiplier 3} ReplicaNoReceiveReadClockNextMaybeNominateValueAndSend2a(
  r:ReplicaImpl
  ) returns (
  ok:bool,
  ghost udpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.nextActionIndex == 3
  requires r.Valid()
  modifies r.Repr
  ensures r.Repr == old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==> 
            && r.Valid()
            && r.Env() == old(r.Env())
            && r.nextActionIndex == old(r.nextActionIndex)
            && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
            && OnlySentMarshallableData(udpEventLog)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && old(r.Env().udp.history()) + udpEventLog == r.Env().udp.history()
{
  ghost var replica_old := r.replica;
  var clock,udpEvent0 := ReadClock(r.udpClient);
  ghost var io0 := LIoOpReadClock(clock.t as int);

  var sent_packets;
  r.replica,sent_packets := Replica_Next_Spontaneous_MaybeNominateValueAndSend2a(r.replica, clock);
  lemma_RevealQFromReplicaNextMaybeNominateValueAndSend2aPostconditions(replica_old, r.replica, clock, sent_packets);

  assert r.Valid();
  ghost var preDeliveryHistory := r.Env().udp.history();
  ghost var log_tail, ios_tail;
  ok, log_tail, ios_tail := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  ghost var ios_head := [io0];
  ghost var log_head := [udpEvent0];
  ios := ios_head + ios_tail;
  udpEventLog := log_head + log_tail;

  lemma_ReplicaNoReceiveReadClockNextHelper2(old(r.Env().udp.history()), preDeliveryHistory, r.Env().udp.history(),
                                             log_head, log_tail, udpEventLog);
  lemma_ReplicaNoReceiveReadClockNextHelper(
            old(r.replica), r.replica, clock, sent_packets, r.nextActionIndex as int,
            ios, io0, ios_head, ios_tail, 
            udpEvent0, log_head, log_tail, udpEventLog);
}

lemma lemma_RevealQFromReplicaNextCheckForViewTimeoutPostconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  clock:CClockReading,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_ReadClock_CheckForViewTimeout_Preconditions(replica)
  requires Replica_Next_ReadClock_CheckForViewTimeout_Postconditions(replica, replica', clock, packets_sent)
  ensures  Q_LReplica_Next_ReadClock_CheckForViewTimeout(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                                         AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
{
  reveal Q_LReplica_Next_ReadClock_CheckForViewTimeout();
}

method {:fuel ReplicaStateIsValid,0,0}{:timeLimitMultiplier 3} ReplicaNoReceiveReadClockNextCheckForViewTimeout(
  r:ReplicaImpl
  ) returns (
  ok:bool,
  ghost udpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.nextActionIndex == 7
  requires r.Valid()
  modifies r.Repr, r.cur_req_set, r.prev_req_set  //, r.reply_cache_mutable;
  ensures r.Repr == old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env())
  ensures ok ==>
            && r.Valid()
            && r.Env() == old(r.Env())
            && r.nextActionIndex == old(r.nextActionIndex)
            && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
            && OnlySentMarshallableData(udpEventLog)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && old(r.Env().udp.history()) + udpEventLog == r.Env().udp.history()
{
  ghost var replica_old := r.replica;
  var clock,udpEvent0 := ReadClock(r.udpClient);
  ghost var io0 := LIoOpReadClock(clock.t as int);

  var sent_packets;
  r.replica,sent_packets := Replica_Next_ReadClock_CheckForViewTimeout(r.replica, clock, r.cur_req_set, r.prev_req_set);
  lemma_RevealQFromReplicaNextCheckForViewTimeoutPostconditions(replica_old, r.replica, clock, sent_packets);

  assert r.Valid();
  ghost var preDeliveryHistory := r.Env().udp.history();
  ghost var log_tail, ios_tail;
  ok, log_tail, ios_tail := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  ghost var ios_head := [io0];
  ghost var log_head := [udpEvent0];
  ios := ios_head + ios_tail;
  udpEventLog := log_head + log_tail;

  lemma_ReplicaNoReceiveReadClockNextHelper2(old(r.Env().udp.history()), preDeliveryHistory, r.Env().udp.history(),
                                             log_head, log_tail, udpEventLog);
  lemma_ReplicaNoReceiveReadClockNextHelper(
            old(r.replica), r.replica, clock, sent_packets, r.nextActionIndex as int,
            ios, io0, ios_head, ios_tail, 
            udpEvent0, log_head, log_tail, udpEventLog);
}

lemma lemma_RevealQFromReplicaNextCheckForQuorumOfViewSuspicionsPostconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  clock:CClockReading,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Preconditions(replica)
  requires Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Postconditions(replica, replica', clock, packets_sent)
  ensures  Q_LReplica_Next_ReadClock_CheckForQuorumOfViewSuspicions(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                                                    AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
{
  reveal Q_LReplica_Next_ReadClock_CheckForQuorumOfViewSuspicions();
}

method {:fuel ReplicaStateIsValid,0,0}{:timeLimitMultiplier 3} ReplicaNoReceiveReadClockNextCheckForQuorumOfViewSuspicions(
  r:ReplicaImpl
  ) returns (
  ok:bool,
  ghost udpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.nextActionIndex == 8
  requires r.Valid()
  modifies r.Repr, r.cur_req_set, r.prev_req_set  //, r.reply_cache_mutable
  ensures r.Repr == old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env())
  ensures ok ==>
            && r.Valid()
            && r.Env() == old(r.Env())
            && r.nextActionIndex == old(r.nextActionIndex)
            && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
            && OnlySentMarshallableData(udpEventLog)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && old(r.Env().udp.history()) + udpEventLog == r.Env().udp.history()
{
  ghost var replica_old := r.replica;
  var clock,udpEvent0 := ReadClock(r.udpClient);
  ghost var io0 := LIoOpReadClock(clock.t as int);

  var sent_packets;
  r.replica,sent_packets := Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions(r.replica, clock, r.cur_req_set, r.prev_req_set);
  lemma_RevealQFromReplicaNextCheckForQuorumOfViewSuspicionsPostconditions(replica_old, r.replica, clock, sent_packets);
        
  assert r.Valid();
  ghost var preDeliveryHistory := r.Env().udp.history();
  ghost var log_tail, ios_tail;
  ok, log_tail, ios_tail := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  ghost var ios_head := [io0];
  ghost var log_head := [udpEvent0];
  ios := ios_head + ios_tail;
  udpEventLog := log_head + log_tail;

  lemma_ReplicaNoReceiveReadClockNextHelper2(old(r.Env().udp.history()), preDeliveryHistory, r.Env().udp.history(),
                                             log_head, log_tail, udpEventLog);
  lemma_ReplicaNoReceiveReadClockNextHelper(
            old(r.replica), r.replica, clock, sent_packets, r.nextActionIndex as int,
            ios, io0, ios_head, ios_tail, 
            udpEvent0, log_head, log_tail, udpEventLog);
}

lemma lemma_RevealQFromReplicaNextMaybeSendHeartbeatPostconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  clock:CClockReading,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica)
  requires Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions(replica, replica', clock, packets_sent)
  ensures  Q_LReplica_Next_ReadClock_MaybeSendHeartbeat(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                                        AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
{
  reveal Q_LReplica_Next_ReadClock_MaybeSendHeartbeat();
}

method {:fuel ReplicaStateIsValid,0,0}{:timeLimitMultiplier 3} ReplicaNoReceiveReadClockNextMaybeSendHeartbat(
  r:ReplicaImpl
  ) returns (
  ok:bool,
  ghost udpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.nextActionIndex == 9
  requires r.Valid()
  modifies r.Repr
  ensures r.Repr == old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env())
  ensures ok ==>
            && r.Valid()
            && r.Env() == old(r.Env())
            && r.nextActionIndex == old(r.nextActionIndex)
            && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
            && OnlySentMarshallableData(udpEventLog)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && old(r.Env().udp.history()) + udpEventLog == r.Env().udp.history()
{
  ghost var replica_old := r.replica;
  var clock,udpEvent0 := ReadClock(r.udpClient);
  ghost var io0 := LIoOpReadClock(clock.t as int);

  var sent_packets;
  r.replica,sent_packets := Replica_Next_ReadClock_MaybeSendHeartbeat(r.replica, clock);
  lemma_RevealQFromReplicaNextMaybeSendHeartbeatPostconditions(replica_old, r.replica, clock, sent_packets);

  assert r.Valid();
  ghost var preDeliveryHistory := r.Env().udp.history();
  ghost var log_tail, ios_tail;
  ok, log_tail, ios_tail := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  ghost var ios_head := [io0];
  ghost var log_head := [udpEvent0];
  ios := ios_head + ios_tail;
  udpEventLog := log_head + log_tail;

  lemma_ReplicaNoReceiveReadClockNextHelper2(old(r.Env().udp.history()), preDeliveryHistory, r.Env().udp.history(),
                                             log_head, log_tail, udpEventLog);
  lemma_ReplicaNoReceiveReadClockNextHelper(
            old(r.replica), r.replica, clock, sent_packets, r.nextActionIndex as int,
            ios, io0, ios_head, ios_tail, 
            udpEvent0, log_head, log_tail, udpEventLog);
}

method {:fuel ReplicaStateIsValid,0,0} Replica_NoReceive_ReadClock_Next(
  r:ReplicaImpl
  ) returns (
  ok:bool,
  ghost udpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.nextActionIndex == 3 || 7<=r.nextActionIndex<=9
  requires r.Valid()
  modifies r.Repr, r.cur_req_set, r.prev_req_set  //, r.reply_cache_mutable;
  ensures r.Repr == old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env())
  ensures ok ==>
            && r.Valid()
            && r.Env() == old(r.Env())
            && r.nextActionIndex == old(r.nextActionIndex)
            && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
            && OnlySentMarshallableData(udpEventLog)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && old(r.Env().udp.history()) + udpEventLog == r.Env().udp.history()
{
  if r.nextActionIndex == 3 {
    ok, udpEventLog, ios := ReplicaNoReceiveReadClockNextMaybeNominateValueAndSend2a(r);
  } else if r.nextActionIndex == 7 {
    ok, udpEventLog, ios := ReplicaNoReceiveReadClockNextCheckForViewTimeout(r);
  } else if r.nextActionIndex == 8 {
    ok, udpEventLog, ios := ReplicaNoReceiveReadClockNextCheckForQuorumOfViewSuspicions(r);
  } else if r.nextActionIndex == 9 {
    ok, udpEventLog, ios := ReplicaNoReceiveReadClockNextMaybeSendHeartbat(r);
  }
}

}
