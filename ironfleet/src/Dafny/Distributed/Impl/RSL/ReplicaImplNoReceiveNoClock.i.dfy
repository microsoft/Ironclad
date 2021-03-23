include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/RSL/Replica.i.dfy"
include "ReplicaModel.i.dfy"
include "ReplicaImplLemmas.i.dfy"
include "ReplicaImplClass.i.dfy"
include "ReplicaImplDelivery.i.dfy"
include "UdpRSL.i.dfy"
include "CClockReading.i.dfy"

module LiveRSL__ReplicaImplNoReceiveNoClock_i {

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
import opened LiveRSL__ReplicaImplLemmas_i
import opened LiveRSL__ReplicaImplClass_i
import opened LiveRSL__ReplicaImplDelivery_i
import opened LiveRSL__ReplicaModel_i
import opened LiveRSL__ReplicaModel_Part3_i
import opened LiveRSL__ReplicaModel_Part5_i
import opened LiveRSL__ReplicaState_i
import opened LiveRSL__Types_i
import opened LiveRSL__UdpRSL_i
import opened Common__UdpClient_i
import opened Environment_s

lemma lemma_RevealQFromReplicaNextSpontaneousMaybeEnterNewViewAndSend1aPostconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(replica)
  requires Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions(replica, replica', packets_sent)
  ensures  Q_LReplica_Next_Spontaneous_MaybeEnterNewViewAndSend1a(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                                                  AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
{
  reveal Q_LReplica_Next_Spontaneous_MaybeEnterNewViewAndSend1a();
}

method ReplicaNoReceiveNoClockNextSpontaneousMaybeEnterNewViewAndSend1a(r:ReplicaImpl)
  returns (ok:bool, ghost udpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
  requires r.nextActionIndex==1
  requires r.Valid()
  modifies r.Repr
  ensures r.Repr == old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && OnlySentMarshallableData(udpEventLog)
            && old(r.Env().udp.history()) + udpEventLog == r.Env().udp.history()
{
  ghost var replica_old := r.replica;
  var sent_packets;
  r.replica,sent_packets := Replica_Next_Spontaneous_MaybeEnterNewViewAndSend1a(r.replica);
  lemma_RevealQFromReplicaNextSpontaneousMaybeEnterNewViewAndSend1aPostconditions(replica_old, r.replica, sent_packets);

  ok, udpEventLog, ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }
  assert old(r.Env().udp.history()) + udpEventLog == r.Env().udp.history(); // deleteme

  assert SpontaneousIos(ios, 0);
  assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
  assert r.Env() == old(r.Env());
  assert RawIoConsistentWithSpecIO(udpEventLog, ios);
  lemma_EstablishQLReplicaNoReceiveNextFromNoClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), r.nextActionIndex as int, ios);
}

lemma lemma_RevealQFromReplicaNextSpontaneousMaybeEnterPhase2Postconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_MaybeEnterPhase2_Preconditions(replica)
  requires Replica_Next_MaybeEnterPhase2_Postconditions(replica, replica', packets_sent)
  ensures  Q_LReplica_Next_Spontaneous_MaybeEnterPhase2(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                                        AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
{
  reveal Q_LReplica_Next_Spontaneous_MaybeEnterPhase2();
}

method ReplicaNoReceiveNoClockNextSpontaneousMaybeEnterPhase2(r:ReplicaImpl)
  returns (ok:bool, ghost udpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
  requires r.nextActionIndex==2
  requires r.Valid()
  modifies r.Repr
  ensures r.Repr == old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && OnlySentMarshallableData(udpEventLog)
            && old(r.Env().udp.history()) + udpEventLog == r.Env().udp.history()
{
  ghost var replica_old := r.replica;
  var sent_packets;
  r.replica,sent_packets := Replica_Next_Spontaneous_MaybeEnterPhase2(r.replica);
  lemma_RevealQFromReplicaNextSpontaneousMaybeEnterPhase2Postconditions(replica_old, r.replica, sent_packets);

  ok, udpEventLog, ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }
  assert old(r.Env().udp.history()) + udpEventLog == r.Env().udp.history(); // deleteme

  assert SpontaneousIos(ios, 0);
  assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
  assert r.Env() == old(r.Env());
  assert RawIoConsistentWithSpecIO(udpEventLog, ios);
  lemma_EstablishQLReplicaNoReceiveNextFromNoClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), r.nextActionIndex as int, ios);
}

lemma lemma_RevealQFromReplicaNextSpontaneousTruncateLogBasedOnCheckpointsPostconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica)
  requires Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions(replica, replica', packets_sent)
  ensures  Q_LReplica_Next_Spontaneous_TruncateLogBasedOnCheckpoints(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                                                     AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Spontaneous_TruncateLogBasedOnCheckpoints();
}

method ReplicaNoReceiveNoClockNextSpontaneousTruncateLogBasedOnCheckpoints(r:ReplicaImpl)
  returns (ok:bool, ghost udpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
  requires r.nextActionIndex==4
  requires r.Valid()
  modifies r.Repr
  ensures r.Repr == old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && OnlySentMarshallableData(udpEventLog)
            && old(r.Env().udp.history()) + udpEventLog == r.Env().udp.history()
{
  ghost var replica_old := r.replica;
  var sent_packets;
  r.replica,sent_packets := Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints(r.replica);
  lemma_RevealQFromReplicaNextSpontaneousTruncateLogBasedOnCheckpointsPostconditions(replica_old, r.replica, sent_packets);

  ok, udpEventLog, ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }
  assert old(r.Env().udp.history()) + udpEventLog == r.Env().udp.history(); // deleteme

  assert SpontaneousIos(ios, 0);
  assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
  assert r.Env() == old(r.Env());
  assert RawIoConsistentWithSpecIO(udpEventLog, ios);
  lemma_EstablishQLReplicaNoReceiveNextFromNoClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), r.nextActionIndex as int, ios);
}

lemma lemma_RevealQFromReplicaNextSpontaneousMaybeMakeDecisionPostconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica)
  requires Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(replica, replica', packets_sent)
  ensures  Q_LReplica_Next_Spontaneous_MaybeMakeDecision(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                                         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
{
  reveal Q_LReplica_Next_Spontaneous_MaybeMakeDecision();
}

method ReplicaNoReceiveNoClockNextSpontaneousMaybeMakeDecision(r:ReplicaImpl)
  returns (ok:bool, ghost udpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
  requires r.nextActionIndex==5
  requires r.Valid()
  modifies r.Repr
  ensures r.Repr == old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && OnlySentMarshallableData(udpEventLog)
            && old(r.Env().udp.history()) + udpEventLog == r.Env().udp.history()
{
  ghost var replica_old := r.replica;
  var sent_packets;
  r.replica,sent_packets := Replica_Next_Spontaneous_MaybeMakeDecision(r.replica);
  lemma_RevealQFromReplicaNextSpontaneousMaybeMakeDecisionPostconditions(replica_old, r.replica, sent_packets);

  ok, udpEventLog, ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }
  assert old(r.Env().udp.history()) + udpEventLog == r.Env().udp.history(); // deleteme

  assert SpontaneousIos(ios, 0);
  assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
  assert r.Env() == old(r.Env());
  assert RawIoConsistentWithSpecIO(udpEventLog, ios);
  lemma_EstablishQLReplicaNoReceiveNextFromNoClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), r.nextActionIndex as int, ios);
}

lemma lemma_RevealQFromReplicaNextSpontaneousMaybeExecutePostconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica)
  requires Replica_Next_Spontaneous_MaybeExecute_Postconditions(replica, replica', packets_sent)
  ensures  Q_LReplica_Next_Spontaneous_MaybeExecute(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                                    AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Spontaneous_MaybeExecute();
}

method ReplicaNoReceiveNoClockNextSpontaneousMaybeExecute(r:ReplicaImpl)
  returns (ok:bool, ghost udpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
  requires r.nextActionIndex==6
  requires r.Valid()
  modifies r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures r.Repr == old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && OnlySentMarshallableData(udpEventLog)
            && old(r.Env().udp.history()) + udpEventLog == r.Env().udp.history()
{
  ghost var replica_old := r.replica;
  var sent_packets;
  r.replica,sent_packets := Replica_Next_Spontaneous_MaybeExecute(r.replica, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable);
  lemma_RevealQFromReplicaNextSpontaneousMaybeExecutePostconditions(replica_old, r.replica, sent_packets);

  ok, udpEventLog, ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }
  assert old(r.Env().udp.history()) + udpEventLog == r.Env().udp.history(); // deleteme

  assert SpontaneousIos(ios, 0);
  assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
  assert r.Env() == old(r.Env());
  assert RawIoConsistentWithSpecIO(udpEventLog, ios);
  lemma_EstablishQLReplicaNoReceiveNextFromNoClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), r.nextActionIndex as int, ios);
}

method Replica_NoReceive_NoClock_Next(r:ReplicaImpl) returns (ok:bool, ghost udpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
  requires r.nextActionIndex==1 || r.nextActionIndex==2 || r.nextActionIndex==4 || r.nextActionIndex==5 || r.nextActionIndex==6
  requires r.Valid()
  modifies r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures r.Repr == old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && OnlySentMarshallableData(udpEventLog)
            && old(r.Env().udp.history()) + udpEventLog == r.Env().udp.history()
{
  if r.nextActionIndex == 1 {
    ok, udpEventLog, ios := ReplicaNoReceiveNoClockNextSpontaneousMaybeEnterNewViewAndSend1a(r);
  } else if r.nextActionIndex == 2 {
    ok, udpEventLog, ios := ReplicaNoReceiveNoClockNextSpontaneousMaybeEnterPhase2(r);
  } else if r.nextActionIndex == 4 {
    ok, udpEventLog, ios := ReplicaNoReceiveNoClockNextSpontaneousTruncateLogBasedOnCheckpoints(r);
  } else if r.nextActionIndex == 5 {
    ok, udpEventLog, ios := ReplicaNoReceiveNoClockNextSpontaneousMaybeMakeDecision(r);
  } else if r.nextActionIndex == 6 {
    ok, udpEventLog, ios := ReplicaNoReceiveNoClockNextSpontaneousMaybeExecute(r);
  }
}

}
