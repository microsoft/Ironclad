include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/RSL/Replica.i.dfy"
include "ReplicaModel.i.dfy"
include "ReplicaImplLemmas.i.dfy"
include "ReplicaImplClass.i.dfy"
include "ReplicaImplDelivery.i.dfy"
include "UdpRSL.i.dfy"
include "CClockReading.i.dfy"

module LiveRSL__ReplicaImplProcessPacketNoClock_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened LiveRSL__CClockReading_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__Environment_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__QRelations_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ReplicaImplLemmas_i
import opened LiveRSL__ReplicaImplClass_i
import opened LiveRSL__ReplicaImplDelivery_i
import opened LiveRSL__ReplicaModel_i
import opened LiveRSL__ReplicaModel_Part1_i
import opened LiveRSL__ReplicaModel_Part2_i
import opened LiveRSL__ReplicaModel_Part3_i
import opened LiveRSL__ReplicaModel_Part4_i
import opened LiveRSL__ReplicaModel_Part5_i
import opened LiveRSL__ReplicaState_i
import opened LiveRSL__Types_i
import opened LiveRSL__UdpRSL_i
import opened Common__UdpClient_i
import opened Environment_s
import opened Logic__Option_i
import opened Common__Util_i

lemma lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(
  cpacket:CPacket,
  sent_packets:OutboundPackets,
  old_udp_history:seq<UdpEvent>,
  post_receive_udp_history:seq<UdpEvent>,
  current_udp_history:seq<UdpEvent>,
  receive_event:UdpEvent,
  send_events:seq<UdpEvent>,
  receive_io:RslIo,
  send_ios:seq<RslIo>
  ) returns (
  udpEventLog:seq<UdpEvent>,
  ios:seq<RslIo>
  )
  requires post_receive_udp_history == old_udp_history + [receive_event]
  requires current_udp_history == post_receive_udp_history + send_events

  // From Receive:
  requires receive_event.LIoOpReceive?
  requires !cpacket.msg.CMessage_Heartbeat?
  requires CPacketIsAbstractable(cpacket)
  requires UdpEventIsAbstractable(receive_event)
  requires AbstractifyCPacketToRslPacket(cpacket) == AbstractifyUdpPacketToRslPacket(receive_event.r)
  requires receive_io == AbstractifyUdpEventToRslIo(receive_event)
    
  // From DeliverOutboundPackets:
  requires AllIosAreSends(send_ios)
  requires OutboundPacketsIsAbstractable(sent_packets)
  requires AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(send_ios)
  requires RawIoConsistentWithSpecIO(send_events, send_ios)
  requires OnlySentMarshallableData(send_events)
        
  ensures  RawIoConsistentWithSpecIO(udpEventLog, ios)
  ensures  |ios| >= 1
  ensures  ios[0] == receive_io
  ensures  AllIosAreSends(ios[1..])
  ensures  current_udp_history == old_udp_history + udpEventLog
  ensures  AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios)
  ensures  OnlySentMarshallableData(udpEventLog)
{
  var ios_head := [receive_io];
  ios := ios_head + send_ios;
  udpEventLog := [receive_event] + send_events;
        
  calc {
    AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets);
    ExtractSentPacketsFromIos(send_ios);
      { lemma_ExtractSentPacketsFromIosDoesNotMindSomeClutter(ios_head, send_ios); }
    ExtractSentPacketsFromIos(ios_head + send_ios);
    ExtractSentPacketsFromIos(ios);
  }

  forall io | io in ios[1..] ensures io.LIoOpSend?
  {
    var idx :| 0<=idx<|ios[1..]| && io==ios[1..][idx];  // because spec uses 'in seq' instead of indexing
    assert io == send_ios[idx];
    assert AllIosAreSends(send_ios);
    assert io.LIoOpSend?;
  }

  assert UdpEventLogIsAbstractable(udpEventLog);
  assert AbstractifyRawLogToIos(udpEventLog) == ios;
    
  lemma_ExtractSentPacketsFromIosDoesNotMindSomeClutter(ios_head, send_ios);
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} ReplicaNextProcessPacketInvalid(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_udp_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ghost udpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_udp_history + [receive_event] == r.Env().udp.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_Invalid?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  ensures  LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
  ensures  Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
  ensures  RawIoConsistentWithSpecIO(udpEventLog, ios)
  ensures  old_udp_history + udpEventLog == r.Env().udp.history()
  ensures  OnlySentMarshallableData(udpEventLog)
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := r.replica;
  ghost var rreplica := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_Invalid\n");

  var sent_packets := OutboundPacket(None());
  assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == [];

  assert Q_LReplica_Next_Process_Invalid(rreplica, r.AbstractifyToLReplica(), lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));

  ghost var send_events := [];
  ghost var send_ios := [];

  udpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_udp_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(rreplica, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcessRequestPostconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_Request_Preconditions(replica, inp)
  requires Replica_Next_Process_Request_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_Request(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                           AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Process_Request();
}
    
method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacketRequest(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_udp_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost udpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_udp_history + [receive_event] == r.Env().udp.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_Request?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_Request_Preconditions(r.replica, cpacket)
  modifies r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures r.Repr==old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && OnlySentMarshallableData(udpEventLog)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && r.Env() == old(r.Env())
            && old_udp_history + udpEventLog == r.Env().udp.history()
{
  if ShouldPrintProgress() {
    print("Received request from client ");
    print(cpacket.src.addr);
    print(":");
    print(cpacket.src.port);
    print(" with sequence number ");
    print(cpacket.msg.seqno);
    print("\n");
  }
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := r.replica;
  ghost var rreplica := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_Request\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var udp_client_old := r.udpClient;
  ghost var udp_addr_old := r.udpClient.LocalEndPoint();
  assert UdpClientIsValid(udp_client_old);

  var sent_packets;
  r.replica, sent_packets := Replica_Next_Process_Request(r.replica, cpacket, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable);

  // Mention unchanged predicates over mutable state in the new heap.
  assert udp_client_old == r.udpClient;
  assert UdpClientIsValid(r.udpClient);
  assert udp_addr_old == r.udpClient.LocalEndPoint();

  lemma_RevealQFromReplicaNextProcessRequestPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  udpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_udp_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(rreplica, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcess1aPostconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_1a_Preconditions(replica, inp)
  requires Replica_Next_Process_1a_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_1a(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                      AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Process_1a();
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacket1a(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_udp_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost udpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_udp_history + [receive_event] == r.Env().udp.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_1a?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_1a_Preconditions(r.replica, cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && OnlySentMarshallableData(udpEventLog)
            && r.Env() == old(r.Env())
            && old_udp_history + udpEventLog == r.Env().udp.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := r.replica;
  ghost var rreplica := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_1a\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var udp_client_old := r.udpClient;
  ghost var udp_addr_old := r.udpClient.LocalEndPoint();
  assert UdpClientIsValid(udp_client_old);

  var sent_packets;
  r.replica, sent_packets := Replica_Next_Process_1a(r.replica, cpacket);

  // Mention unchanged predicates over mutable state in the new heap.
  assert udp_client_old == r.udpClient;
  assert UdpClientIsValid(r.udpClient);
  assert udp_addr_old == r.udpClient.LocalEndPoint();

  lemma_RevealQFromReplicaNextProcess1aPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  udpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_udp_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(rreplica, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcess1bPostconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_1b_Preconditions(replica, inp)
  requires Replica_Next_Process_1b_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_1b(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                      AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Process_1b();
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacket1b(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_udp_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost udpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_udp_history + [receive_event] == r.Env().udp.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_1b?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_1b_Preconditions(r.replica,cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && OnlySentMarshallableData(udpEventLog)
            && r.Env() == old(r.Env())
            && old_udp_history + udpEventLog == r.Env().udp.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := r.replica;
  ghost var rreplica := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_1b\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var udp_client_old := r.udpClient;
  ghost var udp_addr_old := r.udpClient.LocalEndPoint();
  assert UdpClientIsValid(udp_client_old);

  var sent_packets;
  r.replica, sent_packets := Replica_Next_Process_1b(r.replica, cpacket);

  // Mention unchanged predicates over mutable state in the new heap.
  assert udp_client_old == r.udpClient;
  assert UdpClientIsValid(r.udpClient);
  assert udp_addr_old == r.udpClient.LocalEndPoint();

  lemma_RevealQFromReplicaNextProcess1bPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  udpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_udp_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(rreplica, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcessStartingPhase2Postconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_StartingPhase2_Preconditions(replica, inp)
  requires Replica_Next_Process_StartingPhase2_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_StartingPhase2(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                                  AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
{
  reveal Q_LReplica_Next_Process_StartingPhase2();
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} {:timeLimitMultiplier 5} ReplicaNextProcessPacketStartingPhase2(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_udp_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost udpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_udp_history + [receive_event] == r.Env().udp.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_StartingPhase2?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && OnlySentMarshallableData(udpEventLog)
            && r.Env() == old(r.Env())
            && old_udp_history + udpEventLog == r.Env().udp.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := r.replica;
  ghost var rreplica := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_StartingPhase2\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var udp_client_old := r.udpClient;
  ghost var udp_addr_old := r.udpClient.LocalEndPoint();
  assert UdpClientIsValid(udp_client_old);

  var sent_packets;
  r.replica, sent_packets := Replica_Next_Process_StartingPhase2(r.replica, cpacket);

  // Mention unchanged predicates over mutable state in the new heap.
  assert udp_client_old == r.udpClient;
  assert UdpClientIsValid(r.udpClient);
  assert udp_addr_old == r.udpClient.LocalEndPoint();

  lemma_RevealQFromReplicaNextProcessStartingPhase2Postconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  udpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_udp_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(rreplica, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcess2aPostconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_2a_Preconditions(replica, inp)
  requires Replica_Next_Process_2a_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_2a(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                      AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Process_2a();
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacket2a(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_udp_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost udpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_udp_history + [receive_event] == r.Env().udp.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_2a?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_2a_Preconditions(r.replica,cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && OnlySentMarshallableData(udpEventLog)
            && r.Env() == old(r.Env())
            && old_udp_history + udpEventLog == r.Env().udp.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := r.replica;
  ghost var rreplica := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_2a\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var udp_client_old := r.udpClient;
  ghost var udp_addr_old := r.udpClient.LocalEndPoint();
  assert UdpClientIsValid(udp_client_old);

  var sent_packets;
  r.replica, sent_packets := Replica_Next_Process_2a(r.replica, cpacket);

  // Mention unchanged predicates over mutable state in the new heap.
  assert udp_client_old == r.udpClient;
  assert UdpClientIsValid(r.udpClient);
  assert udp_addr_old == r.udpClient.LocalEndPoint();

  lemma_RevealQFromReplicaNextProcess2aPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  udpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_udp_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(rreplica, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcess2bPostconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_2b_Preconditions(replica, inp)
  requires Replica_Next_Process_2b_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_2b(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                      AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Process_2b();
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacket2b(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_udp_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost udpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_udp_history + [receive_event] == r.Env().udp.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_2b?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_2b_Preconditions(r.replica,cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && OnlySentMarshallableData(udpEventLog)
            && r.Env() == old(r.Env())
            && old_udp_history + udpEventLog == r.Env().udp.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := r.replica;
  ghost var rreplica := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_2b\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var udp_client_old := r.udpClient;
  ghost var udp_addr_old := r.udpClient.LocalEndPoint();
  assert UdpClientIsValid(udp_client_old);

  var sent_packets;
  r.replica, sent_packets := Replica_Next_Process_2b(r.replica, cpacket);

  // Mention unchanged predicates over mutable state in the new heap.
  assert udp_client_old == r.udpClient;
  assert UdpClientIsValid(r.udpClient);
  assert udp_addr_old == r.udpClient.LocalEndPoint();

  lemma_RevealQFromReplicaNextProcess2bPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  udpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_udp_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(rreplica, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} ReplicaNextProcessPacketReply(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_udp_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ghost udpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_udp_history + [receive_event] == r.Env().udp.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_Reply?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  ensures  LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
  ensures  Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
  ensures  RawIoConsistentWithSpecIO(udpEventLog, ios)
  ensures  OnlySentMarshallableData(udpEventLog)
  ensures  old_udp_history + udpEventLog == r.Env().udp.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := r.replica;
  ghost var rreplica := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_Reply\n");

  var sent_packets := Broadcast(CBroadcastNop);
  lemma_YesWeHaveNoPackets();
  reveal Q_LReplica_Next_Process_Reply();
  assert Q_LReplica_Next_Process_Reply(rreplica, r.AbstractifyToLReplica(), lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));

  ghost var send_events := [];
  ghost var send_ios := [];

  calc {
    ExtractSentPacketsFromIos(send_ios);
      { reveal ExtractSentPacketsFromIos(); }
    [];
  }

  udpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_udp_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(rreplica, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcessAppStateRequestPostconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_AppStateRequest_Preconditions(replica, inp)
  requires Replica_Next_Process_AppStateRequest_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_AppStateRequest(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                                   AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
{
  reveal Q_LReplica_Next_Process_AppStateRequest();
}
    
method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacketAppStateRequest(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_udp_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost udpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_udp_history + [receive_event] == r.Env().udp.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_AppStateRequest?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  modifies r.Repr, r.reply_cache_mutable
  ensures r.Repr==old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && OnlySentMarshallableData(udpEventLog)
            && r.Env() == old(r.Env())
            && old_udp_history + udpEventLog == r.Env().udp.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := r.replica;
  ghost var rreplica := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_AppStateRequest\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var udp_client_old := r.udpClient;
  ghost var udp_addr_old := r.udpClient.LocalEndPoint();
  assert UdpClientIsValid(udp_client_old);

  var sent_packets;
  r.replica, sent_packets := Replica_Next_Process_AppStateRequest(r.replica, cpacket, r.reply_cache_mutable);

  // Mention unchanged predicates over mutable state in the new heap.
  assert udp_client_old == r.udpClient;
  assert UdpClientIsValid(r.udpClient);
  assert udp_addr_old == r.udpClient.LocalEndPoint();

  lemma_RevealQFromReplicaNextProcessAppStateRequestPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  udpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_udp_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(rreplica, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcessAppStateSupplyPostconditions(
  replica:ReplicaState,
  replica':ReplicaState,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_AppStateSupply_Preconditions(replica, inp)
  requires Replica_Next_Process_AppStateSupply_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_AppStateSupply(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaStateToLReplica(replica'),
                                                  AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
{
  reveal Q_LReplica_Next_Process_AppStateSupply();
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} {:timeLimitMultiplier 5} ReplicaNextProcessPacketAppStateSupply(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_udp_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost udpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_udp_history + [receive_event] == r.Env().udp.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_AppStateSupply?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_AppStateSupply_Preconditions(r.replica,cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && OnlySentMarshallableData(udpEventLog)
            && r.Env() == old(r.Env())
            && old_udp_history + udpEventLog == r.Env().udp.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := r.replica;
  ghost var rreplica := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_AppStateSupply\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var udp_client_old := r.udpClient;
  ghost var udp_addr_old := r.udpClient.LocalEndPoint();
  assert UdpClientIsValid(udp_client_old);

  var sent_packets, replicaChanged, newCache;
  r.replica, sent_packets, replicaChanged, newCache := Replica_Next_Process_AppStateSupply(r.replica, cpacket);
  if replicaChanged {
    r.reply_cache_mutable := newCache;
  }

  // Mention unchanged predicates over mutable state in the new heap.
  assert udp_client_old == r.udpClient;
  assert UdpClientIsValid(r.udpClient);
  assert udp_addr_old == r.udpClient.LocalEndPoint();

  lemma_RevealQFromReplicaNextProcessAppStateSupplyPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  udpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_udp_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);

  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(rreplica, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} Replica_Next_ProcessPacketWithoutReadingClock_body(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_udp_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost udpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_udp_history + [receive_event] == r.Env().udp.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires NoClockMessage(cpacket.msg)
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires cpacket.msg.CMessage_AppStateSupply? ==> Replica_Next_Process_AppStateSupply_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_2b? ==> Replica_Next_Process_2b_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_2a? ==> Replica_Next_Process_2a_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_1a? ==> Replica_Next_Process_1a_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_1b? ==> Replica_Next_Process_1b_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_Request? ==> Replica_Next_Process_Request_Preconditions(r.replica,cpacket)
  // requires Replica_Next_Process_AppStateSupply_Preconditions(r.replica,cpacket)
  modifies r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures r.Repr==old(r.Repr)
  ensures r.udpClient != null
  ensures ok == UdpClientOk(r.udpClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(udpEventLog, ios)
            && OnlySentMarshallableData(udpEventLog)
            && r.Env() == old(r.Env())
            && old_udp_history + udpEventLog == r.Env().udp.history()
{
  if (cpacket.msg.CMessage_Invalid?) {
    ok := true;
    udpEventLog, ios := ReplicaNextProcessPacketInvalid(r, cpacket, old_udp_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_Request?) {
    ok, udpEventLog, ios := ReplicaNextProcessPacketRequest(r, cpacket, old_udp_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_1a?) {
    ok, udpEventLog, ios := ReplicaNextProcessPacket1a(r, cpacket, old_udp_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_1b?) {
    ok, udpEventLog, ios := ReplicaNextProcessPacket1b(r, cpacket, old_udp_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_StartingPhase2?) {
    ok, udpEventLog, ios := ReplicaNextProcessPacketStartingPhase2(r, cpacket, old_udp_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_2a?) {
    ok, udpEventLog, ios := ReplicaNextProcessPacket2a(r, cpacket, old_udp_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_2b?) {
    ok, udpEventLog, ios := ReplicaNextProcessPacket2b(r, cpacket, old_udp_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_Reply?) {
    ok := true;
    udpEventLog, ios := ReplicaNextProcessPacketReply(r, cpacket, old_udp_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_AppStateRequest?) {
    ok, udpEventLog, ios := ReplicaNextProcessPacketAppStateRequest(r, cpacket, old_udp_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_AppStateSupply?) {
    ok, udpEventLog, ios := ReplicaNextProcessPacketAppStateSupply(r, cpacket, old_udp_history, receive_event, receive_io);
  } else {
    assert false;
  }
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

}
