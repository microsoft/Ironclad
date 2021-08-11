include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/RSL/Replica.i.dfy"
include "ReplicaModel.i.dfy"
include "ReplicaImplLemmas.i.dfy"
include "ReplicaImplClass.i.dfy"
include "ReplicaImplDelivery.i.dfy"
include "NetRSL.i.dfy"
include "CClockReading.i.dfy"

module LiveRSL__ReplicaImplProcessPacketNoClock_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened LiveRSL__AppInterface_i
import opened LiveRSL__CClockReading_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__Environment_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__QRelations_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ReplicaConstantsState_i
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
import opened LiveRSL__NetRSL_i
import opened Common__NetClient_i
import opened Environment_s
import opened Logic__Option_i
import opened Common__Util_i

lemma lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(
  cpacket:CPacket,
  sent_packets:OutboundPackets,
  old_net_history:seq<NetEvent>,
  post_receive_net_history:seq<NetEvent>,
  current_net_history:seq<NetEvent>,
  receive_event:NetEvent,
  send_events:seq<NetEvent>,
  receive_io:RslIo,
  send_ios:seq<RslIo>
  ) returns (
  netEventLog:seq<NetEvent>,
  ios:seq<RslIo>
  )
  requires post_receive_net_history == old_net_history + [receive_event]
  requires current_net_history == post_receive_net_history + send_events

  // From Receive:
  requires receive_event.LIoOpReceive?
  requires !cpacket.msg.CMessage_Heartbeat?
  requires CPacketIsAbstractable(cpacket)
  requires NetEventIsAbstractable(receive_event)
  requires AbstractifyCPacketToRslPacket(cpacket) == AbstractifyNetPacketToRslPacket(receive_event.r)
  requires receive_io == AbstractifyNetEventToRslIo(receive_event)
    
  // From DeliverOutboundPackets:
  requires AllIosAreSends(send_ios)
  requires OutboundPacketsIsAbstractable(sent_packets)
  requires AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(send_ios)
  requires RawIoConsistentWithSpecIO(send_events, send_ios)
  requires OnlySentMarshallableData(send_events)
        
  ensures  RawIoConsistentWithSpecIO(netEventLog, ios)
  ensures  |ios| >= 1
  ensures  ios[0] == receive_io
  ensures  AllIosAreSends(ios[1..])
  ensures  current_net_history == old_net_history + netEventLog
  ensures  AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios)
  ensures  OnlySentMarshallableData(netEventLog)
{
  var ios_head := [receive_io];
  ios := ios_head + send_ios;
  netEventLog := [receive_event] + send_events;
        
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

  assert NetEventLogIsAbstractable(netEventLog);
  assert AbstractifyRawLogToIos(netEventLog) == ios;
    
  lemma_ExtractSentPacketsFromIosDoesNotMindSomeClutter(ios_head, send_ios);
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} ReplicaNextProcessPacketInvalid(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<NetEvent>,
  ghost receive_event:NetEvent,
  ghost receive_io:RslIo
  ) returns (
  ghost netEventLog:seq<NetEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().net.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_Invalid?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  ensures  LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
  ensures  Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
  ensures  RawIoConsistentWithSpecIO(netEventLog, ios)
  ensures  old_net_history + netEventLog == r.Env().net.history()
  ensures  OnlySentMarshallableData(netEventLog)
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var rreplica := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_Invalid\n");

  var sent_packets := OutboundPacket(None());
  assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == [];

  assert Q_LReplica_Next_Process_Invalid(rreplica, r.AbstractifyToLReplica(), lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));

  ghost var send_events := [];
  ghost var send_ios := [];

  netEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().net.history()),
                                                                              r.Env().net.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(rreplica, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcessRequestPostconditions(
  replica:LReplica,
  replica':ReplicaState,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_Request_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_Request(replica, AbstractifyReplicaStateToLReplica(replica'),
                                           AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Process_Request();
}
    
method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacketRequest(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<NetEvent>,
  ghost receive_event:NetEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost netEventLog:seq<NetEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().net.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_Request?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_Request_Preconditions(r.replica, cpacket)
  modifies r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == NetClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && OnlySentMarshallableData(netEventLog)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && r.Env() == old(r.Env())
            && old_net_history + netEventLog == r.Env().net.history()
{
  if PrintParams.ShouldPrintProgress() {
    print("Received request from client ");
    print(cpacket.src);
    print(" with sequence number ");
    print(cpacket.msg.seqno);
    print("\n");
  }
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_Request\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.MyPublicKey();
  assert NetClientIsValid(net_client_old);

  var sent_packets;
  r.replica, sent_packets := Replica_Next_Process_Request(r.replica, cpacket, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable);

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert NetClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.MyPublicKey();

  lemma_RevealQFromReplicaNextProcessRequestPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  netEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().net.history()),
                                                                              r.Env().net.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcess1aPostconditions(
  replica:LReplica,
  replica':ReplicaState,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_1a_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_1a(replica, AbstractifyReplicaStateToLReplica(replica'),
                                      AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Process_1a();
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacket1a(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<NetEvent>,
  ghost receive_event:NetEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost netEventLog:seq<NetEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().net.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_1a?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_1a_Preconditions(r.replica, cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == NetClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && r.Env() == old(r.Env())
            && old_net_history + netEventLog == r.Env().net.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_1a\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.MyPublicKey();
  assert NetClientIsValid(net_client_old);

  var sent_packets;
  r.replica, sent_packets := Replica_Next_Process_1a(r.replica, cpacket);

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert NetClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.MyPublicKey();

  lemma_RevealQFromReplicaNextProcess1aPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  netEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().net.history()),
                                                                              r.Env().net.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcess1bPostconditions(
  replica:LReplica,
  replica':ReplicaState,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_1b_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_1b(replica, AbstractifyReplicaStateToLReplica(replica'),
                                      AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Process_1b();
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacket1b(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<NetEvent>,
  ghost receive_event:NetEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost netEventLog:seq<NetEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().net.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_1b?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_1b_Preconditions(r.replica,cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == NetClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && r.Env() == old(r.Env())
            && old_net_history + netEventLog == r.Env().net.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_1b\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.MyPublicKey();
  assert NetClientIsValid(net_client_old);

  var sent_packets;
  r.replica, sent_packets := Replica_Next_Process_1b(r.replica, cpacket);

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert NetClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.MyPublicKey();

  lemma_RevealQFromReplicaNextProcess1bPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  netEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().net.history()),
                                                                              r.Env().net.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcessStartingPhase2Postconditions(
  replica:LReplica,
  replica':ReplicaState,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_StartingPhase2_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_StartingPhase2(replica, AbstractifyReplicaStateToLReplica(replica'),
                                                  AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
{
  reveal Q_LReplica_Next_Process_StartingPhase2();
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} {:timeLimitMultiplier 5} ReplicaNextProcessPacketStartingPhase2(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<NetEvent>,
  ghost receive_event:NetEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost netEventLog:seq<NetEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().net.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_StartingPhase2?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == NetClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && r.Env() == old(r.Env())
            && old_net_history + netEventLog == r.Env().net.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_StartingPhase2\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.MyPublicKey();
  assert NetClientIsValid(net_client_old);

  var sent_packets;
  r.replica, sent_packets := Replica_Next_Process_StartingPhase2(r.replica, cpacket);

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert NetClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.MyPublicKey();

  lemma_RevealQFromReplicaNextProcessStartingPhase2Postconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  netEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().net.history()),
                                                                              r.Env().net.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcess2aPostconditions(
  replica:LReplica,
  replica':ReplicaState,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_2a_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_2a(replica, AbstractifyReplicaStateToLReplica(replica'),
                                      AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Process_2a();
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacket2a(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<NetEvent>,
  ghost receive_event:NetEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost netEventLog:seq<NetEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().net.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_2a?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_2a_Preconditions(r.replica,cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == NetClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && r.Env() == old(r.Env())
            && old_net_history + netEventLog == r.Env().net.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_2a\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.MyPublicKey();
  assert NetClientIsValid(net_client_old);

  var sent_packets;
  r.replica, sent_packets := Replica_Next_Process_2a(r.replica, cpacket);

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert NetClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.MyPublicKey();

  lemma_RevealQFromReplicaNextProcess2aPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  netEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().net.history()),
                                                                              r.Env().net.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcess2bPostconditions(
  replica:LReplica,
  replica':ReplicaState,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_2b_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_2b(replica, AbstractifyReplicaStateToLReplica(replica'),
                                      AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Process_2b();
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacket2b(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<NetEvent>,
  ghost receive_event:NetEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost netEventLog:seq<NetEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().net.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_2b?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_2b_Preconditions(r.replica,cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == NetClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && r.Env() == old(r.Env())
            && old_net_history + netEventLog == r.Env().net.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_2b\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.MyPublicKey();
  assert NetClientIsValid(net_client_old);

  var sent_packets;
  r.replica, sent_packets := Replica_Next_Process_2b(r.replica, cpacket);

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert NetClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.MyPublicKey();

  lemma_RevealQFromReplicaNextProcess2bPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  netEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().net.history()),
                                                                              r.Env().net.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} ReplicaNextProcessPacketReply(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<NetEvent>,
  ghost receive_event:NetEvent,
  ghost receive_io:RslIo
  ) returns (
  ghost netEventLog:seq<NetEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().net.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_Reply?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  ensures  LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
  ensures  Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
  ensures  RawIoConsistentWithSpecIO(netEventLog, ios)
  ensures  OnlySentMarshallableData(netEventLog)
  ensures  old_net_history + netEventLog == r.Env().net.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_Reply\n");

  var sent_packets := Broadcast(CBroadcastNop);
  lemma_YesWeHaveNoPackets();
  reveal Q_LReplica_Next_Process_Reply();
  assert Q_LReplica_Next_Process_Reply(replica_old, r.AbstractifyToLReplica(), lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));

  ghost var send_events := [];
  ghost var send_ios := [];

  calc {
    ExtractSentPacketsFromIos(send_ios);
      { reveal ExtractSentPacketsFromIos(); }
    [];
  }

  netEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().net.history()),
                                                                              r.Env().net.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcessAppStateRequestPostconditions(
  replica:LReplica,
  replica':ReplicaState,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_AppStateRequest_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_AppStateRequest(replica, AbstractifyReplicaStateToLReplica(replica'),
                                                   AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
{
  reveal Q_LReplica_Next_Process_AppStateRequest();
}
    
method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacketAppStateRequest(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<NetEvent>,
  ghost receive_event:NetEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost netEventLog:seq<NetEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().net.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_AppStateRequest?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  modifies r.Repr, r.reply_cache_mutable
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == NetClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && r.Env() == old(r.Env())
            && old_net_history + netEventLog == r.Env().net.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_AppStateRequest\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.MyPublicKey();
  assert NetClientIsValid(net_client_old);

  var sent_packets;
  r.replica, sent_packets := Replica_Next_Process_AppStateRequest(r.replica, cpacket, r.reply_cache_mutable);

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert NetClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.MyPublicKey();

  lemma_RevealQFromReplicaNextProcessAppStateRequestPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  netEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().net.history()),
                                                                              r.Env().net.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcessAppStateSupplyPostconditions(
  replica:LReplica,
  replica':ReplicaState,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_AppStateSupply_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_AppStateSupply(replica, AbstractifyReplicaStateToLReplica(replica'),
                                                  AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
{
  reveal Q_LReplica_Next_Process_AppStateSupply();
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} {:timeLimitMultiplier 5} ReplicaNextProcessPacketAppStateSupply(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<NetEvent>,
  ghost receive_event:NetEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost netEventLog:seq<NetEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().net.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_AppStateSupply?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_AppStateSupply_Preconditions(r.replica,cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == NetClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && r.Env() == old(r.Env())
            && old_net_history + netEventLog == r.Env().net.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyReplicaStateToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_AppStateSupply\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.MyPublicKey();
  assert NetClientIsValid(net_client_old);

  var sent_packets, replicaChanged;
  r.replica, sent_packets, replicaChanged := Replica_Next_Process_AppStateSupply(r.replica, cpacket);

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert NetClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.MyPublicKey();

  lemma_RevealQFromReplicaNextProcessAppStateSupplyPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  netEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().net.history()),
                                                                              r.Env().net.history(),
                                                                              receive_event, send_events, receive_io, send_ios);

  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyReplicaStateToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

method {:fuel AbstractifyReplicaStateToLReplica,0,0} {:fuel ReplicaStateIsValid,0,0} Replica_Next_ProcessPacketWithoutReadingClock_body(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<NetEvent>,
  ghost receive_event:NetEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost netEventLog:seq<NetEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().net.history()
  requires CPaxosConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires NoClockMessage(cpacket.msg)
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires cpacket.msg.CMessage_AppStateRequest? ==> Replica_Next_Process_AppStateRequest_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_AppStateSupply? ==> Replica_Next_Process_AppStateSupply_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_2b? ==> Replica_Next_Process_2b_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_2a? ==> Replica_Next_Process_2a_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_1a? ==> Replica_Next_Process_1a_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_1b? ==> Replica_Next_Process_1b_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_Request? ==> Replica_Next_Process_Request_Preconditions(r.replica,cpacket)
  // requires Replica_Next_Process_AppStateSupply_Preconditions(r.replica,cpacket)
  modifies r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == NetClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && r.Env() == old(r.Env())
            && old_net_history + netEventLog == r.Env().net.history()
{
  if (cpacket.msg.CMessage_Invalid?) {
    ok := true;
    netEventLog, ios := ReplicaNextProcessPacketInvalid(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_Request?) {
    ok, netEventLog, ios := ReplicaNextProcessPacketRequest(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_1a?) {
    ok, netEventLog, ios := ReplicaNextProcessPacket1a(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_1b?) {
    ok, netEventLog, ios := ReplicaNextProcessPacket1b(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_StartingPhase2?) {
    ok, netEventLog, ios := ReplicaNextProcessPacketStartingPhase2(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_2a?) {
    ok, netEventLog, ios := ReplicaNextProcessPacket2a(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_2b?) {
    ok, netEventLog, ios := ReplicaNextProcessPacket2b(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_Reply?) {
    ok := true;
    netEventLog, ios := ReplicaNextProcessPacketReply(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_AppStateRequest?) {
    ok, netEventLog, ios := ReplicaNextProcessPacketAppStateRequest(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_AppStateSupply?) {
    ok, netEventLog, ios := ReplicaNextProcessPacketAppStateSupply(r, cpacket, old_net_history, receive_event, receive_io);
  } else {
    assert false;
  }
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

}
