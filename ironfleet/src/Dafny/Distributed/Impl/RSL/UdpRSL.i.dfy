include "../Common/UdpClient.i.dfy"
include "PacketParsing.i.dfy"
include "CPaxosConfiguration.i.dfy"
include "CClockReading.i.dfy"
include "Broadcast.i.dfy"

module LiveRSL__UdpRSL_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Common__GenericMarshalling_i
import opened Common__NodeIdentity_i
import opened Common__UdpClient_i
import opened Common__Util_i
import opened LiveRSL__CClockReading_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__Environment_i
import opened LiveRSL__PacketParsing_i
import opened Impl__LiveRSL__Broadcast_i 
import opened Logic__Option_i
import opened Environment_s

//////////////////////////////////////////////////////////////////////////////
// These functions relate UdpEvent to LiveRSL's LIoOps.
// 

predicate UdpEventIsAbstractable(evt:UdpEvent)
{
  match evt
    case LIoOpSend(s) => UdpPacketIsAbstractable(s)
    case LIoOpReceive(r) => UdpPacketIsAbstractable(r)
    case LIoOpTimeoutReceive => true
    case LIoOpReadClock(t) => true
}

function AbstractifyUdpEventToRslIo(evt:UdpEvent) : RslIo
  requires UdpEventIsAbstractable(evt)
{
  match evt
    case LIoOpSend(s) => LIoOpSend(AbstractifyUdpPacketToRslPacket(s))
    case LIoOpReceive(r) => LIoOpReceive(AbstractifyUdpPacketToRslPacket(r))
    case LIoOpTimeoutReceive => LIoOpTimeoutReceive()
    case LIoOpReadClock(t) => LIoOpReadClock(t as int)
}

predicate UdpEventLogIsAbstractable(rawlog:seq<UdpEvent>)
{
  forall i :: 0<=i<|rawlog| ==> UdpEventIsAbstractable(rawlog[i])
}

function {:opaque} AbstractifyRawLogToIos(rawlog:seq<UdpEvent>) : seq<RslIo>
  requires UdpEventLogIsAbstractable(rawlog)
  ensures |AbstractifyRawLogToIos(rawlog)| == |rawlog|
  ensures forall i {:trigger AbstractifyUdpEventToRslIo(rawlog[i])} {:trigger AbstractifyRawLogToIos(rawlog)[i]} :: 0<=i<|rawlog| ==> AbstractifyRawLogToIos(rawlog)[i] == AbstractifyUdpEventToRslIo(rawlog[i])
{
  if (rawlog==[]) then [] else [AbstractifyUdpEventToRslIo(rawlog[0])] + AbstractifyRawLogToIos(rawlog[1..])
}

lemma lemma_EstablishAbstractifyRawLogToIos(rawlog:seq<UdpEvent>, ios:seq<RslIo>)
  requires UdpEventLogIsAbstractable(rawlog)
  requires |rawlog| == |ios|
  requires forall i :: 0<=i<|rawlog| ==> ios[i] == AbstractifyUdpEventToRslIo(rawlog[i])
  ensures AbstractifyRawLogToIos(rawlog) == ios
{
  reveal AbstractifyRawLogToIos();
}

predicate RawIoConsistentWithSpecIO(rawlog:seq<UdpEvent>, ios:seq<RslIo>)
{
  && UdpEventLogIsAbstractable(rawlog)
  && AbstractifyRawLogToIos(rawlog) == ios
}

predicate OnlySentMarshallableData(rawlog:seq<UdpEvent>)
{
  forall io :: io in rawlog && io.LIoOpSend? ==> UdpPacketBound(io.s.msg) && Marshallable(PaxosDemarshallData(io.s.msg))
}

//////////////////////////////////////////////////////////////////////////////
// These methods wrap the raw UdpClient interface
//

datatype ReceiveResult = RRFail() | RRTimeout() | RRPacket(cpacket:CPacket)

method GetEndPoint(ipe:IPEndPoint) returns (ep:EndPoint)
  ensures ep == ipe.EP()
  ensures EndPointIsValidIPV4(ep)
{
  var addr := ipe.GetAddress();
  var port := ipe.GetPort();
  ep := EndPoint(addr[..], port);
}

method{:timeLimitMultiplier 2} Receive(udpClient:UdpClient, localAddr:EndPoint, config:CPaxosConfiguration, msg_grammar:G) returns (rr:ReceiveResult, ghost udpEvent:UdpEvent)
  requires UdpClientIsValid(udpClient)
  requires udpClient.LocalEndPoint() == localAddr
  //requires KnownSendersMatchConfig(config)
  requires CPaxosConfigurationIsValid(config)
  requires msg_grammar == CMessage_grammar()
  modifies UdpClientRepr(udpClient)
  ensures udpClient.env == old(udpClient.env)
  ensures udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint())
  ensures UdpClientOk(udpClient) <==> !rr.RRFail?
  ensures old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient)
  ensures !rr.RRFail? ==>
            && udpClient.IsOpen()
            && old(udpClient.env.udp.history()) + [udpEvent] == udpClient.env.udp.history()
  ensures rr.RRTimeout? ==> udpEvent.LIoOpTimeoutReceive?;
  ensures rr.RRPacket? ==>
            && udpEvent.LIoOpReceive?
            && UdpPacketIsAbstractable(udpEvent.r)
            && CPacketIsAbstractable(rr.cpacket)
            && CMessageIs64Bit(rr.cpacket.msg)
            && EndPointIsValidIPV4(rr.cpacket.src)
            && AbstractifyCPacketToRslPacket(rr.cpacket) == AbstractifyUdpPacketToRslPacket(udpEvent.r)
            && rr.cpacket.msg == PaxosDemarshallData(udpEvent.r.msg)
            && PaxosEndPointIsValid(rr.cpacket.src, config)
{
  var timeout := 0;
  ghost var old_udp_history := udpClient.env.udp.history();
  var ok, timedOut, remote, buffer := udpClient.Receive(timeout);

  if (!ok) {
    rr := RRFail();
    return;
  }

  if (timedOut) {
    rr := RRTimeout();
    udpEvent := LIoOpTimeoutReceive(); 
    return;
  }

  udpEvent := LIoOpReceive(LPacket(udpClient.LocalEndPoint(), remote.EP(), buffer[..]));
  assert udpClient.env.udp.history() == old_udp_history + [udpEvent];
  var start_time := Time.GetDebugTimeTicks();
  lemma_CMessageGrammarValid();
  var cmessage := PaxosDemarshallDataMethod(buffer, msg_grammar);
  var end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("PaxosDemarshallDataMethod", start_time, end_time);

  var srcEp := GetEndPoint(remote);
  var cpacket := CPacket(localAddr, srcEp, cmessage);
  rr := RRPacket(cpacket);
  assert udpClient.env.udp.history() == old_udp_history + [udpEvent];

  if cmessage.CMessage_Invalid? {
    RecordTimingSeq("DemarshallMessage_Invalid", start_time, end_time);
  } else if cmessage.CMessage_Request? {
    RecordTimingSeq("DemarshallMessage_Request", start_time, end_time);
  } else if cmessage.CMessage_1a? {
    RecordTimingSeq("DemarshallMessage_1a", start_time, end_time);
  } else if cmessage.CMessage_1b? {
    RecordTimingSeq("DemarshallMessage_1b", start_time, end_time);
  } else if cmessage.CMessage_2a? {
    RecordTimingSeq("DemarshallMessage_2a", start_time, end_time);
  } else if cmessage.CMessage_2b? {
    RecordTimingSeq("DemarshallMessage_2b", start_time, end_time);
  } else if cmessage.CMessage_Heartbeat? {
    RecordTimingSeq("DemarshallMessage_Heartbeat", start_time, end_time);
  } else if cmessage.CMessage_Reply? {
    RecordTimingSeq("DemarshallMessage_Reply", start_time, end_time);
  } else if cmessage.CMessage_AppStateRequest? {
    RecordTimingSeq("DemarshallMessage_AppStateRequest", start_time, end_time);
  } else if cmessage.CMessage_AppStateSupply? {
    RecordTimingSeq("DemarshallMessage_AppStateSupply", start_time, end_time);
  } else if cmessage.CMessage_StartingPhase2? {
    RecordTimingSeq("DemarshallMessage_StartingPhase2", start_time, end_time);
  }

  assert EndPointIsValidIPV4(udpClient.LocalEndPoint());
  assert PaxosEndPointIsValid(rr.cpacket.src, config);
  assert AbstractifyCPacketToRslPacket(rr.cpacket) == AbstractifyUdpPacketToRslPacket(udpEvent.r);

  /*
  forall ()
    ensures AbstractifyCPacketToRslPacket(rr.cpacket) == AbstractifyUdpPacketToRslPacket(udpEvent.r)
    ensures PaxosEndPointIsValid(rr.cpacket.src, config)
  {
//    lemma_Uint64EndPointRelationships();
//    assert ConvertEndPointToUint64(srcEp) == rr.cpacket.src;    // OBSERVE trigger
      assert EndPointIsValidIPV4(udpClient.LocalEndPoint());  // OBSERVE trigger
  }
  */
}

method ReadClock(udpClient:UdpClient) returns (clock:CClockReading, ghost clockEvent:UdpEvent)
  requires UdpClientIsValid(udpClient)
  modifies UdpClientRepr(udpClient)
  ensures old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient)
  ensures UdpClientIsValid(udpClient)
  ensures udpClient.env == old(udpClient.env)
  ensures old(udpClient.env.udp.history()) + [clockEvent] == udpClient.env.udp.history()
  ensures clockEvent.LIoOpReadClock?
  ensures clock.t as int == clockEvent.t
  ensures UdpClientIsValid(udpClient)
  ensures UdpEventIsAbstractable(clockEvent)
  ensures udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint())
  // TODO we're going to call GetTime, which returns a single value.
{
  var t := Time.GetTime(udpClient.env);
  clockEvent := LIoOpReadClock(t as int);
  clock := CClockReading(t);
}

predicate SendLogEntryReflectsPacket(event:UdpEvent, cpacket:CPacket)
{
  && event.LIoOpSend?
  && UdpPacketIsAbstractable(event.s)
  && CPacketIsAbstractable(cpacket)
  && AbstractifyCPacketToRslPacket(cpacket) == AbstractifyUdpPacketToRslPacket(event.s)
}

predicate SendLogReflectsPacket(udpEventLog:seq<UdpEvent>, packet:Option<CPacket>)
{
  match packet {
    case Some(p) => |udpEventLog| == 1 && SendLogEntryReflectsPacket(udpEventLog[0], p)
    case None => udpEventLog == []
  }
}

predicate SendLogReflectsPacketSeq(udpEventLog:seq<UdpEvent>, packets:seq<CPacket>)
{
  && |udpEventLog| == |packets| 
  && (forall i :: 0 <= i < |packets| ==> SendLogEntryReflectsPacket(udpEventLog[i], packets[i]))
}

predicate SendLogMatchesRefinement(udpEventLog:seq<UdpEvent>, broadcast:CBroadcast, index:int)
  requires CBroadcastIsAbstractable(broadcast)
  requires broadcast.CBroadcast?
  requires 0<=|udpEventLog|<=|broadcast.dsts|
  requires 0 <= index < |udpEventLog|
{
  && udpEventLog[index].LIoOpSend? && UdpPacketIsAbstractable(udpEventLog[index].s)
  && AbstractifyCBroadcastToRlsPacketSeq(broadcast)[index] == AbstractifyUdpPacketToRslPacket(udpEventLog[index].s)
}

predicate SendLogReflectsBroadcastPrefix(udpEventLog:seq<UdpEvent>, broadcast:CBroadcast)
  requires CBroadcastIsAbstractable(broadcast)
  requires broadcast.CBroadcast?
{
  && 0<=|udpEventLog|<=|broadcast.dsts|
  && forall i :: 0<=i<|udpEventLog| ==> SendLogMatchesRefinement(udpEventLog, broadcast, i)
}

predicate SendLogReflectsBroadcast(udpEventLog:seq<UdpEvent>, broadcast:CBroadcast)
  requires CBroadcastIsAbstractable(broadcast)
{
  if broadcast.CBroadcastNop? then
    udpEventLog == []
  else 
    && SendLogReflectsBroadcastPrefix(udpEventLog, broadcast)
    && |udpEventLog| == |broadcast.dsts|
}

lemma lemma_UdpEventLogAppend(broadcast:CBroadcast, udpEventLog:seq<UdpEvent>, udpEvent:UdpEvent)
  requires broadcast.CBroadcast?
  requires CBroadcastIsValid(broadcast)
  requires SendLogReflectsBroadcastPrefix(udpEventLog, broadcast)
  requires |udpEventLog| < |broadcast.dsts|
  requires udpEvent.LIoOpSend?
  requires UdpPacketIsAbstractable(udpEvent.s)
  requires CMessageIsAbstractable(PaxosDemarshallData(udpEvent.s.msg))
  requires udpEvent.s.dst == broadcast.dsts[|udpEventLog|]
  requires udpEvent.s.src == broadcast.src
  requires BufferRefinementAgreesWithMessageRefinement(broadcast.msg, udpEvent.s.msg)
  ensures SendLogReflectsBroadcastPrefix(udpEventLog + [udpEvent], broadcast)
{
  var i := |udpEventLog|;

  calc {
    AbstractifyCBroadcastToRlsPacketSeq(broadcast)[i];
    BuildLBroadcast(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                    AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                    AbstractifyCMessageToRslMessage(broadcast.msg))[i];
    LPacket(AbstractifyEndPointsToNodeIdentities(broadcast.dsts)[i], 
            AbstractifyEndPointToNodeIdentity(broadcast.src), 
            AbstractifyCMessageToRslMessage(broadcast.msg));
    LPacket(AbstractifyEndPointToNodeIdentity(udpEvent.s.dst),
            AbstractifyEndPointToNodeIdentity(udpEvent.s.src),
            AbstractifyCMessageToRslMessage(PaxosDemarshallData(udpEvent.s.msg)));
    AbstractifyUdpPacketToRslPacket(udpEvent.s);
  }

  var new_log := udpEventLog + [udpEvent];

  forall i' | 0 <= i' < |new_log|
    ensures SendLogMatchesRefinement(new_log, broadcast, i')
  {
    if i' < |udpEventLog| {
      assert new_log[i'] == udpEventLog[i'];
      assert SendLogMatchesRefinement(udpEventLog, broadcast, i');
      assert SendLogMatchesRefinement(new_log, broadcast, i');
    } else {
      assert new_log[i'] == udpEvent;
      assert SendLogMatchesRefinement(new_log, broadcast, i');
    }
  }

  calc ==> {
    true;
    forall i' :: 0 <= i' < |new_log| ==> SendLogMatchesRefinement(new_log, broadcast, i');
    SendLogReflectsBroadcastPrefix(new_log, broadcast);
    SendLogReflectsBroadcastPrefix(udpEventLog + [udpEvent], broadcast);
  }
}

method SendBroadcast(udpClient:UdpClient, broadcast:CBroadcast, ghost localAddr_:EndPoint) returns (ok:bool, ghost udpEventLog:seq<UdpEvent>)
  requires UdpClientIsValid(udpClient)
  requires CBroadcastIsValid(broadcast)
  requires udpClient.LocalEndPoint() == localAddr_
  requires broadcast.CBroadcast? ==> broadcast.src == localAddr_
  modifies UdpClientRepr(udpClient)
  ensures old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient)
  ensures udpClient.env == old(udpClient.env)
  ensures udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint())
  ensures UdpClientOk(udpClient) <==> ok
  ensures ok ==>
            && UdpClientIsValid(udpClient)
            && udpClient.IsOpen()
            && old(udpClient.env.udp.history()) + udpEventLog == udpClient.env.udp.history()
            && OnlySentMarshallableData(udpEventLog)
            && SendLogReflectsBroadcast(udpEventLog, broadcast)
{
  ok := true;
  udpEventLog := [];

  if broadcast.CBroadcastNop? {
    // No work to do!
  } else {
    // Do the marshalling work once
    assert CMessageIsAbstractable(broadcast.msg);
    assert Marshallable(broadcast.msg);
    //var marshall_start_time := Time.GetDebugTimeTicks();
    var buffer := PaxosMarshall(broadcast.msg);
    //var marshall_end_time := Time.GetDebugTimeTicks();
    //RecordTimingSeq("SendBroadcast_PaxosMarshall", marshall_start_time, marshall_end_time);
    assert UdpPacketBound(buffer[..]);

    calc ==> {
      true;
      CBroadcastIsValid(broadcast);
      CBroadcastIsAbstractable(broadcast);
      CMessageIsAbstractable(broadcast.msg);
    }

    var i:uint64 := 0;
    while i < |broadcast.dsts| as uint64
      invariant 0 <= i as int <= |broadcast.dsts|
      invariant |udpEventLog| == i as int
      invariant UdpClientRepr(udpClient) == old(UdpClientRepr(udpClient))
      invariant udpClient.env == old(udpClient.env)
      invariant udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint())
      invariant UdpClientIsValid(udpClient)
      invariant UdpClientOk(udpClient)
      invariant old(udpClient.env.udp.history()) + udpEventLog == udpClient.env.udp.history()
      invariant UdpPacketBound(buffer[..])
      invariant Marshallable(PaxosDemarshallData(buffer[..]))
      invariant BufferRefinementAgreesWithMessageRefinement(broadcast.msg, buffer[..])
      invariant SendLogReflectsBroadcastPrefix(udpEventLog, broadcast)
      invariant CMessageIsAbstractable(PaxosDemarshallData(buffer[..]))
      invariant OnlySentMarshallableData(udpEventLog)
    {
      ghost var udpEventLog_old := udpEventLog;

      // Construct the remote address -- TODO: Only do this once per replica!
      var dstEp:EndPoint := broadcast.dsts[i];
      //var construct_start_time := Time.GetDebugTimeTicks();
      var dstAddrAry := seqToArrayOpt(dstEp.addr);
      var remote;
      ok, remote := IPEndPoint.Construct(dstAddrAry, dstEp.port, udpClient.env);
      if (!ok) { return; }
      //var construct_end_time := Time.GetDebugTimeTicks();
      //RecordTimingSeq("SendBroadcast_IPEndPointConstruct", construct_start_time, construct_end_time);

      //var send_start_time := Time.GetDebugTimeTicks();
      ok := udpClient.Send(remote, buffer);
      if (!ok) { return; }
      //var send_end_time := Time.GetDebugTimeTicks();
      //RecordTimingSeq("SendBroadcast_Send", send_start_time, send_end_time);

      ghost var udpEvent := LIoOpSend(LPacket(remote.EP(), udpClient.LocalEndPoint(), buffer[..]));
      udpEventLog := udpEventLog + [udpEvent];

      lemma_UdpEventLogAppend(broadcast, udpEventLog_old, udpEvent);

      i := i + 1;
    }
  }
}


method SendPacket(udpClient:UdpClient, packets:OutboundPackets, ghost localAddr_:EndPoint) returns (ok:bool, ghost udpEventLog:seq<UdpEvent>)
  requires UdpClientIsValid(udpClient)
  requires packets.OutboundPacket?
  requires OutboundPacketsIsValid(packets)
  requires udpClient.LocalEndPoint() == localAddr_
  requires OutboundPacketsHasCorrectSrc(packets, localAddr_)
  modifies UdpClientRepr(udpClient)
  ensures old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient)
  ensures udpClient.env == old(udpClient.env)
  ensures udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint())
  ensures UdpClientOk(udpClient) <==> ok
  ensures ok ==> && UdpClientIsValid(udpClient)
                 && udpClient.IsOpen()
                 && old(udpClient.env.udp.history()) + udpEventLog == udpClient.env.udp.history()
                 && OnlySentMarshallableData(udpEventLog)
                 && SendLogReflectsPacket(udpEventLog, packets.p)
{
  var j:uint64 := 0;
  udpEventLog := [];
  ok := true;
  var opt_packet := packets.p;

  if opt_packet.None? {

  } else {
    var cpacket := opt_packet.v;

    ghost var udpEventLog_old := udpEventLog;

    // Construct the remote address
    var dstEp:EndPoint := cpacket.dst;
    var dstAddrAry := seqToArrayOpt(dstEp.addr);
    var remote;
    ok, remote := IPEndPoint.Construct(dstAddrAry, dstEp.port, udpClient.env);
    if (!ok) { return; }

    assert CMessageIsAbstractable(cpacket.msg);
    assert Marshallable(cpacket.msg);
    var marshall_start_time := Time.GetDebugTimeTicks();
    var buffer := PaxosMarshall(cpacket.msg);
    var marshall_end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("SendBatch_PaxosMarshall", marshall_start_time, marshall_end_time);

    ghost var data := buffer[..];
    assert BufferRefinementAgreesWithMessageRefinement(cpacket.msg, data);

    ok := udpClient.Send(remote, buffer);
    if (!ok) { return; }

    ghost var udpEvent := LIoOpSend(LPacket(remote.EP(), udpClient.LocalEndPoint(), buffer[..]));
    ghost var udp := udpEvent.s;

    calc {
      AbstractifyCPacketToRslPacket(cpacket);
      LPacket(AbstractifyEndPointToNodeIdentity(cpacket.dst), AbstractifyEndPointToNodeIdentity(cpacket.src), AbstractifyCMessageToRslMessage(cpacket.msg));
      LPacket(AbstractifyEndPointToNodeIdentity(udp.dst), AbstractifyEndPointToNodeIdentity(udp.src), AbstractifyCMessageToRslMessage(cpacket.msg));
      AbstractifyBufferToRslPacket(udp.src, udp.dst, data);
      AbstractifyBufferToRslPacket(udp.src, udp.dst, udp.msg);
      AbstractifyUdpPacketToRslPacket(udpEvent.s);
    }
    assert SendLogEntryReflectsPacket(udpEvent, cpacket);
    udpEventLog := [udpEvent];
  }
}


method{:timeLimitMultiplier 2} SendPacketSequence(udpClient:UdpClient, packets:OutboundPackets, ghost localAddr_:EndPoint) returns (ok:bool, ghost udpEventLog:seq<UdpEvent>)
  requires UdpClientIsValid(udpClient)
  requires OutboundPacketsIsValid(packets)
  requires packets.PacketSequence?
  requires udpClient.LocalEndPoint() == localAddr_
  requires OutboundPacketsHasCorrectSrc(packets, localAddr_)
  modifies UdpClientRepr(udpClient)
  ensures old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient)
  ensures udpClient.env == old(udpClient.env)
  ensures udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint())
  ensures UdpClientOk(udpClient) <==> ok
  ensures ok ==>
            && UdpClientIsValid(udpClient)
            && udpClient.IsOpen()
            && old(udpClient.env.udp.history()) + udpEventLog == udpClient.env.udp.history()
            && OnlySentMarshallableData(udpEventLog)
            && SendLogReflectsPacketSeq(udpEventLog, packets.s)
{
  var cpackets := packets.s;
  var j:uint64 := 0;
  udpEventLog := [];
  ok := true;
    
  ghost var udpEventLog_old := udpEventLog;
  ghost var udpClientEnvHistory_old := old(udpClient.env.udp.history());
  var i:uint64 := 0;

  while i < |cpackets| as uint64
    invariant old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient)
    invariant udpClient.env == old(udpClient.env)
    invariant udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint())
    invariant UdpClientOk(udpClient) <==> ok
    invariant ok ==> ( UdpClientIsValid(udpClient) && udpClient.IsOpen())
    invariant ok ==> udpClientEnvHistory_old + udpEventLog == udpClient.env.udp.history()
    invariant (i == 0) ==> |udpEventLog| == 0
    invariant (0 < i as int < |cpackets|) ==> |udpEventLog| == |cpackets[0..i]|
    invariant (0 < i as int < |cpackets|) ==> SendLogReflectsPacketSeq(udpEventLog, cpackets[0..i]);
    invariant (i as int >= |cpackets|) ==> SendLogReflectsPacketSeq(udpEventLog, cpackets);
    invariant OnlySentMarshallableData(udpEventLog)
  {
    var cpacket := cpackets[i];
    // Construct the remote address
    var dstEp:EndPoint := cpacket.dst;
    assert cpacket in cpackets;
    assert OutboundPacketsIsValid(packets);

    var dstAddrAry := seqToArrayOpt(dstEp.addr);
    var remote;
    ok, remote := IPEndPoint.Construct(dstAddrAry, dstEp.port, udpClient.env);
    if (!ok) { return; }

    assert CMessageIsAbstractable(cpacket.msg);
         
    assert Marshallable(cpacket.msg);
    var buffer := PaxosMarshall(cpacket.msg);

    ghost var data := buffer[..];
    assert BufferRefinementAgreesWithMessageRefinement(cpacket.msg, data);

    ok := udpClient.Send(remote, buffer);
    if (!ok) { return; }

    ghost var udpEvent := LIoOpSend(LPacket(remote.EP(), udpClient.LocalEndPoint(), buffer[..]));
    ghost var udp := udpEvent.s;

    calc {
      AbstractifyCPacketToRslPacket(cpacket);
      LPacket(AbstractifyEndPointToNodeIdentity(cpacket.dst), AbstractifyEndPointToNodeIdentity(cpacket.src), AbstractifyCMessageToRslMessage(cpacket.msg));
      LPacket(AbstractifyEndPointToNodeIdentity(udp.dst), AbstractifyEndPointToNodeIdentity(udp.src), AbstractifyCMessageToRslMessage(cpacket.msg));
      AbstractifyBufferToRslPacket(udp.src, udp.dst, data);
      AbstractifyBufferToRslPacket(udp.src, udp.dst, udp.msg);
      AbstractifyUdpPacketToRslPacket(udpEvent.s);
    }
        
    assert SendLogEntryReflectsPacket(udpEvent, cpacket);
        
    udpEventLog := udpEventLog + [udpEvent];
    assert cpackets[0..(i as int+1)] == cpackets[0..i as int] + [cpacket];
    assert SendLogReflectsPacketSeq(udpEventLog, cpackets[0..(i as int+1)]);
    i := i + 1;
  }
}

} 
