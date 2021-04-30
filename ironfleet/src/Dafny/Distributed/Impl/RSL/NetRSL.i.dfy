include "../Common/NetClient.i.dfy"
include "PacketParsing.i.dfy"
include "CPaxosConfiguration.i.dfy"
include "CClockReading.i.dfy"
include "Broadcast.i.dfy"

module LiveRSL__NetRSL_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Common__GenericMarshalling_i
import opened Common__NodeIdentity_i
import opened Common__NetClient_i
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
// These functions relate NetEvent to LiveRSL's LIoOps.
// 

predicate NetEventIsAbstractable(evt:NetEvent)
{
  match evt
    case LIoOpSend(s) => NetPacketIsAbstractable(s)
    case LIoOpReceive(r) => NetPacketIsAbstractable(r)
    case LIoOpTimeoutReceive => true
    case LIoOpReadClock(t) => true
}

function AbstractifyNetEventToRslIo(evt:NetEvent) : RslIo
  requires NetEventIsAbstractable(evt)
{
  match evt
    case LIoOpSend(s) => LIoOpSend(AbstractifyNetPacketToRslPacket(s))
    case LIoOpReceive(r) => LIoOpReceive(AbstractifyNetPacketToRslPacket(r))
    case LIoOpTimeoutReceive => LIoOpTimeoutReceive()
    case LIoOpReadClock(t) => LIoOpReadClock(t as int)
}

predicate NetEventLogIsAbstractable(rawlog:seq<NetEvent>)
{
  forall i :: 0<=i<|rawlog| ==> NetEventIsAbstractable(rawlog[i])
}

function {:opaque} AbstractifyRawLogToIos(rawlog:seq<NetEvent>) : seq<RslIo>
  requires NetEventLogIsAbstractable(rawlog)
  ensures |AbstractifyRawLogToIos(rawlog)| == |rawlog|
  ensures forall i {:trigger AbstractifyNetEventToRslIo(rawlog[i])} {:trigger AbstractifyRawLogToIos(rawlog)[i]} :: 0<=i<|rawlog| ==> AbstractifyRawLogToIos(rawlog)[i] == AbstractifyNetEventToRslIo(rawlog[i])
{
  if (rawlog==[]) then [] else [AbstractifyNetEventToRslIo(rawlog[0])] + AbstractifyRawLogToIos(rawlog[1..])
}

lemma lemma_EstablishAbstractifyRawLogToIos(rawlog:seq<NetEvent>, ios:seq<RslIo>)
  requires NetEventLogIsAbstractable(rawlog)
  requires |rawlog| == |ios|
  requires forall i :: 0<=i<|rawlog| ==> ios[i] == AbstractifyNetEventToRslIo(rawlog[i])
  ensures AbstractifyRawLogToIos(rawlog) == ios
{
  reveal AbstractifyRawLogToIos();
}

predicate RawIoConsistentWithSpecIO(rawlog:seq<NetEvent>, ios:seq<RslIo>)
{
  && NetEventLogIsAbstractable(rawlog)
  && AbstractifyRawLogToIos(rawlog) == ios
}

predicate OnlySentMarshallableData(rawlog:seq<NetEvent>)
{
  forall io :: io in rawlog && io.LIoOpSend? ==> NetPacketBound(io.s.msg) && Marshallable(PaxosDemarshallData(io.s.msg))
}

//////////////////////////////////////////////////////////////////////////////
// These methods wrap the raw NetClient interface
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

method{:timeLimitMultiplier 2} Receive(netClient:NetClient, localAddr:EndPoint, config:CPaxosConfiguration, msg_grammar:G) returns (rr:ReceiveResult, ghost netEvent:NetEvent)
  requires NetClientIsValid(netClient)
  requires netClient.LocalEndPoint() == localAddr
  //requires KnownSendersMatchConfig(config)
  requires CPaxosConfigurationIsValid(config)
  requires msg_grammar == CMessage_grammar()
  modifies NetClientRepr(netClient)
  ensures netClient.env == old(netClient.env)
  ensures netClient.LocalEndPoint() == old(netClient.LocalEndPoint())
  ensures NetClientOk(netClient) <==> !rr.RRFail?
  ensures old(NetClientRepr(netClient)) == NetClientRepr(netClient)
  ensures !rr.RRFail? ==>
            && netClient.IsOpen()
            && old(netClient.env.net.history()) + [netEvent] == netClient.env.net.history()
  ensures rr.RRTimeout? ==> netEvent.LIoOpTimeoutReceive?;
  ensures rr.RRPacket? ==>
            && netEvent.LIoOpReceive?
            && NetPacketIsAbstractable(netEvent.r)
            && CPacketIsAbstractable(rr.cpacket)
            && CMessageIs64Bit(rr.cpacket.msg)
            && EndPointIsValidIPV4(rr.cpacket.src)
            && AbstractifyCPacketToRslPacket(rr.cpacket) == AbstractifyNetPacketToRslPacket(netEvent.r)
            && rr.cpacket.msg == PaxosDemarshallData(netEvent.r.msg)
            && PaxosEndPointIsValid(rr.cpacket.src, config)
{
  var timeout := 0;
  ghost var old_net_history := netClient.env.net.history();
  var ok, timedOut, remote, buffer := netClient.Receive(timeout);

  if (!ok) {
    rr := RRFail();
    return;
  }

  if (timedOut) {
    rr := RRTimeout();
    netEvent := LIoOpTimeoutReceive(); 
    return;
  }

  netEvent := LIoOpReceive(LPacket(netClient.LocalEndPoint(), remote.EP(), buffer[..]));
  assert netClient.env.net.history() == old_net_history + [netEvent];
  var start_time := Time.GetDebugTimeTicks();
  lemma_CMessageGrammarValid();
  var cmessage := PaxosDemarshallDataMethod(buffer, msg_grammar);
  var end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("PaxosDemarshallDataMethod", start_time, end_time);

  var srcEp := GetEndPoint(remote);
  var cpacket := CPacket(localAddr, srcEp, cmessage);
  rr := RRPacket(cpacket);
  assert netClient.env.net.history() == old_net_history + [netEvent];

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

  assert EndPointIsValidIPV4(netClient.LocalEndPoint());
  assert PaxosEndPointIsValid(rr.cpacket.src, config);
  assert AbstractifyCPacketToRslPacket(rr.cpacket) == AbstractifyNetPacketToRslPacket(netEvent.r);

  /*
  forall ()
    ensures AbstractifyCPacketToRslPacket(rr.cpacket) == AbstractifyNetPacketToRslPacket(netEvent.r)
    ensures PaxosEndPointIsValid(rr.cpacket.src, config)
  {
//    lemma_Uint64EndPointRelationships();
//    assert ConvertEndPointToUint64(srcEp) == rr.cpacket.src;    // OBSERVE trigger
      assert EndPointIsValidIPV4(netClient.LocalEndPoint());  // OBSERVE trigger
  }
  */
}

method ReadClock(netClient:NetClient) returns (clock:CClockReading, ghost clockEvent:NetEvent)
  requires NetClientIsValid(netClient)
  modifies NetClientRepr(netClient)
  ensures old(NetClientRepr(netClient)) == NetClientRepr(netClient)
  ensures NetClientIsValid(netClient)
  ensures netClient.env == old(netClient.env)
  ensures old(netClient.env.net.history()) + [clockEvent] == netClient.env.net.history()
  ensures clockEvent.LIoOpReadClock?
  ensures clock.t as int == clockEvent.t
  ensures NetClientIsValid(netClient)
  ensures NetEventIsAbstractable(clockEvent)
  ensures netClient.LocalEndPoint() == old(netClient.LocalEndPoint())
  // TODO we're going to call GetTime, which returns a single value.
{
  var t := Time.GetTime(netClient.env);
  clockEvent := LIoOpReadClock(t as int);
  clock := CClockReading(t);
}

predicate SendLogEntryReflectsPacket(event:NetEvent, cpacket:CPacket)
{
  && event.LIoOpSend?
  && NetPacketIsAbstractable(event.s)
  && CPacketIsAbstractable(cpacket)
  && AbstractifyCPacketToRslPacket(cpacket) == AbstractifyNetPacketToRslPacket(event.s)
}

predicate SendLogReflectsPacket(netEventLog:seq<NetEvent>, packet:Option<CPacket>)
{
  match packet {
    case Some(p) => |netEventLog| == 1 && SendLogEntryReflectsPacket(netEventLog[0], p)
    case None => netEventLog == []
  }
}

predicate SendLogReflectsPacketSeq(netEventLog:seq<NetEvent>, packets:seq<CPacket>)
{
  && |netEventLog| == |packets| 
  && (forall i :: 0 <= i < |packets| ==> SendLogEntryReflectsPacket(netEventLog[i], packets[i]))
}

predicate SendLogMatchesRefinement(netEventLog:seq<NetEvent>, broadcast:CBroadcast, index:int)
  requires CBroadcastIsAbstractable(broadcast)
  requires broadcast.CBroadcast?
  requires 0<=|netEventLog|<=|broadcast.dsts|
  requires 0 <= index < |netEventLog|
{
  && netEventLog[index].LIoOpSend? && NetPacketIsAbstractable(netEventLog[index].s)
  && AbstractifyCBroadcastToRlsPacketSeq(broadcast)[index] == AbstractifyNetPacketToRslPacket(netEventLog[index].s)
}

predicate SendLogReflectsBroadcastPrefix(netEventLog:seq<NetEvent>, broadcast:CBroadcast)
  requires CBroadcastIsAbstractable(broadcast)
  requires broadcast.CBroadcast?
{
  && 0<=|netEventLog|<=|broadcast.dsts|
  && forall i :: 0<=i<|netEventLog| ==> SendLogMatchesRefinement(netEventLog, broadcast, i)
}

predicate SendLogReflectsBroadcast(netEventLog:seq<NetEvent>, broadcast:CBroadcast)
  requires CBroadcastIsAbstractable(broadcast)
{
  if broadcast.CBroadcastNop? then
    netEventLog == []
  else 
    && SendLogReflectsBroadcastPrefix(netEventLog, broadcast)
    && |netEventLog| == |broadcast.dsts|
}

lemma lemma_NetEventLogAppend(broadcast:CBroadcast, netEventLog:seq<NetEvent>, netEvent:NetEvent)
  requires broadcast.CBroadcast?
  requires CBroadcastIsValid(broadcast)
  requires SendLogReflectsBroadcastPrefix(netEventLog, broadcast)
  requires |netEventLog| < |broadcast.dsts|
  requires netEvent.LIoOpSend?
  requires NetPacketIsAbstractable(netEvent.s)
  requires CMessageIsAbstractable(PaxosDemarshallData(netEvent.s.msg))
  requires netEvent.s.dst == broadcast.dsts[|netEventLog|]
  requires netEvent.s.src == broadcast.src
  requires BufferRefinementAgreesWithMessageRefinement(broadcast.msg, netEvent.s.msg)
  ensures SendLogReflectsBroadcastPrefix(netEventLog + [netEvent], broadcast)
{
  var i := |netEventLog|;

  calc {
    AbstractifyCBroadcastToRlsPacketSeq(broadcast)[i];
    BuildLBroadcast(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                    AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                    AbstractifyCMessageToRslMessage(broadcast.msg))[i];
    LPacket(AbstractifyEndPointsToNodeIdentities(broadcast.dsts)[i], 
            AbstractifyEndPointToNodeIdentity(broadcast.src), 
            AbstractifyCMessageToRslMessage(broadcast.msg));
    LPacket(AbstractifyEndPointToNodeIdentity(netEvent.s.dst),
            AbstractifyEndPointToNodeIdentity(netEvent.s.src),
            AbstractifyCMessageToRslMessage(PaxosDemarshallData(netEvent.s.msg)));
    AbstractifyNetPacketToRslPacket(netEvent.s);
  }

  var new_log := netEventLog + [netEvent];

  forall i' | 0 <= i' < |new_log|
    ensures SendLogMatchesRefinement(new_log, broadcast, i')
  {
    if i' < |netEventLog| {
      assert new_log[i'] == netEventLog[i'];
      assert SendLogMatchesRefinement(netEventLog, broadcast, i');
      assert SendLogMatchesRefinement(new_log, broadcast, i');
    } else {
      assert new_log[i'] == netEvent;
      assert SendLogMatchesRefinement(new_log, broadcast, i');
    }
  }

  calc ==> {
    true;
    forall i' :: 0 <= i' < |new_log| ==> SendLogMatchesRefinement(new_log, broadcast, i');
    SendLogReflectsBroadcastPrefix(new_log, broadcast);
    SendLogReflectsBroadcastPrefix(netEventLog + [netEvent], broadcast);
  }
}

method SendBroadcast(netClient:NetClient, broadcast:CBroadcast, ghost localAddr_:EndPoint) returns (ok:bool, ghost netEventLog:seq<NetEvent>)
  requires NetClientIsValid(netClient)
  requires CBroadcastIsValid(broadcast)
  requires netClient.LocalEndPoint() == localAddr_
  requires broadcast.CBroadcast? ==> broadcast.src == localAddr_
  modifies NetClientRepr(netClient)
  ensures old(NetClientRepr(netClient)) == NetClientRepr(netClient)
  ensures netClient.env == old(netClient.env)
  ensures netClient.LocalEndPoint() == old(netClient.LocalEndPoint())
  ensures NetClientOk(netClient) <==> ok
  ensures ok ==>
            && NetClientIsValid(netClient)
            && netClient.IsOpen()
            && old(netClient.env.net.history()) + netEventLog == netClient.env.net.history()
            && OnlySentMarshallableData(netEventLog)
            && SendLogReflectsBroadcast(netEventLog, broadcast)
{
  ok := true;
  netEventLog := [];

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
    assert NetPacketBound(buffer[..]);

    calc ==> {
      true;
      CBroadcastIsValid(broadcast);
      CBroadcastIsAbstractable(broadcast);
      CMessageIsAbstractable(broadcast.msg);
    }

    var i:uint64 := 0;
    while i < |broadcast.dsts| as uint64
      invariant 0 <= i as int <= |broadcast.dsts|
      invariant |netEventLog| == i as int
      invariant NetClientRepr(netClient) == old(NetClientRepr(netClient))
      invariant netClient.env == old(netClient.env)
      invariant netClient.LocalEndPoint() == old(netClient.LocalEndPoint())
      invariant NetClientIsValid(netClient)
      invariant NetClientOk(netClient)
      invariant old(netClient.env.net.history()) + netEventLog == netClient.env.net.history()
      invariant NetPacketBound(buffer[..])
      invariant Marshallable(PaxosDemarshallData(buffer[..]))
      invariant BufferRefinementAgreesWithMessageRefinement(broadcast.msg, buffer[..])
      invariant SendLogReflectsBroadcastPrefix(netEventLog, broadcast)
      invariant CMessageIsAbstractable(PaxosDemarshallData(buffer[..]))
      invariant OnlySentMarshallableData(netEventLog)
    {
      ghost var netEventLog_old := netEventLog;

      // Construct the remote address -- TODO: Only do this once per replica!
      var dstEp:EndPoint := broadcast.dsts[i];
      //var construct_start_time := Time.GetDebugTimeTicks();
      var dstAddrAry := seqToArrayOpt(dstEp.addr);
      var remote;
      ok, remote := IPEndPoint.Construct(dstAddrAry, dstEp.port, netClient.env);
      if (!ok) { return; }
      //var construct_end_time := Time.GetDebugTimeTicks();
      //RecordTimingSeq("SendBroadcast_IPEndPointConstruct", construct_start_time, construct_end_time);

      //var send_start_time := Time.GetDebugTimeTicks();
      ok := netClient.Send(remote, buffer);
      if (!ok) { return; }
      //var send_end_time := Time.GetDebugTimeTicks();
      //RecordTimingSeq("SendBroadcast_Send", send_start_time, send_end_time);

      ghost var netEvent := LIoOpSend(LPacket(remote.EP(), netClient.LocalEndPoint(), buffer[..]));
      netEventLog := netEventLog + [netEvent];

      lemma_NetEventLogAppend(broadcast, netEventLog_old, netEvent);

      i := i + 1;
    }
  }
}


method SendPacket(netClient:NetClient, packets:OutboundPackets, ghost localAddr_:EndPoint) returns (ok:bool, ghost netEventLog:seq<NetEvent>)
  requires NetClientIsValid(netClient)
  requires packets.OutboundPacket?
  requires OutboundPacketsIsValid(packets)
  requires netClient.LocalEndPoint() == localAddr_
  requires OutboundPacketsHasCorrectSrc(packets, localAddr_)
  modifies NetClientRepr(netClient)
  ensures old(NetClientRepr(netClient)) == NetClientRepr(netClient)
  ensures netClient.env == old(netClient.env)
  ensures netClient.LocalEndPoint() == old(netClient.LocalEndPoint())
  ensures NetClientOk(netClient) <==> ok
  ensures ok ==> && NetClientIsValid(netClient)
                 && netClient.IsOpen()
                 && old(netClient.env.net.history()) + netEventLog == netClient.env.net.history()
                 && OnlySentMarshallableData(netEventLog)
                 && SendLogReflectsPacket(netEventLog, packets.p)
{
  var j:uint64 := 0;
  netEventLog := [];
  ok := true;
  var opt_packet := packets.p;

  if opt_packet.None? {

  } else {
    var cpacket := opt_packet.v;

    ghost var netEventLog_old := netEventLog;

    // Construct the remote address
    var dstEp:EndPoint := cpacket.dst;
    var dstAddrAry := seqToArrayOpt(dstEp.addr);
    var remote;
    ok, remote := IPEndPoint.Construct(dstAddrAry, dstEp.port, netClient.env);
    if (!ok) { return; }

    assert CMessageIsAbstractable(cpacket.msg);
    assert Marshallable(cpacket.msg);
    var marshall_start_time := Time.GetDebugTimeTicks();
    var buffer := PaxosMarshall(cpacket.msg);
    var marshall_end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("SendBatch_PaxosMarshall", marshall_start_time, marshall_end_time);

    ghost var data := buffer[..];
    assert BufferRefinementAgreesWithMessageRefinement(cpacket.msg, data);

    ok := netClient.Send(remote, buffer);
    if (!ok) { return; }

    ghost var netEvent := LIoOpSend(LPacket(remote.EP(), netClient.LocalEndPoint(), buffer[..]));
    ghost var net := netEvent.s;

    calc {
      AbstractifyCPacketToRslPacket(cpacket);
      LPacket(AbstractifyEndPointToNodeIdentity(cpacket.dst), AbstractifyEndPointToNodeIdentity(cpacket.src), AbstractifyCMessageToRslMessage(cpacket.msg));
      LPacket(AbstractifyEndPointToNodeIdentity(net.dst), AbstractifyEndPointToNodeIdentity(net.src), AbstractifyCMessageToRslMessage(cpacket.msg));
      AbstractifyBufferToRslPacket(net.src, net.dst, data);
      AbstractifyBufferToRslPacket(net.src, net.dst, net.msg);
      AbstractifyNetPacketToRslPacket(netEvent.s);
    }
    assert SendLogEntryReflectsPacket(netEvent, cpacket);
    netEventLog := [netEvent];
  }
}


method{:timeLimitMultiplier 2} SendPacketSequence(netClient:NetClient, packets:OutboundPackets, ghost localAddr_:EndPoint) returns (ok:bool, ghost netEventLog:seq<NetEvent>)
  requires NetClientIsValid(netClient)
  requires OutboundPacketsIsValid(packets)
  requires packets.PacketSequence?
  requires netClient.LocalEndPoint() == localAddr_
  requires OutboundPacketsHasCorrectSrc(packets, localAddr_)
  modifies NetClientRepr(netClient)
  ensures old(NetClientRepr(netClient)) == NetClientRepr(netClient)
  ensures netClient.env == old(netClient.env)
  ensures netClient.LocalEndPoint() == old(netClient.LocalEndPoint())
  ensures NetClientOk(netClient) <==> ok
  ensures ok ==>
            && NetClientIsValid(netClient)
            && netClient.IsOpen()
            && old(netClient.env.net.history()) + netEventLog == netClient.env.net.history()
            && OnlySentMarshallableData(netEventLog)
            && SendLogReflectsPacketSeq(netEventLog, packets.s)
{
  var cpackets := packets.s;
  var j:uint64 := 0;
  netEventLog := [];
  ok := true;
    
  ghost var netEventLog_old := netEventLog;
  ghost var netClientEnvHistory_old := old(netClient.env.net.history());
  var i:uint64 := 0;

  while i < |cpackets| as uint64
    invariant old(NetClientRepr(netClient)) == NetClientRepr(netClient)
    invariant netClient.env == old(netClient.env)
    invariant netClient.LocalEndPoint() == old(netClient.LocalEndPoint())
    invariant NetClientOk(netClient) <==> ok
    invariant ok ==> ( NetClientIsValid(netClient) && netClient.IsOpen())
    invariant ok ==> netClientEnvHistory_old + netEventLog == netClient.env.net.history()
    invariant (i == 0) ==> |netEventLog| == 0
    invariant (0 < i as int < |cpackets|) ==> |netEventLog| == |cpackets[0..i]|
    invariant (0 < i as int < |cpackets|) ==> SendLogReflectsPacketSeq(netEventLog, cpackets[0..i]);
    invariant (i as int >= |cpackets|) ==> SendLogReflectsPacketSeq(netEventLog, cpackets);
    invariant OnlySentMarshallableData(netEventLog)
  {
    var cpacket := cpackets[i];
    // Construct the remote address
    var dstEp:EndPoint := cpacket.dst;
    assert cpacket in cpackets;
    assert OutboundPacketsIsValid(packets);

    var dstAddrAry := seqToArrayOpt(dstEp.addr);
    var remote;
    ok, remote := IPEndPoint.Construct(dstAddrAry, dstEp.port, netClient.env);
    if (!ok) { return; }

    assert CMessageIsAbstractable(cpacket.msg);
         
    assert Marshallable(cpacket.msg);
    var buffer := PaxosMarshall(cpacket.msg);

    ghost var data := buffer[..];
    assert BufferRefinementAgreesWithMessageRefinement(cpacket.msg, data);

    ok := netClient.Send(remote, buffer);
    if (!ok) { return; }

    ghost var netEvent := LIoOpSend(LPacket(remote.EP(), netClient.LocalEndPoint(), buffer[..]));
    ghost var net := netEvent.s;

    calc {
      AbstractifyCPacketToRslPacket(cpacket);
      LPacket(AbstractifyEndPointToNodeIdentity(cpacket.dst), AbstractifyEndPointToNodeIdentity(cpacket.src), AbstractifyCMessageToRslMessage(cpacket.msg));
      LPacket(AbstractifyEndPointToNodeIdentity(net.dst), AbstractifyEndPointToNodeIdentity(net.src), AbstractifyCMessageToRslMessage(cpacket.msg));
      AbstractifyBufferToRslPacket(net.src, net.dst, data);
      AbstractifyBufferToRslPacket(net.src, net.dst, net.msg);
      AbstractifyNetPacketToRslPacket(netEvent.s);
    }
        
    assert SendLogEntryReflectsPacket(netEvent, cpacket);
        
    netEventLog := netEventLog + [netEvent];
    assert cpackets[0..(i as int+1)] == cpackets[0..i as int] + [cpacket];
    assert SendLogReflectsPacketSeq(netEventLog, cpackets[0..(i as int+1)]);
    i := i + 1;
  }
}

} 
