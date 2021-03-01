include "../Common/UdpClient.i.dfy"
include "../SHT/PacketParsing.i.dfy"
include "../../Protocol/LiveSHT/RefinementProof/Environment.i.dfy"
include "../SHT/SHTConcreteConfiguration.i.dfy"
include "../SHT/CMessage.i.dfy"

module LiveSHT__UdpSHT_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened Environment_s
import opened Common__Util_i
import opened Common__UdpClient_i
import opened Common__NodeIdentity_i
import opened SHT__PacketParsing_i
import opened LiveSHT__Environment_i
import opened SHT__SHTConcreteConfiguration_i
import opened SHT__CMessage_i

predicate UdpEventIsAbstractable(evt:UdpEvent)
{
    match evt
        case LIoOpSend(s) => UdpPacketIsAbstractable(s)
        case LIoOpReceive(r) => UdpPacketIsAbstractable(r)
        case LIoOpTimeoutReceive => true
        case LIoOpReadClock(t) => true
}

function AbstractifyUdpEventToLSHTIo(evt:UdpEvent) : LSHTIo
    requires UdpEventIsAbstractable(evt);
{
    match evt
        case LIoOpSend(s) => LIoOpSend(AbstractifyUdpPacketToLSHTPacket(s))
        case LIoOpReceive(r) => LIoOpReceive(AbstractifyUdpPacketToLSHTPacket(r))
        case LIoOpTimeoutReceive => LIoOpTimeoutReceive()
        case LIoOpReadClock(t) => LIoOpReadClock(t as int)
}


predicate UdpEventLogIsAbstractable(rawlog:seq<UdpEvent>)
{
    forall i :: 0<=i<|rawlog| ==> UdpEventIsAbstractable(rawlog[i])
}

function {:opaque} AbstractifyRawLogToIos(rawlog:seq<UdpEvent>) : seq<LSHTIo>
    requires UdpEventLogIsAbstractable(rawlog);
    ensures |AbstractifyRawLogToIos(rawlog)| == |rawlog|;
    ensures forall i {:trigger AbstractifyUdpEventToLSHTIo(rawlog[i])} {:trigger AbstractifyRawLogToIos(rawlog)[i]} :: 0<=i<|rawlog| ==> AbstractifyRawLogToIos(rawlog)[i] == AbstractifyUdpEventToLSHTIo(rawlog[i]);
{
    if (rawlog==[]) then [] else [AbstractifyUdpEventToLSHTIo(rawlog[0])] + AbstractifyRawLogToIos(rawlog[1..])
}

lemma lemma_AbstractifyRawLogToIos_properties(rawlog:seq<UdpEvent>, ios:seq<LSHTIo>)
    requires UdpEventLogIsAbstractable(rawlog);
    requires |rawlog| == |ios|;
    requires forall i :: 0<=i<|rawlog| ==> ios[i] == AbstractifyUdpEventToLSHTIo(rawlog[i]);
    ensures AbstractifyRawLogToIos(rawlog) == ios;
{
    reveal_AbstractifyRawLogToIos();
}

predicate RawIoConsistentWithSpecIO(rawlog:seq<UdpEvent>, ios:seq<LSHTIo>)
{
       UdpEventLogIsAbstractable(rawlog)
    && AbstractifyRawLogToIos(rawlog) == ios
}

predicate OnlySentMarshallableData(rawlog:seq<UdpEvent>)
{
    forall io :: io in rawlog && io.LIoOpSend? ==> UdpPacketBound(io.s.msg) && CSingleMessageMarshallable(SHTDemarshallData(io.s.msg))
}

//////////////////////////////////////////////////////////////////////////////
// These methods wrap the raw UdpClient interface
//

datatype ReceiveResult = RRFail() | RRTimeout() | RRPacket(cpacket:CPacket)

method GetEndPoint(ipe:IPEndPoint) returns (ep:EndPoint)
    ensures ep == ipe.EP();
    ensures EndPointIsValidIPV4(ep);
{
    var addr := ipe.GetAddress();
    var port := ipe.GetPort();
    ep := EndPoint(addr[..], port);
}

method Receive(udpClient:UdpClient, localAddr:EndPoint) returns (rr:ReceiveResult, ghost udpEvent:UdpEvent)
    requires UdpClientIsValid(udpClient);
    requires udpClient.LocalEndPoint() == localAddr;
    //requires KnownSendersMatchConfig(config);
    //requires SHTConcreteConfigurationIsValid(config);
    modifies UdpClientRepr(udpClient);
    ensures udpClient.env == old(udpClient.env);
    ensures udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint());
    ensures UdpClientOk(udpClient) <==> !rr.RRFail?;
    ensures old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient);
    ensures !rr.RRFail? ==>
           udpClient.IsOpen()
        && old(udpClient.env.udp.history()) + [udpEvent] == udpClient.env.udp.history();
    ensures rr.RRTimeout? ==>
        udpEvent.LIoOpTimeoutReceive?;
    ensures rr.RRPacket? ==>
           udpEvent.LIoOpReceive?
        && UdpPacketIsAbstractable(udpEvent.r)
        && CPacketIsAbstractable(rr.cpacket)
        && EndPointIsValidIPV4(rr.cpacket.src)
        && AbstractifyCPacketToShtPacket(rr.cpacket) == AbstractifyUdpPacketToShtPacket(udpEvent.r)
        && rr.cpacket.msg == SHTDemarshallData(udpEvent.r.msg)
        && (rr.cpacket.dst == localAddr)
{
    var timeout := 0;    
    var ok, timedOut, remote, buffer := udpClient.Receive(timeout);

    if (!ok) {
        rr := RRFail();
        return;
    }

    if (timedOut) {
        rr := RRTimeout();
        udpEvent := LIoOpTimeoutReceive(); 
        return;
    } else {
        var start_time := Time.GetDebugTimeTicks();
        var cmessage := SHTDemarshallDataMethod(buffer);
        var end_time := Time.GetDebugTimeTicks();
        var srcEp := GetEndPoint(remote);
        var cpacket := CPacket(localAddr, srcEp, cmessage);
        rr := RRPacket(cpacket);
        udpEvent := LIoOpReceive(LPacket(udpClient.LocalEndPoint(), remote.EP(), buffer[..]));
        forall ()
            ensures AbstractifyCPacketToShtPacket(rr.cpacket) == AbstractifyUdpPacketToShtPacket(udpEvent.r);
            //ensures SHTEndPointIsValid(rr.cpacket.src, config);
        {
//            Uint64EndPointRelationships();
//            assert ConvertEndPointToUint64(srcEp) == rr.cpacket.src;    // OBSERVE trigger
            assert EndPointIsValidIPV4(udpClient.LocalEndPoint());  // OBSERVE trigger
        }
    }
}

/*
method ReadClock(udpClient:UdpClient) returns (clock:CBoundedClock, ghost clockEvent:UdpEvent)
    requires UdpClientIsValid(udpClient);
    modifies UdpClientRepr(udpClient);
    ensures old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient);
    ensures UdpClientIsValid(udpClient);
    ensures udpClient.env == old(udpClient.env);
    ensures old(udpClient.env.udp.history()) + [clockEvent] == udpClient.env.udp.history();
    ensures clockEvent.UdpGetTime?;
    ensures clock.min as int <= clockEvent.time as int <= clock.max as int;
    ensures UdpClientIsValid(udpClient);
    ensures UdpEventIsAbstractable(clockEvent);
    ensures udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint());
    ensures clock.min==clock.max==clockEvent.time;  // silly
    // ensures clockEvent.ClockEvent(clock_min, clock_max);
    // TODO we're going to call GetTime, which returns a single value.
    // Add/subtract the margin of error to make a CBoundedClock.
    // TODO Jay: if I pretend the margin is 0, how will the verification fail?
{
    var t := Time.GetTime(udpClient.env);
    var u := t as uint64;
    clockEvent := UdpGetTime(t);
    clock := CBoundedClock(t,t);
}
*/

predicate SendLogEntryReflectsPacket(event:UdpEvent, cpacket:CPacket)
{
       event.LIoOpSend?
    && UdpPacketIsAbstractable(event.s)
    && CPacketIsAbstractable(cpacket)
    && AbstractifyCPacketToShtPacket(cpacket) == AbstractifyUdpPacketToShtPacket(event.s)
}

predicate SendLogReflectsPacket(udpEventLog:seq<UdpEvent>, packets:seq<CPacket>)
{
       |udpEventLog| == |packets| 
    && (forall i :: 0 <= i < |packets| ==> SendLogEntryReflectsPacket(udpEventLog[i], packets[i]))
}

/*
predicate SendLogMatchesRefinement(udpEventLog:seq<UdpEvent>, broadcast:CBroadcast, index:int)
    requires CBroadcastIsAbstractable(broadcast);
    requires broadcast.CBroadcast?;
    requires 0<=|udpEventLog|<=|broadcast.dsts|
    requires 0 <= index < |udpEventLog|;
{
      udpEventLog[index].UdpSendEvent? && UdpPacketIsAbstractable(udpEventLog[index].sendPacket)
   && AbstractifyCBroadcastToRlsPacketSeq(broadcast)[index] == AbstractifyCPacketToShtPacket(udpEventLog[index].sendPacket)
}

predicate SendLogReflectsBroadcastPrefix(udpEventLog:seq<UdpEvent>, broadcast:CBroadcast)
    requires CBroadcastIsAbstractable(broadcast);
    requires broadcast.CBroadcast?;
{
       0<=|udpEventLog|<=|broadcast.dsts|
    && forall i :: 0<=i<|udpEventLog| ==> SendLogMatchesRefinement(udpEventLog, broadcast, i)
}
*/

/*
predicate SendLogReflectsBroadcast(udpEventLog:seq<UdpEvent>, broadcast:CBroadcast)
    requires CBroadcastIsAbstractable(broadcast);
{
    if broadcast.CBroadcastNop? then udpEventLog == []
    else 
       SendLogReflectsBroadcastPrefix(udpEventLog, broadcast)
    && |udpEventLog| == |broadcast.dsts|
}

lemma lemma_UdpEventLogAppend(broadcast:CBroadcast, udpEventLog:seq<UdpEvent>, udpEvent:UdpEvent)
    requires broadcast.CBroadcast?;
    requires CBroadcastIsValid(broadcast);
    requires SendLogReflectsBroadcastPrefix(udpEventLog, broadcast);
    requires |udpEventLog| < |broadcast.dsts|;
    requires udpEvent.UdpSendEvent?;
    requires UdpPacketIsAbstractable(udpEvent.sendPacket);
    requires CMessageIsAbstractable(PaxosDemarshallData(udpEvent.sendPacket.data));
    requires udpEvent.sendPacket.dst == broadcast.dsts[|udpEventLog|];
    requires udpEvent.sendPacket.src == broadcast.src;
    requires BufferRefinementAgreesWithMessageRefinement(broadcast.msg, udpEvent.sendPacket.data);
    ensures SendLogReflectsBroadcastPrefix(udpEventLog + [udpEvent], broadcast);
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
        LPacket(AbstractifyEndPointToNodeIdentity(udpEvent.sendPacket.dst),
                AbstractifyEndPointToNodeIdentity(udpEvent.sendPacket.src),
                AbstractifyCMessageToRslMessage(PaxosDemarshallData(udpEvent.sendPacket.data)));
        AbstractifyCPacketToShtPacket(udpEvent.sendPacket);
    }

    var new_log := udpEventLog + [udpEvent];

    forall i | 0 <= i < |new_log|
        ensures SendLogMatchesRefinement(new_log, broadcast, i);
    {
        if i < |udpEventLog| {
            assert new_log[i] == udpEventLog[i];
            assert SendLogMatchesRefinement(udpEventLog, broadcast, i);
            assert SendLogMatchesRefinement(new_log, broadcast, i);
        } else {
            assert new_log[i] == udpEvent;
            assert SendLogMatchesRefinement(new_log, broadcast, i);
        }
    }

    calc ==> {
        true;
        forall i :: 0 <= i < |new_log| ==> SendLogMatchesRefinement(new_log, broadcast, i);
        SendLogReflectsBroadcastPrefix(new_log, broadcast);
        SendLogReflectsBroadcastPrefix(udpEventLog + [udpEvent], broadcast);
    }
    
}
*/


/*
method SendBroadcast(udpClient:UdpClient, broadcast:CBroadcast, ghost localAddr_:EndPoint) returns (ok:bool, ghost udpEventLog:seq<UdpEvent>)
    requires UdpClientIsValid(udpClient);
    requires CBroadcastIsValid(broadcast);
    requires udpClient.LocalEndPoint() == localAddr_;
    requires broadcast.CBroadcast? ==> broadcast.src == localAddr_;
    modifies UdpClientRepr(udpClient);
    ensures old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient);
    ensures udpClient.env == old(udpClient.env);
    ensures udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint());
    ensures UdpClientOk(udpClient) <==> ok;
    ensures ok ==> (
           UdpClientIsValid(udpClient)
        && udpClient.IsOpen()
        && old(udpClient.env.udp.history()) + udpEventLog == udpClient.env.udp.history()
        && SendLogReflectsBroadcast(udpEventLog, broadcast));
{
    ok := true;
    udpEventLog := [];

    if broadcast.CBroadcastNop? {
        // No work to do!
    } else {
        // Do the marshalling work once
        assert CMessageIsAbstractable(broadcast.msg);
        assert Marshallable(broadcast.msg);
        var buffer := PaxosMarshall(broadcast.msg);
        assert PaxosDemarshallable(buffer[..]);

        calc ==> {
            true;
            CBroadcastIsValid(broadcast);
            CBroadcastIsAbstractable(broadcast);
            CMessageIsAbstractable(broadcast.msg);
        }

        lemma_PaxosDemarshallableImpliesRefinable(buffer[..]);

        var i:uint64 := 0;
        while i < |broadcast.dsts| as uint64
            invariant 0 <= i as int <= |broadcast.dsts|;
            invariant |udpEventLog| == i as int;
            invariant UdpClientRepr(udpClient) == old(UdpClientRepr(udpClient));
            invariant udpClient.env == old(udpClient.env);
            invariant udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint());
            invariant UdpClientIsValid(udpClient);
            invariant UdpClientOk(udpClient);
            invariant old(udpClient.env.udp.history()) + udpEventLog == udpClient.env.udp.history();
            invariant PaxosDemarshallable(buffer[..]);
            invariant BufferRefinementAgreesWithMessageRefinement(broadcast.msg, buffer[..]);
            invariant SendLogReflectsBroadcastPrefix(udpEventLog, broadcast);
            invariant CMessageIsAbstractable(PaxosDemarshallData(buffer[..]));
        {
            ghost var udpEventLog_old := udpEventLog;

            // Construct the remote address -- TODO: Only do this once per replica!
            var dstEp:EndPoint := broadcast.dsts[i];
            var dstAddrAry := seqToArrayOpt(dstEp.addr);
            var remote;
            ok, remote := IPEndPoint.Construct(dstAddrAry, dstEp.port, udpClient.env);
            if (!ok) { return; }

            ok := udpClient.Send(remote, buffer);
            if (!ok) { return; }

            ghost var udpEvent := UdpSendEvent(UdpPacket_ctor(remote.EP(), udpClient.LocalEndPoint(), buffer[..]));
            udpEventLog := udpEventLog + [udpEvent];

            lemma_UdpEventLogAppend(broadcast, udpEventLog_old, udpEvent);

            i := i + 1;
        }
    }

}
*/


method SendPacketSeq(udpClient:UdpClient, cpackets:seq<CPacket>, ghost localAddr_:EndPoint) returns (ok:bool, ghost udpEventLog:seq<UdpEvent>)
    requires UdpClientIsValid(udpClient);
    requires OutboundPacketsSeqIsValid(cpackets);
    requires udpClient.LocalEndPoint() == localAddr_;
    requires OutboundPacketsSeqHasCorrectSrc(cpackets, localAddr_);
    modifies UdpClientRepr(udpClient);
    ensures old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient);
    ensures udpClient.env == old(udpClient.env);
    ensures udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint());
    ensures UdpClientOk(udpClient) <==> ok;
    ensures ok ==> ( UdpClientIsValid(udpClient) && udpClient.IsOpen());
    ensures ok ==> old(udpClient.env.udp.history()) + udpEventLog == udpClient.env.udp.history();
    ensures ok ==> SendLogReflectsPacket(udpEventLog, cpackets) && OnlySentMarshallableData(udpEventLog);
{
    var j:uint64 := 0;
    udpEventLog := [];
    ok := true;
    
    ghost var udpEventLog_old := udpEventLog;
    ghost var udpClientEnvHistory_old := old(udpClient.env.udp.history());
    var i := 0;

    while (i < |cpackets|)
        invariant old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient);
        invariant udpClient.env == old(udpClient.env);
        invariant udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint());
        invariant UdpClientOk(udpClient) <==> ok;
        invariant ok ==> ( UdpClientIsValid(udpClient) && udpClient.IsOpen());
        invariant ok ==> udpClientEnvHistory_old + udpEventLog == udpClient.env.udp.history();
        invariant ok ==> OnlySentMarshallableData(udpEventLog);
        invariant (i == 0) ==> |udpEventLog| == 0;
        invariant (0 < i < |cpackets|) ==> |udpEventLog| == |cpackets[0..i]|;
        invariant (0 < i < |cpackets|) ==> SendLogReflectsPacket(udpEventLog, cpackets[0..i]); 
        invariant (i >= |cpackets|) ==> SendLogReflectsPacket(udpEventLog, cpackets); 
        
    {
        var cpacket := cpackets[i];
        // Construct the remote address
        var dstEp:EndPoint := cpacket.dst;
        assert cpacket in cpackets;
        assert OutboundPacketsIsValid(cpacket);


        var dstAddrAry := seqToArrayOpt(dstEp.addr);
        var remote;
        ok, remote := IPEndPoint.Construct(dstAddrAry, dstEp.port, udpClient.env);
        if (!ok) { return; }

        assert CSingleMessageIsAbstractable(cpacket.msg);
         
        assert CSingleMessageMarshallable(cpacket.msg);
        var buffer := SHTMarshall(cpacket.msg);

        ghost var data := buffer[..];
        assert BufferRefinementAgreesWithMessageRefinement(cpacket.msg, data);

        ok := udpClient.Send(remote, buffer);
        if (!ok) { return; }

        ghost var udpEvent := LIoOpSend(LPacket(remote.EP(), udpClient.LocalEndPoint(), buffer[..]));
        ghost var udp := udpEvent.s;

        calc {
            AbstractifyCPacketToLSHTPacket(cpacket);
            LPacket(AbstractifyEndPointToNodeIdentity(cpacket.dst), AbstractifyEndPointToNodeIdentity(cpacket.src), AbstractifyCSingleMessageToSingleMessage(cpacket.msg));
            LPacket(AbstractifyEndPointToNodeIdentity(udp.dst), AbstractifyEndPointToNodeIdentity(udp.src), AbstractifyCSingleMessageToSingleMessage(cpacket.msg));
            AbstractifyBufferToLSHTPacket(udp.src, udp.dst, data);
            AbstractifyBufferToLSHTPacket(udp.src, udp.dst, udp.msg);
            AbstractifyUdpPacketToLSHTPacket(udpEvent.s);
        }
        
        assert SendLogEntryReflectsPacket(udpEvent, cpacket);
        assert OnlySentMarshallableData(udpEventLog);
        assert UdpPacketBound(udpEvent.s.msg) && CSingleMessageMarshallable(SHTDemarshallData(udpEvent.s.msg));
        udpEventLog := udpEventLog + [udpEvent];
        assert cpackets[0..(i+1)] == cpackets[0..i] + [cpacket];
        assert SendLogReflectsPacket(udpEventLog, cpackets[0..(i+1)]);
        assert OnlySentMarshallableData(udpEventLog);
        i := i + 1;
    }
}
} 
