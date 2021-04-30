include "../Common/NetClient.i.dfy"
include "../SHT/PacketParsing.i.dfy"
include "../../Protocol/LiveSHT/RefinementProof/Environment.i.dfy"
include "../SHT/SHTConcreteConfiguration.i.dfy"
include "../SHT/CMessage.i.dfy"

module LiveSHT__NetSHT_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened Environment_s
import opened Common__Util_i
import opened Common__NetClient_i
import opened Common__NodeIdentity_i
import opened SHT__PacketParsing_i
import opened LiveSHT__Environment_i
import opened SHT__SHTConcreteConfiguration_i
import opened SHT__CMessage_i

predicate NetEventIsAbstractable(evt:NetEvent)
{
    match evt
        case LIoOpSend(s) => NetPacketIsAbstractable(s)
        case LIoOpReceive(r) => NetPacketIsAbstractable(r)
        case LIoOpTimeoutReceive => true
        case LIoOpReadClock(t) => true
}

function AbstractifyNetEventToLSHTIo(evt:NetEvent) : LSHTIo
    requires NetEventIsAbstractable(evt);
{
    match evt
        case LIoOpSend(s) => LIoOpSend(AbstractifyNetPacketToLSHTPacket(s))
        case LIoOpReceive(r) => LIoOpReceive(AbstractifyNetPacketToLSHTPacket(r))
        case LIoOpTimeoutReceive => LIoOpTimeoutReceive()
        case LIoOpReadClock(t) => LIoOpReadClock(t as int)
}


predicate NetEventLogIsAbstractable(rawlog:seq<NetEvent>)
{
    forall i :: 0<=i<|rawlog| ==> NetEventIsAbstractable(rawlog[i])
}

function {:opaque} AbstractifyRawLogToIos(rawlog:seq<NetEvent>) : seq<LSHTIo>
    requires NetEventLogIsAbstractable(rawlog);
    ensures |AbstractifyRawLogToIos(rawlog)| == |rawlog|;
    ensures forall i {:trigger AbstractifyNetEventToLSHTIo(rawlog[i])} {:trigger AbstractifyRawLogToIos(rawlog)[i]} :: 0<=i<|rawlog| ==> AbstractifyRawLogToIos(rawlog)[i] == AbstractifyNetEventToLSHTIo(rawlog[i]);
{
    if (rawlog==[]) then [] else [AbstractifyNetEventToLSHTIo(rawlog[0])] + AbstractifyRawLogToIos(rawlog[1..])
}

lemma lemma_AbstractifyRawLogToIos_properties(rawlog:seq<NetEvent>, ios:seq<LSHTIo>)
    requires NetEventLogIsAbstractable(rawlog);
    requires |rawlog| == |ios|;
    requires forall i :: 0<=i<|rawlog| ==> ios[i] == AbstractifyNetEventToLSHTIo(rawlog[i]);
    ensures AbstractifyRawLogToIos(rawlog) == ios;
{
    reveal_AbstractifyRawLogToIos();
}

predicate RawIoConsistentWithSpecIO(rawlog:seq<NetEvent>, ios:seq<LSHTIo>)
{
       NetEventLogIsAbstractable(rawlog)
    && AbstractifyRawLogToIos(rawlog) == ios
}

predicate OnlySentMarshallableData(rawlog:seq<NetEvent>)
{
    forall io :: io in rawlog && io.LIoOpSend? ==> NetPacketBound(io.s.msg) && CSingleMessageMarshallable(SHTDemarshallData(io.s.msg))
}

//////////////////////////////////////////////////////////////////////////////
// These methods wrap the raw NetClient interface
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

method Receive(netClient:NetClient, localAddr:EndPoint) returns (rr:ReceiveResult, ghost netEvent:NetEvent)
    requires NetClientIsValid(netClient);
    requires netClient.LocalEndPoint() == localAddr;
    //requires KnownSendersMatchConfig(config);
    //requires SHTConcreteConfigurationIsValid(config);
    modifies NetClientRepr(netClient);
    ensures netClient.env == old(netClient.env);
    ensures netClient.LocalEndPoint() == old(netClient.LocalEndPoint());
    ensures NetClientOk(netClient) <==> !rr.RRFail?;
    ensures old(NetClientRepr(netClient)) == NetClientRepr(netClient);
    ensures !rr.RRFail? ==>
           netClient.IsOpen()
        && old(netClient.env.net.history()) + [netEvent] == netClient.env.net.history();
    ensures rr.RRTimeout? ==>
        netEvent.LIoOpTimeoutReceive?;
    ensures rr.RRPacket? ==>
           netEvent.LIoOpReceive?
        && NetPacketIsAbstractable(netEvent.r)
        && CPacketIsAbstractable(rr.cpacket)
        && EndPointIsValidIPV4(rr.cpacket.src)
        && AbstractifyCPacketToShtPacket(rr.cpacket) == AbstractifyNetPacketToShtPacket(netEvent.r)
        && rr.cpacket.msg == SHTDemarshallData(netEvent.r.msg)
        && (rr.cpacket.dst == localAddr)
{
    var timeout := 0;    
    var ok, timedOut, remote, buffer := netClient.Receive(timeout);

    if (!ok) {
        rr := RRFail();
        return;
    }

    if (timedOut) {
        rr := RRTimeout();
        netEvent := LIoOpTimeoutReceive(); 
        return;
    } else {
        var start_time := Time.GetDebugTimeTicks();
        var cmessage := SHTDemarshallDataMethod(buffer);
        var end_time := Time.GetDebugTimeTicks();
        var srcEp := GetEndPoint(remote);
        var cpacket := CPacket(localAddr, srcEp, cmessage);
        rr := RRPacket(cpacket);
        netEvent := LIoOpReceive(LPacket(netClient.LocalEndPoint(), remote.EP(), buffer[..]));
        forall ()
            ensures AbstractifyCPacketToShtPacket(rr.cpacket) == AbstractifyNetPacketToShtPacket(netEvent.r);
            //ensures SHTEndPointIsValid(rr.cpacket.src, config);
        {
//            Uint64EndPointRelationships();
//            assert ConvertEndPointToUint64(srcEp) == rr.cpacket.src;    // OBSERVE trigger
            assert EndPointIsValidIPV4(netClient.LocalEndPoint());  // OBSERVE trigger
        }
    }
}

/*
method ReadClock(netClient:NetClient) returns (clock:CBoundedClock, ghost clockEvent:NetEvent)
    requires NetClientIsValid(netClient);
    modifies NetClientRepr(netClient);
    ensures old(NetClientRepr(netClient)) == NetClientRepr(netClient);
    ensures NetClientIsValid(netClient);
    ensures netClient.env == old(netClient.env);
    ensures old(netClient.env.net.history()) + [clockEvent] == netClient.env.net.history();
    ensures clockEvent.NetGetTime?;
    ensures clock.min as int <= clockEvent.time as int <= clock.max as int;
    ensures NetClientIsValid(netClient);
    ensures NetEventIsAbstractable(clockEvent);
    ensures netClient.LocalEndPoint() == old(netClient.LocalEndPoint());
    ensures clock.min==clock.max==clockEvent.time;  // silly
    // ensures clockEvent.ClockEvent(clock_min, clock_max);
    // TODO we're going to call GetTime, which returns a single value.
    // Add/subtract the margin of error to make a CBoundedClock.
    // TODO Jay: if I pretend the margin is 0, how will the verification fail?
{
    var t := Time.GetTime(netClient.env);
    var u := t as uint64;
    clockEvent := NetGetTime(t);
    clock := CBoundedClock(t,t);
}
*/

predicate SendLogEntryReflectsPacket(event:NetEvent, cpacket:CPacket)
{
       event.LIoOpSend?
    && NetPacketIsAbstractable(event.s)
    && CPacketIsAbstractable(cpacket)
    && AbstractifyCPacketToShtPacket(cpacket) == AbstractifyNetPacketToShtPacket(event.s)
}

predicate SendLogReflectsPacket(netEventLog:seq<NetEvent>, packets:seq<CPacket>)
{
       |netEventLog| == |packets| 
    && (forall i :: 0 <= i < |packets| ==> SendLogEntryReflectsPacket(netEventLog[i], packets[i]))
}

/*
predicate SendLogMatchesRefinement(netEventLog:seq<NetEvent>, broadcast:CBroadcast, index:int)
    requires CBroadcastIsAbstractable(broadcast);
    requires broadcast.CBroadcast?;
    requires 0<=|netEventLog|<=|broadcast.dsts|
    requires 0 <= index < |netEventLog|;
{
      netEventLog[index].NetSendEvent? && NetPacketIsAbstractable(netEventLog[index].sendPacket)
   && AbstractifyCBroadcastToRlsPacketSeq(broadcast)[index] == AbstractifyCPacketToShtPacket(netEventLog[index].sendPacket)
}

predicate SendLogReflectsBroadcastPrefix(netEventLog:seq<NetEvent>, broadcast:CBroadcast)
    requires CBroadcastIsAbstractable(broadcast);
    requires broadcast.CBroadcast?;
{
       0<=|netEventLog|<=|broadcast.dsts|
    && forall i :: 0<=i<|netEventLog| ==> SendLogMatchesRefinement(netEventLog, broadcast, i)
}
*/

/*
predicate SendLogReflectsBroadcast(netEventLog:seq<NetEvent>, broadcast:CBroadcast)
    requires CBroadcastIsAbstractable(broadcast);
{
    if broadcast.CBroadcastNop? then netEventLog == []
    else 
       SendLogReflectsBroadcastPrefix(netEventLog, broadcast)
    && |netEventLog| == |broadcast.dsts|
}

lemma lemma_NetEventLogAppend(broadcast:CBroadcast, netEventLog:seq<NetEvent>, netEvent:NetEvent)
    requires broadcast.CBroadcast?;
    requires CBroadcastIsValid(broadcast);
    requires SendLogReflectsBroadcastPrefix(netEventLog, broadcast);
    requires |netEventLog| < |broadcast.dsts|;
    requires netEvent.NetSendEvent?;
    requires NetPacketIsAbstractable(netEvent.sendPacket);
    requires CMessageIsAbstractable(PaxosDemarshallData(netEvent.sendPacket.data));
    requires netEvent.sendPacket.dst == broadcast.dsts[|netEventLog|];
    requires netEvent.sendPacket.src == broadcast.src;
    requires BufferRefinementAgreesWithMessageRefinement(broadcast.msg, netEvent.sendPacket.data);
    ensures SendLogReflectsBroadcastPrefix(netEventLog + [netEvent], broadcast);
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
        LPacket(AbstractifyEndPointToNodeIdentity(netEvent.sendPacket.dst),
                AbstractifyEndPointToNodeIdentity(netEvent.sendPacket.src),
                AbstractifyCMessageToRslMessage(PaxosDemarshallData(netEvent.sendPacket.data)));
        AbstractifyCPacketToShtPacket(netEvent.sendPacket);
    }

    var new_log := netEventLog + [netEvent];

    forall i | 0 <= i < |new_log|
        ensures SendLogMatchesRefinement(new_log, broadcast, i);
    {
        if i < |netEventLog| {
            assert new_log[i] == netEventLog[i];
            assert SendLogMatchesRefinement(netEventLog, broadcast, i);
            assert SendLogMatchesRefinement(new_log, broadcast, i);
        } else {
            assert new_log[i] == netEvent;
            assert SendLogMatchesRefinement(new_log, broadcast, i);
        }
    }

    calc ==> {
        true;
        forall i :: 0 <= i < |new_log| ==> SendLogMatchesRefinement(new_log, broadcast, i);
        SendLogReflectsBroadcastPrefix(new_log, broadcast);
        SendLogReflectsBroadcastPrefix(netEventLog + [netEvent], broadcast);
    }
    
}
*/


/*
method SendBroadcast(netClient:NetClient, broadcast:CBroadcast, ghost localAddr_:EndPoint) returns (ok:bool, ghost netEventLog:seq<NetEvent>)
    requires NetClientIsValid(netClient);
    requires CBroadcastIsValid(broadcast);
    requires netClient.LocalEndPoint() == localAddr_;
    requires broadcast.CBroadcast? ==> broadcast.src == localAddr_;
    modifies NetClientRepr(netClient);
    ensures old(NetClientRepr(netClient)) == NetClientRepr(netClient);
    ensures netClient.env == old(netClient.env);
    ensures netClient.LocalEndPoint() == old(netClient.LocalEndPoint());
    ensures NetClientOk(netClient) <==> ok;
    ensures ok ==> (
           NetClientIsValid(netClient)
        && netClient.IsOpen()
        && old(netClient.env.net.history()) + netEventLog == netClient.env.net.history()
        && SendLogReflectsBroadcast(netEventLog, broadcast));
{
    ok := true;
    netEventLog := [];

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
            invariant |netEventLog| == i as int;
            invariant NetClientRepr(netClient) == old(NetClientRepr(netClient));
            invariant netClient.env == old(netClient.env);
            invariant netClient.LocalEndPoint() == old(netClient.LocalEndPoint());
            invariant NetClientIsValid(netClient);
            invariant NetClientOk(netClient);
            invariant old(netClient.env.net.history()) + netEventLog == netClient.env.net.history();
            invariant PaxosDemarshallable(buffer[..]);
            invariant BufferRefinementAgreesWithMessageRefinement(broadcast.msg, buffer[..]);
            invariant SendLogReflectsBroadcastPrefix(netEventLog, broadcast);
            invariant CMessageIsAbstractable(PaxosDemarshallData(buffer[..]));
        {
            ghost var netEventLog_old := netEventLog;

            // Construct the remote address -- TODO: Only do this once per replica!
            var dstEp:EndPoint := broadcast.dsts[i];
            var dstAddrAry := seqToArrayOpt(dstEp.addr);
            var remote;
            ok, remote := IPEndPoint.Construct(dstAddrAry, dstEp.port, netClient.env);
            if (!ok) { return; }

            ok := netClient.Send(remote, buffer);
            if (!ok) { return; }

            ghost var netEvent := NetSendEvent(NetPacket_ctor(remote.EP(), netClient.LocalEndPoint(), buffer[..]));
            netEventLog := netEventLog + [netEvent];

            lemma_NetEventLogAppend(broadcast, netEventLog_old, netEvent);

            i := i + 1;
        }
    }

}
*/


method SendPacketSeq(netClient:NetClient, cpackets:seq<CPacket>, ghost localAddr_:EndPoint) returns (ok:bool, ghost netEventLog:seq<NetEvent>)
    requires NetClientIsValid(netClient);
    requires OutboundPacketsSeqIsValid(cpackets);
    requires netClient.LocalEndPoint() == localAddr_;
    requires OutboundPacketsSeqHasCorrectSrc(cpackets, localAddr_);
    modifies NetClientRepr(netClient);
    ensures old(NetClientRepr(netClient)) == NetClientRepr(netClient);
    ensures netClient.env == old(netClient.env);
    ensures netClient.LocalEndPoint() == old(netClient.LocalEndPoint());
    ensures NetClientOk(netClient) <==> ok;
    ensures ok ==> ( NetClientIsValid(netClient) && netClient.IsOpen());
    ensures ok ==> old(netClient.env.net.history()) + netEventLog == netClient.env.net.history();
    ensures ok ==> SendLogReflectsPacket(netEventLog, cpackets) && OnlySentMarshallableData(netEventLog);
{
    var j:uint64 := 0;
    netEventLog := [];
    ok := true;
    
    ghost var netEventLog_old := netEventLog;
    ghost var netClientEnvHistory_old := old(netClient.env.net.history());
    var i := 0;

    while (i < |cpackets|)
        invariant old(NetClientRepr(netClient)) == NetClientRepr(netClient);
        invariant netClient.env == old(netClient.env);
        invariant netClient.LocalEndPoint() == old(netClient.LocalEndPoint());
        invariant NetClientOk(netClient) <==> ok;
        invariant ok ==> ( NetClientIsValid(netClient) && netClient.IsOpen());
        invariant ok ==> netClientEnvHistory_old + netEventLog == netClient.env.net.history();
        invariant ok ==> OnlySentMarshallableData(netEventLog);
        invariant (i == 0) ==> |netEventLog| == 0;
        invariant (0 < i < |cpackets|) ==> |netEventLog| == |cpackets[0..i]|;
        invariant (0 < i < |cpackets|) ==> SendLogReflectsPacket(netEventLog, cpackets[0..i]); 
        invariant (i >= |cpackets|) ==> SendLogReflectsPacket(netEventLog, cpackets); 
        
    {
        var cpacket := cpackets[i];
        // Construct the remote address
        var dstEp:EndPoint := cpacket.dst;
        assert cpacket in cpackets;
        assert OutboundPacketsIsValid(cpacket);


        var dstAddrAry := seqToArrayOpt(dstEp.addr);
        var remote;
        ok, remote := IPEndPoint.Construct(dstAddrAry, dstEp.port, netClient.env);
        if (!ok) { return; }

        assert CSingleMessageIsAbstractable(cpacket.msg);
         
        assert CSingleMessageMarshallable(cpacket.msg);
        var buffer := SHTMarshall(cpacket.msg);

        ghost var data := buffer[..];
        assert BufferRefinementAgreesWithMessageRefinement(cpacket.msg, data);

        ok := netClient.Send(remote, buffer);
        if (!ok) { return; }

        ghost var netEvent := LIoOpSend(LPacket(remote.EP(), netClient.LocalEndPoint(), buffer[..]));
        ghost var net := netEvent.s;

        calc {
            AbstractifyCPacketToLSHTPacket(cpacket);
            LPacket(AbstractifyEndPointToNodeIdentity(cpacket.dst), AbstractifyEndPointToNodeIdentity(cpacket.src), AbstractifyCSingleMessageToSingleMessage(cpacket.msg));
            LPacket(AbstractifyEndPointToNodeIdentity(net.dst), AbstractifyEndPointToNodeIdentity(net.src), AbstractifyCSingleMessageToSingleMessage(cpacket.msg));
            AbstractifyBufferToLSHTPacket(net.src, net.dst, data);
            AbstractifyBufferToLSHTPacket(net.src, net.dst, net.msg);
            AbstractifyNetPacketToLSHTPacket(netEvent.s);
        }
        
        assert SendLogEntryReflectsPacket(netEvent, cpacket);
        assert OnlySentMarshallableData(netEventLog);
        assert NetPacketBound(netEvent.s.msg) && CSingleMessageMarshallable(SHTDemarshallData(netEvent.s.msg));
        netEventLog := netEventLog + [netEvent];
        assert cpackets[0..(i+1)] == cpackets[0..i] + [cpacket];
        assert SendLogReflectsPacket(netEventLog, cpackets[0..(i+1)]);
        assert OnlySentMarshallableData(netEventLog);
        i := i + 1;
    }
}
} 
