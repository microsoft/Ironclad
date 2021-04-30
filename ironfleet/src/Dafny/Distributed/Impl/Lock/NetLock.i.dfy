include "../Common/NetClient.i.dfy"
include "PacketParsing.i.dfy"

module NetLock_i {
import opened Native__Io_s
import opened Logic__Option_i
import opened Environment_s
import opened Types_i
import opened Message_i
import opened Common__Util_i
import opened Common__NetClient_i
import opened Common__GenericMarshalling_i
import opened PacketParsing_i 

//////////////////////////////////////////////////////////////////////////////
// These functions relate IO events with bytes to those with LockMessages
// 

function AstractifyNetEventToLockIo(evt:NetEvent) : LockIo
{
    match evt
        case LIoOpSend(s) => LIoOpSend(AbstractifyNetPacket(s))
        case LIoOpReceive(r) => LIoOpReceive(AbstractifyNetPacket(r))
        case LIoOpTimeoutReceive => LIoOpTimeoutReceive()
        case LIoOpReadClock(t) => LIoOpReadClock(t as int)
}

function {:opaque} AbstractifyRawLogToIos(rawlog:seq<NetEvent>) : seq<LockIo>
    ensures |AbstractifyRawLogToIos(rawlog)| == |rawlog|;
    ensures forall i {:trigger AstractifyNetEventToLockIo(rawlog[i])} 
                     {:trigger AbstractifyRawLogToIos(rawlog)[i]} :: 
                0 <= i < |rawlog| ==> AbstractifyRawLogToIos(rawlog)[i] == AstractifyNetEventToLockIo(rawlog[i]);
{
    if (rawlog==[]) then [] else [AstractifyNetEventToLockIo(rawlog[0])] + AbstractifyRawLogToIos(rawlog[1..])
}

lemma lemma_EstablishAbstractifyRawLogToIos(rawlog:seq<NetEvent>, ios:seq<LockIo>)
    requires |rawlog| == |ios|;
    requires forall i :: 0<=i<|rawlog| ==> ios[i] == AstractifyNetEventToLockIo(rawlog[i]);
    ensures AbstractifyRawLogToIos(rawlog) == ios;
{
    reveal_AbstractifyRawLogToIos();
}

predicate OnlySentMarshallableData(rawlog:seq<NetEvent>)
{
    forall io :: io in rawlog && io.LIoOpSend? ==> 
        NetPacketBound(io.s.msg) && Demarshallable(io.s.msg, CMessageGrammar())
}

//////////////////////////////////////////////////////////////////////////////
// These methods wrap the raw NetClient interface
//

datatype ReceiveResult = RRFail() | RRTimeout() | RRPacket(cpacket:CLockPacket)

method GetEndPoint(ipe:IPEndPoint) returns (ep:EndPoint)
    ensures ep == ipe.EP();
    ensures EndPointIsValidIPV4(ep);
{
    var addr := ipe.GetAddress();
    var port := ipe.GetPort();
    ep := EndPoint(addr[..], port);
}

method Receive(netClient:NetClient, localAddr:EndPoint) 
    returns (rr:ReceiveResult, ghost netEvent:NetEvent)
    requires NetClientIsValid(netClient);
    requires netClient.LocalEndPoint() == localAddr;
    modifies NetClientRepr(netClient);
    ensures netClient.env == old(netClient.env);
    ensures netClient.LocalEndPoint() == old(netClient.LocalEndPoint());
    ensures NetClientOk(netClient) <==> !rr.RRFail?;
    ensures old(NetClientRepr(netClient)) == NetClientRepr(netClient);
    ensures !rr.RRFail? ==>
           netClient.IsOpen()
        && old(netClient.env.net.history()) + [netEvent] == netClient.env.net.history();
    ensures rr.RRTimeout? ==> netEvent.LIoOpTimeoutReceive?;
    ensures rr.RRPacket? ==>
           netEvent.LIoOpReceive?
        && EndPointIsValidIPV4(rr.cpacket.src)
        && AbstractifyCLockPacket(rr.cpacket) == AbstractifyNetPacket(netEvent.r)
        && rr.cpacket.msg == DemarshallData(netEvent.r.msg)
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

    var cmessage := DemarshallDataMethod(buffer);
    var srcEp := GetEndPoint(remote);
    var cpacket := LPacket(localAddr, srcEp, cmessage);
    rr := RRPacket(cpacket);
}

predicate SendLogEntryReflectsPacket(event:NetEvent, cpacket:CLockPacket)
{
       event.LIoOpSend?
    && AbstractifyCLockPacket(cpacket) == AbstractifyNetPacket(event.s)
}

predicate SendLogReflectsPacket(netEventLog:seq<NetEvent>, packet:Option<CLockPacket>)
{
    match packet {
        case Some(p) => |netEventLog| == 1 && SendLogEntryReflectsPacket(netEventLog[0], p)
        case None => netEventLog == []
    }
}

method SendPacket(netClient:NetClient, opt_packet:Option<CLockPacket>, ghost localAddr:EndPoint) returns (ok:bool, ghost netEventLog:seq<NetEvent>)
    requires NetClientIsValid(netClient);
    requires netClient.LocalEndPoint() == localAddr;
    requires OptionCLockPacketValid(opt_packet);
    requires opt_packet.Some? ==> opt_packet.v.src == localAddr;
    modifies NetClientRepr(netClient);
    ensures old(NetClientRepr(netClient)) == NetClientRepr(netClient);
    ensures netClient.env == old(netClient.env);
    ensures netClient.LocalEndPoint() == old(netClient.LocalEndPoint());
    ensures NetClientOk(netClient) <==> ok;
    ensures ok ==> ( NetClientIsValid(netClient)
                  && netClient.IsOpen()
                  && old(netClient.env.net.history()) + netEventLog == netClient.env.net.history()
                  && OnlySentMarshallableData(netEventLog)
                  && SendLogReflectsPacket(netEventLog, opt_packet));
{
    netEventLog := [];
    ok := true;

    if opt_packet.None? {

    } else {
        var cpacket := opt_packet.v;

        // Construct the remote address
        var dstEp:EndPoint := cpacket.dst;
        var dstAddrAry := seqToArrayOpt(dstEp.addr);
        var remote;
        ok, remote := IPEndPoint.Construct(dstAddrAry, dstEp.port, netClient.env);
        if (!ok) { return; }

        // Marshall the message
        var buffer := MarshallLockMessage(cpacket.msg);

        // Send the packet off
        ok := netClient.Send(remote, buffer);
        if (!ok) { return; }

        ghost var netEvent := LIoOpSend(LPacket(remote.EP(), netClient.LocalEndPoint(), buffer[..]));
        netEventLog := [netEvent];
    }
}


} 
