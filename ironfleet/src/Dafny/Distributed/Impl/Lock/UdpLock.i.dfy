include "../Common/UdpClient.i.dfy"
include "PacketParsing.i.dfy"

module UdpLock_i {
import opened Common__UdpClient_i
import opened PacketParsing_i 

//////////////////////////////////////////////////////////////////////////////
// These functions relate IO events with bytes to those with LockMessages
// 

function AstractifyUdpEventToLockIo(evt:UdpEvent) : LockIo
{
    match evt
        case LIoOpSend(s) => LIoOpSend(AbstractifyUdpPacket(s))
        case LIoOpReceive(r) => LIoOpReceive(AbstractifyUdpPacket(r))
        case LIoOpTimeoutReceive => LIoOpTimeoutReceive()
        case LIoOpReadClock(t) => LIoOpReadClock(int(t))
}

function {:opaque} AbstractifyRawLogToIos(rawlog:seq<UdpEvent>) : seq<LockIo>
    ensures |AbstractifyRawLogToIos(rawlog)| == |rawlog|;
    ensures forall i {:trigger AstractifyUdpEventToLockIo(rawlog[i])} 
                     {:trigger AbstractifyRawLogToIos(rawlog)[i]} :: 
                0 <= i < |rawlog| ==> AbstractifyRawLogToIos(rawlog)[i] == AstractifyUdpEventToLockIo(rawlog[i]);
{
    if (rawlog==[]) then [] else [AstractifyUdpEventToLockIo(rawlog[0])] + AbstractifyRawLogToIos(rawlog[1..])
}

lemma lemma_EstablishAbstractifyRawLogToIos(rawlog:seq<UdpEvent>, ios:seq<LockIo>)
    requires |rawlog| == |ios|;
    requires forall i :: 0<=i<|rawlog| ==> ios[i] == AstractifyUdpEventToLockIo(rawlog[i]);
    ensures AbstractifyRawLogToIos(rawlog) == ios;
{
    reveal_AbstractifyRawLogToIos();
}

predicate OnlySentMarshallableData(rawlog:seq<UdpEvent>)
{
    forall io :: io in rawlog && io.LIoOpSend? ==> UdpPacketBound(io.s.msg)
}

//////////////////////////////////////////////////////////////////////////////
// These methods wrap the raw UdpClient interface
//

datatype ReceiveResult = RRFail() | RRTimeout() | RRPacket(cpacket:CLockPacket)

method GetEndPoint(ipe:IPEndPoint) returns (ep:EndPoint)
    requires ipe!=null;
    ensures ep == ipe.EP();
    ensures EndPointIsValidIPV4(ep);
{
    var addr := ipe.GetAddress();
    var port := ipe.GetPort();
    ep := EndPoint(addr[..], port);
}

method Receive(udpClient:UdpClient, localAddr:EndPoint) 
    returns (rr:ReceiveResult, ghost udpEvent:UdpEvent)
    requires UdpClientIsValid(udpClient);
    requires udpClient.LocalEndPoint() == localAddr;
    modifies UdpClientRepr(udpClient);
    ensures udpClient.env == old(udpClient.env);
    ensures udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint());
    ensures UdpClientOk(udpClient) <==> !rr.RRFail?;
    ensures old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient);
    ensures !rr.RRFail? ==>
           udpClient.IsOpen()
        && old(udpClient.env.udp.history()) + [udpEvent] == udpClient.env.udp.history();
    ensures rr.RRTimeout? ==> udpEvent.LIoOpTimeoutReceive?;
    ensures rr.RRPacket? ==>
           udpEvent.LIoOpReceive?
        && EndPointIsValidIPV4(rr.cpacket.src)
        && AbstractifyCLockPacket(rr.cpacket) == AbstractifyUdpPacket(udpEvent.r)
        && rr.cpacket.msg == DemarshallData(udpEvent.r.msg)
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

    var cmessage := DemarshallDataMethod(buffer);
    var srcEp := GetEndPoint(remote);
    var cpacket := LPacket(localAddr, srcEp, cmessage);
    rr := RRPacket(cpacket);
}

predicate SendLogEntryReflectsPacket(event:UdpEvent, cpacket:CLockPacket)
{
       event.LIoOpSend?
    && AbstractifyCLockPacket(cpacket) == AbstractifyUdpPacket(event.s)
}

predicate SendLogReflectsPacket(udpEventLog:seq<UdpEvent>, packet:Option<CLockPacket>)
{
    match packet {
        case Some(p) => |udpEventLog| == 1 && SendLogEntryReflectsPacket(udpEventLog[0], p)
        case None => udpEventLog == []
    }
}

method SendPacket(udpClient:UdpClient, opt_packet:Option<CLockPacket>, ghost localAddr:EndPoint) returns (ok:bool, ghost udpEventLog:seq<UdpEvent>)
    requires UdpClientIsValid(udpClient);
    requires udpClient.LocalEndPoint() == localAddr;
    requires OptionCLockPacketValid(opt_packet);
    requires opt_packet.Some? ==> opt_packet.v.src == localAddr;
    modifies UdpClientRepr(udpClient);
    ensures old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient);
    ensures udpClient.env == old(udpClient.env);
    ensures udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint());
    ensures UdpClientOk(udpClient) <==> ok;
    ensures ok ==> ( UdpClientIsValid(udpClient)
                  && udpClient.IsOpen()
                  && old(udpClient.env.udp.history()) + udpEventLog == udpClient.env.udp.history()
                  && OnlySentMarshallableData(udpEventLog)
                  && SendLogReflectsPacket(udpEventLog, opt_packet));
{
    udpEventLog := [];
    ok := true;

    if opt_packet.None? {

    } else {
        var cpacket := opt_packet.v;

        // Construct the remote address
        var dstEp:EndPoint := cpacket.dst;
        var dstAddrAry := seqToArrayOpt(dstEp.addr);
        var remote;
        ok, remote := IPEndPoint.Construct(dstAddrAry, dstEp.port, udpClient.env);
        if (!ok) { return; }

        // Marshall the message
        var buffer := MarshallLockMessage(cpacket.msg);

        // Send the packet off
        ok := udpClient.Send(remote, buffer);
        if (!ok) { return; }

        ghost var udpEvent := LIoOpSend(LPacket(remote.EP(), udpClient.LocalEndPoint(), buffer[..]));
        udpEventLog := [udpEvent];
    }
}


} 
