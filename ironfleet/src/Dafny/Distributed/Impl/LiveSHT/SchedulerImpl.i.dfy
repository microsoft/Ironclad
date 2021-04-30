include "../SHT/HostModel.i.dfy"
include "../../Protocol/LiveSHT/Scheduler.i.dfy"
include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/SHT/Host.i.dfy"
include "NetSHT.i.dfy"
include "SchedulerModel.i.dfy"
include "Unsendable.i.dfy"
//include "CBoundedClock.i.dfy"

module LiveSHT__SchedulerImpl_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened Logic__Option_i
import opened Math__mod_auto_i
import opened Collections__Seqs_i
import opened Environment_s
import opened SHT__Host_i
import opened SHT__HostModel_i
import opened SHT__HostState_i
import opened SHT__CMessage_i
import opened SHT__ConstantsState_i
import opened SHT__Network_i
import opened SHT__PacketParsing_i
import opened SHT__SingleDeliveryState_i
import opened SHT__SingleDelivery_i
import opened Impl_Parameters_i
import opened LiveSHT__Scheduler_i
import opened LiveSHT__NetSHT_i
import opened LiveSHT__SchedulerModel_i
import opened LiveSHT__Unsendable_i
import opened LiveSHT__Environment_i
import opened Common__NetClient_i
import opened Common__NodeIdentity_i 
import opened Common__Util_i

class SchedulerImpl
{
    var host:HostState;
    var nextActionIndex:uint64;
    var resendCount:uint64;
    var netClient:NetClient?;
    var localAddr:EndPoint;

    ghost var Repr : set<object>;

    constructor()
    {
    }

    predicate Valid()
        reads this;
        reads NetClientIsValid.reads(netClient);
    {
           HostStateIsValid(host)
        && HostStateIsAbstractable(host)
        && (0 <= nextActionIndex as int < LHost_NumActions())
        && (0 <= resendCount as int < 100000000)
        && NetClientIsValid(netClient)
        && netClient.LocalEndPoint() == localAddr
        && netClient.LocalEndPoint() == host.me
        && HostStateIsValid(host)
        && Repr == { this } + NetClientRepr(netClient)
        && CSingleDeliveryAccountIsValid(host.sd, host.constants.params)
    }
        
    function Env() : HostEnvironment?
        reads this, NetClientIsValid.reads(netClient);
    {
        if netClient!=null then netClient.env else null
    }
   
    function AbstractifyToHost() : Host
        reads this;
        requires HostStateIsAbstractable(host);
    {
        AbstractifyHostStateToHost(host)
    }

    function AbstractifyToLScheduler() : LScheduler
        reads this;
        requires HostStateIsAbstractable(host);
    {
        LScheduler(
            AbstractifyToHost(),
            nextActionIndex as int,
            resendCount as int)
    }
      
    method ConstructNetClient(constants:ConstantsState, me:EndPoint, ghost env_:HostEnvironment) returns (ok:bool, client:NetClient?)
        requires env_.Valid() && env_.ok.ok();
        requires ConstantsStateIsValid(constants);
        requires EndPointIsAbstractable(me);
        modifies env_.ok;
        ensures ok ==> NetClientIsValid(client)
                    && client.LocalEndPoint() == me
                    && client.env == env_;
    {
        var my_ep := me;
        var ip_byte_array := new byte[|my_ep.addr|];
        assert EndPointIsValidIPV4(my_ep);
        seqIntoArrayOpt(my_ep.addr, ip_byte_array);
        var ip_endpoint;
        ok, ip_endpoint := IPEndPoint.Construct(ip_byte_array, my_ep.port, env_);
        if !ok { return; }
        ok, client := NetClient.Construct(ip_endpoint, env_);
        if ok {
            calc {
                client.LocalEndPoint();
                ip_endpoint.EP();
                my_ep;
            }
        }
    }

    
    method {:timeLimitMultiplier 2} Host_Init_Impl(constants:ConstantsState, me:EndPoint, ghost env_:HostEnvironment) returns (ok:bool)
        requires env_.Valid() && env_.ok.ok();
        requires ConstantsStateIsValid(constants);
        requires EndPointIsAbstractable(me);
        modifies this, netClient;
        modifies env_.ok;
        ensures ok ==>
               Valid()
            && Env() == env_
            && LScheduler_Init(AbstractifyToLScheduler(), AbstractifyEndPointToNodeIdentity(me), AbstractifyEndPointToNodeIdentity(constants.rootIdentity), AbstractifyEndPointsToNodeIdentities(constants.hostIds), AbstractifyCParametersToParameters(constants.params))
            && host.constants == constants;
    {
        ok, netClient := ConstructNetClient(constants, me, env_); 

        if (ok)
        {
            
            host := InitHostState(constants, me);
            nextActionIndex := 0;
            resendCount := 0;
            localAddr := host.me;
            Repr := { this } + NetClientRepr(netClient);
            
        }
    }

    static method rollActionIndex(a:uint64) returns (a':uint64)
        requires 0 <= a as int < 3;
        ensures a' as int == (a as int + 1) % LHost_NumActions();
    {
        lemma_mod_auto(3);
        if (a >= 2) {
            a' := 0;
        } else {
            a' := (a + 1);
        }
    }

    static method rollResendCount(a:uint64) returns (a':uint64)
        requires 0 <= a as int < 100000000;
        ensures a' as int == (a as int + 1) % 100000000;
    {
        lemma_mod_auto(100000000);
        if (a >= 100000000-1) {
            a' := 0;
        } else {
            a' := (a + 1);
        }
    }
    
    static lemma lemma_ExtractSentPacketsFromIos(ios:seq<LSHTIo>)
        requires AllIosAreSends(ios);
        ensures  |ExtractSentPacketsFromIos(ios)| == |ios|;
        ensures  forall i {:auto_trigger} :: 0 <= i < |ios| ==> ExtractSentPacketsFromIos(ios)[i] == ios[i].s;
    {
        reveal_ExtractSentPacketsFromIos();
    }


    method DeliverPacketSeq(packets:seq<CPacket>) returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<LSHTIo>)
        requires Valid();
        requires OutboundPacketsSeqIsValid(packets);
        requires OutboundPacketsSeqHasCorrectSrc(packets, host.me);
        modifies Repr;
        ensures Repr == old(Repr);
        ensures Env() == old(Env());
        ensures ok == NetClientOk(netClient);
        ensures ok ==> (
               Valid()
            && host == old(host)
            && nextActionIndex == old(nextActionIndex)
            && resendCount == old(resendCount)
            && AllIosAreSends(ios)
            && AbstractifyOutboundPacketsToSeqOfLSHTPackets(packets) == ExtractSentPacketsFromIos(ios)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && old(Env().net.history()) + netEventLog == Env().net.history());
    {
        var start_time := Time.GetDebugTimeTicks();
        ok, netEventLog := SendPacketSeq(netClient, packets, localAddr);
        if (!ok) { return; }

        ios := MapSentPacketSeqToIos(packets);
        MapSentPacketSeqToIos_ExtractSentPacketsFromIos_equivalence(packets, ios);
        var end_time := Time.GetDebugTimeTicks();
        RecordTimingSeq("DeliverPacketSeq", start_time, end_time);
        
    }

    method DeliverOutboundPackets(packets:seq<CPacket>) returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<LSHTIo>)
        requires Valid();
        requires OutboundPacketsSeqIsValid(packets);
        requires OutboundPacketsSeqHasCorrectSrc(packets, host.me); 
        modifies Repr;
        ensures Repr == old(Repr);
        ensures Env() == old(Env());
        ensures ok == NetClientOk(netClient);
        ensures ok ==> (
               Valid()
            && host == old(host)
            && nextActionIndex == old(nextActionIndex)
            && resendCount == old(resendCount)
            && AllIosAreSends(ios)
            && AbstractifyOutboundPacketsToSeqOfLSHTPackets(packets) == ExtractSentPacketsFromIos(ios)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && old(Env().net.history()) + netEventLog == Env().net.history());
    {
        ok, netEventLog, ios := DeliverPacketSeq(packets);
    }


    predicate ReceivedPacketProperties(cpacket:CPacket, netEvent0:NetEvent, io0:LSHTIo)
        reads this;
        //requires SHTConcreteConfigurationIsValid(host.constants.all.config);
    {
           CPacketIsSendable(cpacket)
        && EndPointIsValidIPV4(host.me)
        && io0.LIoOpReceive?
        && NetEventIsAbstractable(netEvent0)
        && io0 == AbstractifyNetEventToLSHTIo(netEvent0)
        && NetEventIsAbstractable(netEvent0)
        && netEvent0.LIoOpReceive? && AbstractifyCPacketToShtPacket(cpacket) == AbstractifyNetPacketToShtPacket(netEvent0.r)
    }

    static lemma ExtractSentPacketsFromIos_DoesNotMindSomeClutter(ios_head:seq<LSHTIo>, ios_tail:seq<LSHTIo>)
        requires forall i :: 0<=i<|ios_head| ==> !ios_head[i].LIoOpSend?;
        ensures ExtractSentPacketsFromIos(ios_tail) == ExtractSentPacketsFromIos(ios_head + ios_tail);
    {
        if |ios_head| == 0 {
            assert ios_head + ios_tail == ios_tail;
        } else {
            assert !ios_head[0].LIoOpSend?;
            ghost var ios := [ios_head[0]] + ios_head[1..] + ios_tail;
            
            calc {
                ExtractSentPacketsFromIos(ios_head + ios_tail);
                    { assert ios_head == [ios_head[0]] + ios_head[1..]; }
                ExtractSentPacketsFromIos([ios_head[0]] + ios_head[1..] + ios_tail);
                ExtractSentPacketsFromIos(ios);
                    { assert ios[0] == ios_head[0]; assert ios[1..] == ios_head[1..] + ios_tail;
                      reveal_ExtractSentPacketsFromIos(); 
                    }
                ExtractSentPacketsFromIos(ios_head[1..] + ios_tail);
                    { ExtractSentPacketsFromIos_DoesNotMindSomeClutter(ios_head[1..], ios_tail); }
                ExtractSentPacketsFromIos(ios_tail);
            }
        }
    }

    method Host_NoReceive_NoClock_Next() returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<LSHTIo>)
        requires nextActionIndex == 2;
        requires Valid();
        modifies Repr;
        ensures Repr == old(Repr);
        ensures Env() == old(Env());
        ensures ok == NetClientOk(netClient);
        ensures ok ==> (
               Valid()
            && nextActionIndex == old(nextActionIndex)
            && resendCount == old(resendCount)
            && LHost_NoReceive_Next(old(AbstractifyToHost()), AbstractifyToHost(), ios)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog) 
            && LIoOpSeqCompatibleWithReduction(ios)
            && old(Env().net.history()) + netEventLog == Env().net.history());
    {
    
        var sent_packets;
        
        host,sent_packets := HostModelSpontaneouslyRetransmit(host);
        
        ok, netEventLog, ios := DeliverOutboundPackets(sent_packets);
        if (!ok) { return; }
        assert old(Env().net.history()) + netEventLog == Env().net.history(); // deleteme

        // The following loop takes the forall that's stated in terms of io indices and turns
        // it into a forall in terms of ios.  In other words, it takes
        // forall idx {:trigger 0 <= idx < |ios|} :: 0 <= idx < |ios| ==> ios[idx].LIoOpSend?
        // and turns it into
        // forall io {:trigger io in ios} :: io in ios ==> io.LIoOpSend?
        forall io | io in ios
            ensures io.LIoOpSend?;
        {
            var pos :| 0 <= pos < |ios| && io == ios[pos];
            assert ios[pos].LIoOpSend?;
        }

        assert AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
        assert Env() == old(Env());
        assert RawIoConsistentWithSpecIO(netEventLog, ios);
        reveal_AbstractifyOutboundPacketsToSeqOfLSHTPackets();

        assert ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ios)) == UnAckedMessages(AbstractifyToHost().sd, AbstractifyToHost().me);
        assert SpontaneouslyRetransmit(old(AbstractifyToHost()), AbstractifyToHost(), ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ios)));
        assert LHost_NoReceive_Next(old(AbstractifyToHost()), AbstractifyToHost(), ios);
    }

    
    static lemma SingletonSeqPrependSilly<T>(log_head:seq<T>, log_tail:seq<T>, log:seq<T>)
        requires |log_head|==1;
        requires log == log_head + log_tail;
        ensures log_tail == log[1..];
    {
    }
    
     static lemma Combine_AbstractifyNetEventToLSHTIo(ios_head:seq<LSHTIo>, ios_tail:seq<LSHTIo>, ios:seq<LSHTIo>, log_head:seq<NetEvent>, log_tail:seq<NetEvent>, log:seq<NetEvent>)
        requires |log_head| == |ios_head|;
        requires forall i :: 0<=i<|log_head|
            ==> NetEventIsAbstractable(log_head[i]) && ios_head[i] == AbstractifyNetEventToLSHTIo(log_head[i]);
        requires |log_tail| == |ios_tail|;
        requires forall i :: 0<=i<|log_tail|
            ==> NetEventIsAbstractable(log_tail[i]) && ios_tail[i] == AbstractifyNetEventToLSHTIo(log_tail[i]);
        requires ios == ios_head+ios_tail;
        requires log == log_head+log_tail;
        ensures forall i :: 0<=i<|log| ==> ios[i] == AbstractifyNetEventToLSHTIo(log[i]);
    {
    }

    static lemma NetEventLogIsAbstractable_Extend(log_head:seq<NetEvent>, log_tail:seq<NetEvent>, log:seq<NetEvent>)
        requires log == log_head+log_tail;
        requires NetEventLogIsAbstractable(log_head);
        requires NetEventLogIsAbstractable(log_tail);
        ensures NetEventLogIsAbstractable(log);
    {
    }

    static lemma EstablishCombineIos(ios_head:seq<LSHTIo>, ios_tail:seq<LSHTIo>, ios:seq<LSHTIo>)
        requires ios == ios_head+ios_tail;
        requires |ios_head| == 1;
        requires forall i :: 0<=i<|ios_tail| ==> ios_tail[i].LIoOpSend?;
        ensures forall io :: io in ios[1..] ==> io.LIoOpSend?;
    {
    }

    static lemma SingletonSeqSilly(packets:seq<CPacket>, p:CPacket)
        requires packets == [p];
        requires |packets| == 1;
        ensures forall p' :: p' in packets ==> p' == p
    {
    }
    
    method{:timeLimitMultiplier 8} HostNextReceivePacket(ghost netEventLogOld:seq<NetEvent>, rr:ReceiveResult, ghost receive_event:NetEvent) returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<LSHTIo>)
        requires nextActionIndex == 0;
        requires Valid();
        requires Env().net.history() == netEventLogOld + [receive_event];
        requires rr.RRPacket?;
        requires receive_event.LIoOpReceive?;
        requires CPacketIsAbstractable(rr.cpacket);
        requires NetPacketIsAbstractable(receive_event.r);
        //requires CSingleMessageMarshallable(rr.cpacket.msg);
        requires !rr.cpacket.msg.CInvalidMessage? && CSingleMessageIs64Bit(rr.cpacket.msg);
        requires AbstractifyCPacketToLSHTPacket(rr.cpacket) == AbstractifyNetPacketToLSHTPacket(receive_event.r);
        //requires CPacketIsSendable(rr.cpacket);
        requires rr.cpacket.dst == host.me;
        modifies Repr;
        ensures Repr == old(Repr);
        ensures ok == NetClientOk(netClient);
        ensures Env() == old(Env());
        ensures ok ==> (
               Valid()
            && nextActionIndex == old(nextActionIndex)
            && resendCount == old(resendCount)
            && LHost_ReceivePacket_Next(old(AbstractifyToHost()), AbstractifyToHost(), ios)
            && OnlySentMarshallableData(netEventLog) 
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && LIoOpSeqCompatibleWithReduction(ios)
            && netEventLogOld + netEventLog == Env().net.history());
    {
        var cpacket := rr.cpacket;
        var sent_packets, ack;
        host, sent_packets, ack := HostModelReceivePacket(host, cpacket); 
        assert Valid();
        assert ReceivePacket(old(AbstractifyToHost()), AbstractifyToHost(), AbstractifyCPacketToShtPacket(cpacket), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets), AbstractifyCPacketToShtPacket(ack));

        ghost var io0 := LIoOpReceive(AbstractifyNetPacketToLSHTPacket(receive_event.r));
        ghost var log_head, log_tail, ios_head, ios_tail;

        ios_head := [io0];
        log_head := [receive_event];
        ghost var preDeliveryHistory := Env().net.history();

        assert Env() == old(Env());
        assert Valid();
        assert netClient.LocalEndPoint() == host.me;
        ok, log_tail, ios_tail := DeliverOutboundPackets(sent_packets);
        if (!ok) { return; }
        
        ios := ios_head + ios_tail;
        netEventLog := log_head + log_tail;

        calc {
            netEventLogOld + netEventLog;
            netEventLogOld + (log_head + log_tail);
                { SeqAdditionIsAssociative(netEventLogOld, log_head, log_tail); }
            (netEventLogOld + log_head) + log_tail;
            preDeliveryHistory + log_tail;
                { SingletonSeqPrependSilly(log_head, log_tail, netEventLog); }
            preDeliveryHistory + netEventLog[1..];
            preDeliveryHistory + log_tail;
            Env().net.history();
        }

        reveal_AbstractifyOutboundPacketsToSeqOfLSHTPackets();

        assert Env() == old(Env());

        assert io0 == AbstractifyNetEventToLSHTIo(receive_event);
        forall i | 0<=i<|log_head| ensures NetEventIsAbstractable(log_head[i]) && ios_head[i] == AbstractifyNetEventToLSHTIo(log_head[i]);
        {
            assert log_head[i] == receive_event;
            assert ios_head[i] == io0;
        }

        ExtractSentPacketsFromIos_DoesNotMindSomeClutter(ios_head, ios_tail);
        assert ios_tail == ios[1..];
        assert AllIosAreSends(ios_tail);
        assert forall i{:trigger ios_tail[i].LIoOpSend?} :: 0<=i<|ios_tail| ==> ios_tail[i].LIoOpSend?;
        Combine_AbstractifyNetEventToLSHTIo(ios_head, ios_tail, ios, log_head, log_tail, netEventLog);

        assert AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
        NetEventLogIsAbstractable_Extend(log_head, log_tail, netEventLog);
        assert NetEventLogIsAbstractable(netEventLog);
        lemma_AbstractifyRawLogToIos_properties(netEventLog, ios);

        assert RawIoConsistentWithSpecIO(netEventLog, ios);
        ExtractSentPacketsFromIos_DoesNotMindSomeClutter(ios_head, ios_tail);  
        assert ios[0] == io0;
        assert AbstractifyCPacketToShtPacket(cpacket) == Packet(ios[0].r.dst, ios[0].r.src, ios[0].r.msg);
        assert AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets) == ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ios));
        assert ReceivePacket_Wrapper(old(AbstractifyToHost()), AbstractifyToHost(), AbstractifyCPacketToShtPacket(cpacket), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets));
        assert LHost_ReceivePacketWithoutReadingClock(old(AbstractifyToHost()), AbstractifyToHost(), ios);

        forall i | 1<=i<|ios|
            ensures ios[i].LIoOpSend?;
        {
            SingletonSeqPrependSilly2(ios_head, ios_tail, ios, i);   // Help stabilize the next line 
            assert ios[i] == ios_tail[i-1];
            var j := i-1;
            assert 0 <= j < |ios_tail|;
            assert ios_tail[j].LIoOpSend?;
        }
        assert LHost_ReceivePacket_Next(old(AbstractifyToHost()), AbstractifyToHost(), ios);
    }
    
    method Host_ReceivePacket_Next() returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<LSHTIo>)
        requires nextActionIndex == 0;
        requires Valid();
        modifies Repr;
        ensures Repr == old(Repr);
        ensures ok == NetClientOk(netClient);
        ensures Env() == old(Env());
        ensures ok ==> (
               Valid()
            && nextActionIndex == old(nextActionIndex)
            && resendCount == old(resendCount)
            && (   LHost_ReceivePacket_Next(old(AbstractifyToHost()), AbstractifyToHost(), ios)
                || (   IosReflectIgnoringUnDemarshallable(netEventLog)
                    && old(AbstractifyToHost()) == AbstractifyToHost()) )
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog) 
            && LIoOpSeqCompatibleWithReduction(ios)
            && old(Env().net.history()) + netEventLog == Env().net.history());
    {
        var start_time := Time.GetDebugTimeTicks();
        var rr;
        ghost var netEvent0;
       
        rr, netEvent0 := Receive(netClient, localAddr);
        ghost var midHistory := Env().net.history();
        assert Env()==old(Env());
        

        if (rr.RRFail?) {
            ok := false;
            var end_time := Time.GetDebugTimeTicks();
            RecordTimingSeq("Host_Next_ProcessPacket_fail", start_time, end_time);
            return;
        } else if (rr.RRTimeout?) {
            ok := true;
            ios := [ LIoOpTimeoutReceive() ];
            netEventLog := [ netEvent0 ];
            var end_time := Time.GetDebugTimeTicks();
            RecordTimingSeq("Host_Next_ProcessPacket_timeout", start_time, end_time);
            return;
        } else {
            ok := true;
            var cpacket := rr.cpacket;
            //assert Valid();
            //var marshallable := IsCSingleMessageMarshallable(cpacket.msg);
            //assert Valid();
            if cpacket.msg.CInvalidMessage? {
                ok := true;
                netEventLog := [netEvent0];
                ghost var receive_io := LIoOpReceive(AbstractifyNetPacketToLSHTPacket(netEvent0.r));
                ios := [receive_io];
            } else {
            //assert CPacketIsAbstractable(cpacket) && CSingleMessageMarshallable(cpacket.msg);
                ok, netEventLog, ios := HostNextReceivePacket(old(Env().net.history()), rr, netEvent0); 

               /* 
            host, sent_packets, ack := HostModelReceivePacket(host, cpacket); 
                assert Valid();
            assert ReceivePacket(old(AbstractifyToHost()), AbstractifyToHost(), AbstractifyCPacketToShtPacket(cpacket), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets), AbstractifyCPacketToShtPacket(ack));

            ghost var io0 := LIoOpReceive(AbstractifyNetPacketToLSHTPacket(netEvent0.r));
            ghost var log_head, log_tail, ios_head, ios_tail;

            ios_head := [io0];
            log_head := [netEvent0];
            ghost var preDeliveryHistory := Env().net.history();

            calc {
                old(Env().net.history()) + log_head;
                old(Env().net.history()) + [netEvent0];
                preDeliveryHistory;
            }
            assert Env() == old(Env());
                assert Valid();
            assert netClient.LocalEndPoint() == host.me;
            ok, log_tail, ios_tail := DeliverOutboundPackets(sent_packets);
            if (!ok) { return; }
            
            ios := ios_head + ios_tail;
            netEventLog := log_head + log_tail;

            calc {
                old(Env().net.history()) + netEventLog;
                old(Env().net.history()) + (log_head + log_tail);
                    { SeqAdditionIsAssociative(old(Env().net.history()), log_head, log_tail); }
                (old(Env().net.history()) + log_head) + log_tail;
                preDeliveryHistory + log_tail;
                    { SingletonSeqPrependSilly(log_head, log_tail, netEventLog); }
                preDeliveryHistory + netEventLog[1..];
                preDeliveryHistory + log_tail;
                Env().net.history();
            }

            reveal_AbstractifyOutboundPacketsToSeqOfLSHTPackets();

            assert Env() == old(Env());

            assert io0 == AbstractifyNetEventToLSHTIo(netEvent0);
            forall i | 0<=i<|log_head| ensures NetEventIsAbstractable(log_head[i]) && ios_head[i] == AbstractifyNetEventToLSHTIo(log_head[i]);
            {
                assert log_head[i] == netEvent0;
                assert ios_head[i] == io0;
            }

            ExtractSentPacketsFromIos_DoesNotMindSomeClutter(ios_head, ios_tail);
            assert ios_tail == ios[1..];
            assert AllIosAreSends(ios_tail);
            assert forall i{:trigger ios_tail[i].LIoOpSend?} :: 0<=i<|ios_tail| ==> ios_tail[i].LIoOpSend?;
            Combine_AbstractifyNetEventToLSHTIo(ios_head, ios_tail, ios, log_head, log_tail, netEventLog);

            assert AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
            NetEventLogIsAbstractable_Extend(log_head, log_tail, netEventLog);
            assert NetEventLogIsAbstractable(netEventLog);
            lemma_AbstractifyRawLogToIos_properties(netEventLog, ios);

            assert RawIoConsistentWithSpecIO(netEventLog, ios);
            ExtractSentPacketsFromIos_DoesNotMindSomeClutter(ios_head, ios_tail);  
//                assert LHost_ReceivePacketWithoutReadingClock(old(AbstractifyToHost()), AbstractifyToHost(), ios);

            forall i | 1<=i<|ios|
                ensures ios[i].LIoOpSend?;
            {
                SingletonSeqPrependSilly2(ios_head, ios_tail, ios, i);   // Help stabilize the next line 
                assert ios[i] == ios_tail[i-1];
                var j := i-1;
                assert 0 <= j < |ios_tail|;
                assert ios_tail[j].LIoOpSend?;
            }
            assert LHost_ReceivePacket_Next(old(AbstractifyToHost()), AbstractifyToHost(), ios);
                */
            }
        }
    }

    static lemma SingletonSeqPrependSilly2<T>(log_head:seq<T>, log_tail:seq<T>, log:seq<T>, index:int)
        requires |log_head|==1;
        requires log == log_head + log_tail;
        requires 1 <= index < |log|;
        ensures log_tail[index-1] == log[index];
    {
    }

    method{:timeLimitMultiplier 2} Host_ProcessReceivedPacket_Next() returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<LSHTIo>)
        requires nextActionIndex == 1;
        requires Valid();
        modifies Repr;
        ensures Repr == old(Repr);
        ensures Env() == old(Env());
        ensures ok == NetClientOk(netClient);
        ensures ok ==> (
               Valid()
            && nextActionIndex == old(nextActionIndex)
            && resendCount == old(resendCount)
            && (LHost_ProcessReceivedPacket_Next(old(AbstractifyToHost()), AbstractifyToHost(), ios)
                || HostNextIgnoreUnsendableProcess(old(AbstractifyToLScheduler()), AbstractifyToLScheduler().(nextActionIndex := 2), netEventLog))
            && old(AbstractifyToHost()).me == AbstractifyToHost().me
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog) 
            && LIoOpSeqCompatibleWithReduction(ios)
            && old(AbstractifyToLScheduler()).host.constants == AbstractifyToLScheduler().host.constants
            && old(Env().net.history()) + netEventLog == Env().net.history());
    {
        var sent_packets := [];
        var b;
        if (host.receivedPacket.Some?)
        {
        
            b := ShouldProcessReceivedMessageImpl(host);
            if (b) {
                var cpacket := host.receivedPacket.v;

                if (cpacket.msg.CSingleMessage?) {
                    assert |host.delegationMap.lows| < 0xFFFF_FFFF_FFFF_FFFF - 2;
                    host, sent_packets := HostModelNextReceiveMessage(host, cpacket);
                } else {
                    host := host.(receivedPacket := None);
                    sent_packets := [];
                    assert false;
                }
            } else {
                //host := host.(receivedPacket := None);
                sent_packets := [];
                //assert false;
            }
        } else {
            sent_packets := [];
            
        }
        ok, netEventLog, ios := DeliverOutboundPackets(sent_packets);
        if (!ok) { return; }
        assert old(Env().net.history()) + netEventLog == Env().net.history(); // deleteme
        lemma_ExtractSentPacketsFromIos(ios);   // ==>
        assert |sent_packets| == 0 ==> |ios| == 0;

        // The following loop takes the forall that's stated in terms of io indices and turns
        // it into a forall in terms of ios.  In other words, it takes
        // forall idx {:trigger 0 <= idx < |ios|} :: 0 <= idx < |ios| ==> ios[idx].LIoOpSend?
        // and turns it into
        // forall io {:trigger io in ios} :: io.LIoOpSend?
        forall io | io in ios
            ensures io.LIoOpSend?;
        {
            var pos :| 0 <= pos < |ios| && io == ios[pos];
            assert ios[pos].LIoOpSend?;
        }

        if (old(AbstractifyToHost()).receivedPacket.Some?) {
            if (b) {
                assert AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
                assert Env() == old(Env());
                assert RawIoConsistentWithSpecIO(netEventLog, ios);
                reveal_AbstractifyOutboundPacketsToSeqOfLSHTPackets();
                ghost var packet := old(AbstractifyToHost()).receivedPacket.v;
                if packet.msg.SingleMessage? {
                    assert Process_Message(old(AbstractifyToHost()), AbstractifyToHost(), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets))
                        || HostIgnoringUnParseable(old(AbstractifyToHost()), AbstractifyToHost(), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets));
                } else {
                    assert false;
                }

                assert AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets) == ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ios));

                assert ProcessReceivedPacket(old(AbstractifyToHost()), AbstractifyToHost(), ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ios))) || HostIgnoringUnParseable(old(AbstractifyToHost()), AbstractifyToHost(), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets));
                if ProcessReceivedPacket(old(AbstractifyToHost()), AbstractifyToHost(), ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ios))) {
                    assert LHost_ProcessReceivedPacket_Next(old(AbstractifyToHost()), AbstractifyToHost(), ios);
                } 

                if HostIgnoringUnParseable(old(AbstractifyToHost()), AbstractifyToHost(), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets)) {
                    assert HostNextIgnoreUnsendableProcess(old(AbstractifyToLScheduler()), AbstractifyToLScheduler().(nextActionIndex := 2), netEventLog);
                }
                assert LHost_ProcessReceivedPacket_Next(old(AbstractifyToHost()), AbstractifyToHost(), ios)
                    || HostNextIgnoreUnsendableProcess(old(AbstractifyToLScheduler()), AbstractifyToLScheduler().(nextActionIndex := 2), netEventLog);
            } else {
                assert AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
                assert Env() == old(Env());
                assert RawIoConsistentWithSpecIO(netEventLog, ios);
                reveal_AbstractifyOutboundPacketsToSeqOfLSHTPackets();
                assert !ShouldProcessReceivedMessage(old(AbstractifyToHost()));
                assert ProcessReceivedPacket(old(AbstractifyToHost()), AbstractifyToHost(), ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ios)));
                assert LHost_ProcessReceivedPacket_Next(old(AbstractifyToHost()), AbstractifyToHost(), ios);
            }
        } else {
            assert AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
            assert Env() == old(Env());
            assert RawIoConsistentWithSpecIO(netEventLog, ios);
            reveal_AbstractifyOutboundPacketsToSeqOfLSHTPackets();
            assert host.receivedPacket.Some? == false;
            assert old(AbstractifyToHost()).receivedPacket.Some? == false;
            assert ProcessReceivedPacket(old(AbstractifyToHost()), AbstractifyToHost(), ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ios)));
            assert LHost_ProcessReceivedPacket_Next(old(AbstractifyToHost()), AbstractifyToHost(), ios);
        }
      
    }
    
    
    method {:timeLimitMultiplier 2} Host_Next_main()
        returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<LSHTIo>)
        requires Valid();
        modifies Repr;
        ensures Repr == old(Repr);
        ensures  ok <==> Env() != null && Env().Valid() && Env().ok.ok();
        ensures Env() == old(Env());
        ensures ok ==> (
               Valid()
            && (   LScheduler_Next(old(AbstractifyToLScheduler()), AbstractifyToLScheduler(), ios)
                || HostNextIgnoreUnsendable(old(AbstractifyToLScheduler()), AbstractifyToLScheduler(), netEventLog))
            && LIoOpSeqCompatibleWithReduction(ios)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog) 
            && old(Env().net.history()) + netEventLog == Env().net.history()
            );
    {
        var curActionIndex := nextActionIndex;
        var nextActionIndex' := rollActionIndex(nextActionIndex);

        var curResendCount;
        var nextResendCount;
        ghost var host_old := old(AbstractifyToHost());
        ghost var scheduler_old := old(AbstractifyToLScheduler());
        ghost var host;
        ghost var scheduler;

        //print ("Host_Next_main Enter\n");
        assert scheduler_old.host == host_old;
        if (curActionIndex == 0) {
            ok, netEventLog, ios := Host_ReceivePacket_Next();
            if (!ok) { return; }
        } else if (curActionIndex == 1) {
            ok, netEventLog, ios := Host_ProcessReceivedPacket_Next();
            if (!ok) { return; }
        } else if (curActionIndex == 2) {
            curResendCount := resendCount;
            nextResendCount := rollResendCount(curResendCount);
            resendCount := nextResendCount;
            if (nextResendCount == 0) {
                ok, netEventLog, ios := Host_NoReceive_NoClock_Next();
                if (!ok) { return; }
            } else {
                ok := true;
                netEventLog := [];
                ios := [];
            }
        } else {
            assert false;
        }
        host := AbstractifyToHost();
        nextActionIndex := nextActionIndex';
        scheduler := AbstractifyToLScheduler();
        calc {
            scheduler.nextActionIndex;
            nextActionIndex as int;
            nextActionIndex' as int;
            (curActionIndex+1) as int % LHost_NumActions();
            (scheduler_old.nextActionIndex+1)%LHost_NumActions();
        }
        
        if (curActionIndex == 2) {
            calc {
                scheduler.resendCount;
                resendCount as int;
                nextResendCount as int;
                (curResendCount+1) as int % 100000000;
                (scheduler_old.resendCount+1)%100000000;
            }
        
            if (nextResendCount == 0) {
                assert LHost_NoReceive_Next(old(AbstractifyToLScheduler()).host, AbstractifyToLScheduler().host, ios);
            } else {
                assert scheduler == scheduler_old.(resendCount := scheduler.resendCount, nextActionIndex := scheduler.nextActionIndex);
            }

        }

        //assert  LHost_ReceivePacket_Next(old(AbstractifyToLScheduler()).host, AbstractifyToLScheduler().host, ios) || LHost_ProcessReceivedPacket_Next(old(AbstractifyToLScheduler()).host, AbstractifyToLScheduler().host, ios) || LHost_NoReceive_Next(old(AbstractifyToLScheduler()).host, AbstractifyToLScheduler().host, ios);
        assert NetClientIsValid(netClient);
        assert old(AbstractifyToLScheduler()).host.constants == AbstractifyToLScheduler().host.constants; 
        assert {:split_here} true;
        if (curActionIndex == 0) {
            assert old(AbstractifyToLScheduler()).nextActionIndex == 0;
            calc {
                AbstractifyToLScheduler().nextActionIndex;
                (curActionIndex+1) as int % LHost_NumActions();
                (curActionIndex+1) as int % 3;
                1 % 3;
                 1;
            }
            assert LScheduler_Next(old(AbstractifyToLScheduler()), AbstractifyToLScheduler(), ios)
                || HostNextIgnoreUnsendable(old(AbstractifyToLScheduler()), AbstractifyToLScheduler(), netEventLog);
        } else if (curActionIndex == 1) {
            assert LScheduler_Next(old(AbstractifyToLScheduler()), AbstractifyToLScheduler(), ios)
                || HostNextIgnoreUnsendable(old(AbstractifyToLScheduler()), AbstractifyToLScheduler(), netEventLog);
        } else if (curActionIndex == 2) {
        assert LScheduler_Next(old(AbstractifyToLScheduler()), AbstractifyToLScheduler(), ios);
    }

    }
}
} 
