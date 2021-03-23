include "../SHT/Host.i.dfy"
include "RefinementProof/Environment.i.dfy"
include "RefinementProof/EnvironmentRefinement.i.dfy"
include "../../Common/Collections/Sets.i.dfy"

module LiveSHT__BoundedClock_i {

datatype BoundedClock = BoundedClock(min:int, max:int)
}

module LiveSHT__Scheduler_i {
import opened SHT__Host_i
import opened LiveSHT__Environment_i
import opened LiveSHT__EnvironmentRefinement_i
import opened Collections__Sets_i
import opened LiveSHT__BoundedClock_i
import opened SHT__Network_i
import opened Protocol_Parameters_i
import opened Concrete_NodeIdentity_i`Spec
import opened SHT__Delegations_i
import opened Environment_s

function {:opaque} ExtractSentPacketsFromIos(ios:seq<LSHTIo>) : seq<LSHTPacket>
    ensures forall p :: p in ExtractSentPacketsFromIos(ios) <==> LIoOpSend(p) in ios;
{
    if |ios| == 0 then
        []
    else if ios[0].LIoOpSend? then
        [ios[0].s] + ExtractSentPacketsFromIos(ios[1..])
    else
        ExtractSentPacketsFromIos(ios[1..])

}

predicate ReceivePacket_Wrapper(s:Host, s':Host, pkt:Packet, sent_packets:set<Packet>)
{
    exists ack :: ReceivePacket(s, s', pkt, sent_packets, ack)
}

predicate LHost_ReceivePacketWithoutReadingClock(s:Host, s':Host, ios:seq<LSHTIo>)
    requires |ios| >= 1;
    requires ios[0].LIoOpReceive?;
    requires DelegationMapComplete(s.delegationMap);
{
    var pkt := Packet(ios[0].r.dst, ios[0].r.src, ios[0].r.msg);    
    var sent_packets := ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ios));   
    ReceivePacket_Wrapper(s, s', pkt, sent_packets)
}

predicate LHost_ReceivePacket_Next(s:Host, s':Host, ios:seq<LSHTIo>)
{
       |ios| >= 1
    && if ios[0].LIoOpTimeoutReceive? then
           s' == s && |ios| == 1
       else
       (
              DelegationMapComplete(s.delegationMap)
           && (ios[0].LIoOpReceive?
           //&& ios[0].r.msg.SingleMessage?
           && (forall i{:trigger ios[i].LIoOpSend?} :: 1 <= i < |ios| ==> ios[i].LIoOpSend?)
           && LHost_ReceivePacketWithoutReadingClock(s, s', ios))
       )
}

function LHost_NumActions() : int
{
    3
}

datatype LScheduler = LScheduler(host:Host, nextActionIndex:int, resendCount:int)

predicate LScheduler_Init(s:LScheduler, me:NodeIdentity, rootIdentity:NodeIdentity, hostIds:seq<NodeIdentity>, params:Parameters)
{
       Host_Init(s.host, me, rootIdentity, hostIds, params)
    && s.nextActionIndex == 0
    && s.resendCount == 0
}

predicate LHost_ProcessReceivedPacket_Next(s:Host, s':Host, ios:seq<LSHTIo>)
{
       DelegationMapComplete(s.delegationMap)
    && (forall io {:trigger io in ios} :: io in ios ==> io.LIoOpSend?)
    && ProcessReceivedPacket(s, s', ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ios)))
}

predicate LHost_NoReceive_Next(s:Host, s':Host, ios:seq<LSHTIo>)
{
       DelegationMapComplete(s.delegationMap)
    && (forall io {:trigger io in ios} :: io in ios ==> io.LIoOpSend?)
    && SpontaneouslyRetransmit(s, s', ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ios)))
}

/*
predicate LHost_Next_ReadClock_MaybeReSendUnAckedPackets(s:Host, s':Host, clock:BoundedClock, ios:seq<LSHTIo>)
{
    if clock.max < s.nextHeartbeatTime then
        s' == s && sent_packets == []
    else
           s'.nextHeartbeatTime == LCappedAddition(clock.min, s.constants.all.params.heartbeatPeriod, s.constants.all.params)
        && LBroadcastToEveryone(s.constants.all.config, s.constants.myIndex,
                                LPaxosMessage_Heartbeat(s.proposer.electionState.currentView,
                                                        s.constants.myIndex in s.proposer.electionState.currentViewSuspectors,
                                                        s.executor.opsComplete),
                                sent_packets)
        && s' == s[nextHeartbeatTime := s'.nextHeartbeatTime]
}*/

predicate LHost_NoReceive_Next_Wrapper(s:LScheduler, s':LScheduler, ios:seq<LSHTIo>)
{
       DelegationMapComplete(s.host.delegationMap)
     && s'.resendCount == (s.resendCount + 1) % 100000000
     && if (s'.resendCount == 0) then
           LHost_NoReceive_Next(s.host, s'.host, ios) 
        else (
              ios == []
           && s' == s.(resendCount := s'.resendCount, nextActionIndex := s'.nextActionIndex))
}

predicate LScheduler_Next(s:LScheduler, s':LScheduler, ios:seq<LSHTIo>)
{
       s'.nextActionIndex == (s.nextActionIndex + 1) % LHost_NumActions()
    && s'.host.constants == s.host.constants
    && s'.host.me == s.host.me
    && if s.nextActionIndex == 0 then
             s'.resendCount == s.resendCount
          && LHost_ReceivePacket_Next(s.host, s'.host, ios)
       else if s.nextActionIndex == 1 then
             s'.resendCount == s.resendCount
          && LHost_ProcessReceivedPacket_Next(s.host, s'.host, ios)
       else
          LHost_NoReceive_Next_Wrapper(s, s', ios)
}
} 
