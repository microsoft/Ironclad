
include "../SHT/HostModel.i.dfy"
include "../../Protocol/LiveSHT/Scheduler.i.dfy"
include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/SHT/Host.i.dfy"
include "UdpSHT.i.dfy"
//include "CBoundedClock.i.dfy"

module LiveSHT__SchedulerModel_i {
import opened Environment_s
import opened SHT__Host_i
import opened SHT__HostModel_i
import opened SHT__CMessage_i
import opened SHT__PacketParsing_i
import opened LiveSHT__Scheduler_i
import opened LiveSHT__UdpSHT_i
import opened LiveSHT__Environment_i
import opened Common__NodeIdentity_i

predicate AllIosAreSends(ios:seq<LSHTIo>)
{
    forall i :: 0<=i<|ios| ==> ios[i].LIoOpSend?
}

lemma MapSentPacketToIos_ExtractSentPacketsFromIos_equivalence(sent_packet:CPacket, ios:seq<LSHTIo>)
        requires OutboundPacketsIsValid(sent_packet);
        requires ios == MapSentPacketToIos(sent_packet);
        ensures [AbstractifyOutboundPacketsToLSHTPacket(sent_packet)] == ExtractSentPacketsFromIos(ios);
{
    reveal_ExtractSentPacketsFromIos();
}

lemma MapSentPacketSeqToIos_ExtractSentPacketsFromIos_equivalence(sent_packets:seq<CPacket>, ios:seq<LSHTIo>)
    requires OutboundPacketsSeqIsValid(sent_packets);
    //requires forall i :: 0 <= i < |sent_packets| ==> CPacketIsSendable(sent_packets[i]) && sent_packets[i].msg.CSingleMessage? && CSingleMessageMarshallable(sent_packets[i].msg);
    requires ios == MapSentPacketSeqToIos(sent_packets);
    ensures AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
{
    reveal_ExtractSentPacketsFromIos();
    reveal_MapSentPacketSeqToIos();
    reveal_AbstractifyOutboundPacketsToSeqOfLSHTPackets();
    var x := AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets);
    var y := ExtractSentPacketsFromIos(ios);
    if (|x| > 0) {
        MapSentPacketSeqToIos_ExtractSentPacketsFromIos_equivalence(sent_packets[1..], ios[1..]);
    }
}

function MapSentPacketToIos(sent_packet:CPacket) : seq<LSHTIo>
    requires OutboundPacketsIsValid(sent_packet);
{
    [LIoOpSend(AbstractifyCPacketToLSHTPacket(sent_packet))]
}


function {:opaque} MapSentPacketSeqToIos(sent_packets:seq<CPacket>) : seq<LSHTIo>
    requires OutboundPacketsSeqIsValid(sent_packets);
    //requires forall i :: 0 <= i < |sent_packets| ==> CPacketIsSendable(sent_packets[i]) && sent_packets[i].msg.CSingleMessage? && CSingleMessageMarshallable(sent_packets[i].msg)
    ensures |MapSentPacketSeqToIos(sent_packets)| == |sent_packets|;
    ensures forall i :: 0 <= i < |sent_packets| ==> MapSentPacketSeqToIos(sent_packets)[i] == LIoOpSend(AbstractifyCPacketToLSHTPacket(sent_packets[i]));
    ensures (forall io :: io in MapSentPacketSeqToIos(sent_packets) ==> io.LIoOpSend?);
{
    //lemma_MapSentPacketSeqToIos(sent_packets);
    if |sent_packets| == 0 then
        []
    else if |sent_packets| == 1 then
        [LIoOpSend(AbstractifyCPacketToLSHTPacket(sent_packets[0]))]
    else
        [LIoOpSend(AbstractifyCPacketToLSHTPacket(sent_packets[0]))] + MapSentPacketSeqToIos(sent_packets[1..])
}
} 
