include "../../Protocol/SHT/Host.i.dfy"
include "Delegations.i.dfy"
include "SingleDeliveryState.i.dfy"
include "ConstantsState.i.dfy"
include "PacketParsing.i.dfy"
include "../../Common/Logic/Option.i.dfy"

module SHT__HostState_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened SHT__Host_i
import opened SHT__SingleDeliveryState_i
import opened Impl__Delegations_i
import opened SHT__ConstantsState_i
import opened SHT__PacketParsing_i
import opened SHT__HT_s
import opened Logic__Option_i
import opened AbstractServiceSHT_s`All
import opened SHT__CMessage_i
import opened Common__UdpClient_i
import opened AppInterface_i`Spec
import opened Common__NodeIdentity_i
import opened Impl_Parameters_i

datatype HostState = HostState(
    constants:ConstantsState,
    me:EndPoint,
    delegationMap:CDelegationMap,
    h:Hashtable,
    sd:CSingleDeliveryAcct,
    receivedPacket:Option<CPacket>,
    numDelegations:uint64,
    ghost receivedRequests:seq<AppRequest>
)

predicate HostStateIsAbstractable(host:HostState)
{
       ConstantsStateIsAbstractable(host.constants)
    && EndPointIsAbstractable(host.me)
    && CDelegationMapIsAbstractable(host.delegationMap)
    && true // hashtable goes straight across
    && CSingleDeliveryAcctIsAbstractable(host.sd)
    && OptionCPacketIsAbstractable(host.receivedPacket)
}

function AbstractifyHostStateToHost(host:HostState) : Host
    requires HostStateIsAbstractable(host)
{
    Host(AbstractifyToConstants(host.constants),
        AbstractifyEndPointToNodeIdentity(host.me), 
        AbstractifyCDelegationMapToDelegationMap(host.delegationMap),
        host.h,
        AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(host.sd),
        AbstractifyOptionCPacketToOptionShtPacket(host.receivedPacket),
        host.numDelegations as int,
        host.receivedRequests)
}

predicate HostStateIsValid(host:HostState)
{
       HostStateIsAbstractable(host)
    && (forall k :: k in host.h ==> ValidKey(k)) 
    && (forall k :: k in host.h ==> ValidValue(host.h[k]))
    && CSingleDeliveryAccountIsValid(host.sd, host.constants.params)
    && (host.receivedPacket.Some? ==> CPacketIsAbstractable(host.receivedPacket.v) 
                                   && host.receivedPacket.v.msg.CSingleMessage? 
                                   && !host.receivedPacket.v.msg.CInvalidMessage? 
                                   && CSingleMessageIs64Bit(host.receivedPacket.v.msg) 
                                   && host.receivedPacket.v.dst == host.me)
    && ConstantsStateIsValid(host.constants)
    && host.numDelegations < host.constants.params.max_delegations
    && |host.delegationMap.lows| <= 2 * host.numDelegations as int
}


predicate InitHostStatePostconditions(constants:ConstantsState, host:HostState)
{
       ConstantsStateIsAbstractable(constants)
    && HostStateIsAbstractable(host)
    && Host_Init(AbstractifyHostStateToHost(host), AbstractifyEndPointToNodeIdentity(host.me), AbstractifyEndPointToNodeIdentity(constants.rootIdentity), AbstractifyEndPointsToNodeIdentities(constants.hostIds), AbstractifyCParametersToParameters(constants.params))
    && host.constants == constants
    && CSingleDeliveryAccountIsValid(host.sd, host.constants.params)
    && HostStateIsValid(host)
}

predicate HostState_common_preconditions(host:HostState, cpacket:CPacket)
{
       HostStateIsAbstractable(host)
    && CPacketIsAbstractable(cpacket)
    && HostStateIsValid(host)
}

predicate HostState_common_postconditions(host:HostState, cpacket:CPacket, host':HostState, sent_packets:seq<CPacket>)
{
       HostState_common_preconditions(host, cpacket)
    && HostStateIsAbstractable(host')
    && host'.constants == host.constants
    && host'.me == host.me
    && CPacketSeqIsAbstractable(sent_packets)
    && HostStateIsValid(host')
    && OutboundPacketsSeqIsValid(sent_packets)
    && OutboundPacketsSeqHasCorrectSrc(sent_packets, host.me)
    && (forall p :: p in sent_packets ==> p.msg.CSingleMessage? || p.msg.CAck?)
    && AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets) == ExtractPacketsFromLSHTPackets(AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets))
}

predicate NextGetRequestPreconditions(host:HostState, cpacket:CPacket)
{
       HostStateIsAbstractable(host)
    && CPacketIsAbstractable(cpacket)
    && cpacket.msg.CSingleMessage?
    && cpacket.msg.m.CGetRequest?
    //&& ValidKey(cpacket.msg.m.k_getrequest)
    //&& CSingleMessageMarshallable(cpacket.msg)
    && CSingleDeliveryAccountIsValid(host.sd, host.constants.params)
    && HostState_common_preconditions(host, cpacket)
}
predicate NextGetRequestPostconditions(host:HostState, cpacket:CPacket, host':HostState, sent_packets:seq<CPacket>)
{
       NextGetRequestPreconditions(host, cpacket)
    && HostStateIsAbstractable(host')
    && CPacketSeqIsAbstractable(sent_packets)
    && NextGetRequest(AbstractifyHostStateToHost(host), AbstractifyHostStateToHost(host'), AbstractifyCPacketToShtPacket(cpacket), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets))
    && HostState_common_postconditions(host, cpacket, host', sent_packets)
    && host'.receivedPacket == None
}

predicate NextSetRequestPreconditions(host:HostState, cpacket:CPacket)
{
       HostStateIsAbstractable(host)
    && CPacketIsAbstractable(cpacket)
    && cpacket.msg.CSingleMessage?
    && cpacket.msg.m.CSetRequest?
    && CSingleDeliveryAccountIsValid(host.sd, host.constants.params)
    //&& ValidKey(cpacket.msg.m.k_setrequest)
    //&& ValidOptionalValue(cpacket.msg.m.v_setrequest)
    //&& CSingleMessageMarshallable(cpacket.msg)
    && HostState_common_preconditions(host, cpacket)
}
predicate NextSetRequestPostconditions(host:HostState, cpacket:CPacket, host':HostState, sent_packets:seq<CPacket>)
{
       NextSetRequestPreconditions(host, cpacket)
    && HostStateIsAbstractable(host')
    && CPacketSeqIsAbstractable(sent_packets)
    && NextSetRequest(AbstractifyHostStateToHost(host), AbstractifyHostStateToHost(host'), AbstractifyCPacketToShtPacket(cpacket), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets))
    && HostState_common_postconditions(host, cpacket, host', sent_packets)
    && host'.receivedPacket == None
}

predicate NextDelegatePreconditions(host:HostState, cpacket:CPacket)
{
       HostStateIsAbstractable(host)
    && CPacketIsAbstractable(cpacket)
    && cpacket.msg.CSingleMessage?
    && cpacket.msg.m.CDelegate?
    && CSingleDeliveryAccountIsValid(host.sd, host.constants.params)
    //&& |host.delegationMap.lows| < 0xFFFF_FFFF_FFFF_FFFF - 2
    //&& !EmptyKeyRange(cpacket.msg.m.range)
    /*&& ValidKeyRange(cpacket.msg.m.range)
    && (forall k :: k in cpacket.msg.m.h ==> ValidKey(k))
    && (forall k :: k in cpacket.msg.m.h ==> ValidValue(cpacket.msg.m.h[k]))*/
    //&& CSingleMessageMarshallable(cpacket.msg)
    && HostState_common_preconditions(host, cpacket)
    //&& host.numDelegations < host.constants.params.max_delegations - 2

}
predicate NextDelegatePostconditions(host:HostState, cpacket:CPacket, host':HostState, sent_packets:seq<CPacket>)
{
       NextDelegatePreconditions(host, cpacket)
    && HostStateIsAbstractable(host')
    && CPacketSeqIsAbstractable(sent_packets)
    && HostState_common_postconditions(host, cpacket, host', sent_packets)
    && host'.receivedPacket == None
}

predicate NextShardPreconditions(host:HostState, cpacket:CPacket)
{
       HostStateIsAbstractable(host)
    && CPacketIsAbstractable(cpacket)
    && HostState_common_preconditions(host, cpacket)
    && cpacket.msg.CSingleMessage?
    && cpacket.msg.m.CShard?
    && CSingleDeliveryAccountIsValid(host.sd, host.constants.params)
    //&& cpacket.msg.m.recipient != host.constants.me
    //&& cpacket.msg.m.recipient in host.constants.hostIds
    //&& DelegateForKeyRangeIsHost(AbstractifyCDelegationMapToDelegationMap(host.delegationMap), cpacket.msg.m.kr, AbstractifyEndPointToNodeIdentity(host.constants.me))
    && |host.delegationMap.lows| < 0xFFFF_FFFF_FFFF_FFFF - 2
    //&& !EmptyKeyRange(cpacket.msg.m.kr)
    /*&& ValidKeyRange(cpacket.msg.m.kr)*/
    //&& |ExtractRange(host.h, cpacket.msg.m.kr)| < 0x1_0000_0000
    //&& CSingleMessageMarshallable(cpacket.msg)
    && HostState_common_preconditions(host, cpacket)
    //&& host.numDelegations < host.constants.params.max_delegations - 2
}

predicate NextShardPostconditions(host:HostState, cpacket:CPacket, host':HostState, sent_packets:seq<CPacket>)
{
       NextShardPreconditions(host, cpacket)
    && HostStateIsAbstractable(host')
    && CPacketSeqIsAbstractable(sent_packets)
    && NextShard_Wrapper(AbstractifyHostStateToHost(host), AbstractifyHostStateToHost(host'), AbstractifyCPacketToShtPacket(cpacket), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets))
    && HostState_common_postconditions(host, cpacket, host', sent_packets)
    && host'.receivedPacket == None
}

predicate SpontaneouslyRetransmitPreconditions(host:HostState)
{
       HostStateIsAbstractable(host)
    && CSingleDeliveryAccountIsValid(host.sd, host.constants.params)
    && HostStateIsValid(host)
}

predicate SpontaneouslyRetransmitPostconditions(host:HostState, host':HostState, sent_packets:seq<CPacket>)
{
       SpontaneouslyRetransmitPreconditions(host)
    && host' == host
    && HostStateIsAbstractable(host')
    && CPacketSeqIsAbstractable(sent_packets)
    && SpontaneouslyRetransmit(AbstractifyHostStateToHost(host), AbstractifyHostStateToHost(host'), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets))
    && (forall i :: 0 <= i < |sent_packets| ==> CPacketIsSendable(sent_packets[i]) && sent_packets[i].msg.CSingleMessage? && CSingleMessageMarshallable(sent_packets[i].msg) && sent_packets[i].src == host.me)
    && (forall i :: 0 <= i < |sent_packets| ==> sent_packets[i].src == host.me)
    && HostStateIsValid(host')
}
}
