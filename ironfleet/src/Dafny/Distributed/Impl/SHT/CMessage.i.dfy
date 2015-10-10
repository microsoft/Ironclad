include "../../Protocol/SHT/Message.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../../Protocol/SHT/Network.i.dfy"
include "Parameters.i.dfy"
include "../../Common/Logic/Option.i.dfy"

module SHT__CMessage_i {
import opened SHT__Message_i
import opened Common__NodeIdentity_i
import opened SHT__Network_i
import opened Impl_Parameters_i
import opened Logic__Option_i

// For now, we use the same keys and values the app's spec does
// Someday, we may want to introduce a split between the app's
// high-level view of keys and values, and its low-level implementation

datatype CMessage =
      CGetRequest(k_getrequest:Key)
    | CSetRequest(k_setrequest:Key, v_setrequest:OptionalValue)
    | CReply(k_reply:Key, v:OptionalValue)
    | CRedirect(k_redirect:Key, id:EndPoint)
    | CShard(kr:KeyRange, recipient:EndPoint)
    | CDelegate(range:KeyRange, h:Hashtable)

datatype CSingleMessage = CSingleMessage(seqno:uint64, dst:EndPoint, m:CMessage) 
                        | CAck(ack_seqno:uint64) // I got everything up to and including seqno
                        | CInvalidMessage()

type CPMsg = CSingleMessage
datatype CPacket = CPacket(dst:EndPoint, src:EndPoint, msg:CPMsg)

predicate CMessageIsAbstractable(cmsg:CMessage)
{
       (cmsg.CRedirect? ==> EndPointIsAbstractable(cmsg.id))
    && (cmsg.CShard?    ==> EndPointIsAbstractable(cmsg.recipient))
}

function AbstractifyCMessageToRslMessage(cmsg:CMessage) : Message
    requires CMessageIsAbstractable(cmsg);
{
    match cmsg
        case CGetRequest(k) => GetRequest(k)
        case CSetRequest(k, v) => SetRequest(k, v)
        case CReply(k, v) => Reply(k, v)
        case CRedirect(k, id) => Redirect(k, AbstractifyEndPointToNodeIdentity(id))
        case CShard(kr, recipient) => Shard(kr, AbstractifyEndPointToNodeIdentity(recipient))
        case CDelegate(range, h) => Delegate(range, h)
}

predicate CSingleMessageIsAbstractable(smsg:CSingleMessage)
{
    match smsg
        case CSingleMessage(seqno, dst, m) => EndPointIsAbstractable(dst) && CMessageIsAbstractable(m)
        case CAck(_) => true
        case CInvalidMessage => true
}

function AbstractifyCSingleMessageToSingleMessage(smsg:CSingleMessage) : SingleMessage<Message>
    requires CSingleMessageIsAbstractable(smsg);
{
    match smsg
        case CSingleMessage(seqno, dst, m) => 
            SingleMessage(int(seqno), AbstractifyEndPointToNodeIdentity(dst), AbstractifyCMessageToRslMessage(m))
        case CAck(seqno) => Ack(int(seqno))
        case CInvalidMessage => InvalidMessage()
}

predicate CSingleMessageIsValid(smsg:CSingleMessage, params:CParameters)
{
    match smsg
        case CSingleMessage(seqno, _, _) => seqno < params.max_seqno
        case CAck(seqno) => seqno < params.max_seqno
        case CInvalidMessage => false
}

predicate CSingleMessageSeqIsAbstractable(cs:seq<CSingleMessage>) 
{
    forall i :: 0 <= i < |cs| ==> CSingleMessageIsAbstractable(cs[i])
}

function AbstractifySeqOfCSingleMessageToSeqOfSingleMessage(cs:seq<CSingleMessage>) : seq<SingleMessage<Message>>
    requires CSingleMessageSeqIsAbstractable(cs);                                          
{
    MapSeqToSeq(cs, AbstractifyCSingleMessageToSingleMessage)
}

//////////////////////////////////////////////////////////////////////////////

predicate CPacketIsAbstractable(cpacket:CPacket)
{
       EndPointIsAbstractable(cpacket.dst)
    && EndPointIsAbstractable(cpacket.src)
    && CSingleMessageIsAbstractable(cpacket.msg)
}

function AbstractifyCPacketToShtPacket(cpacket:CPacket) : Packet
    requires CPacketIsAbstractable(cpacket);
{
    Packet(AbstractifyEndPointToNodeIdentity(cpacket.dst),
           AbstractifyEndPointToNodeIdentity(cpacket.src),
           AbstractifyCSingleMessageToSingleMessage(cpacket.msg))
}

predicate CPacketsIsAbstractable(cps:set<CPacket>)
{
    forall p :: p in cps ==> CPacketIsAbstractable(p)
}

function {:opaque} AbstractifyCPacketsToPackets(cps:set<CPacket>) : set<Packet>
    requires CPacketsIsAbstractable(cps);
    ensures forall p :: p in cps ==> AbstractifyCPacketToShtPacket(p) in AbstractifyCPacketsToPackets(cps);
{
    set p | p in cps :: AbstractifyCPacketToShtPacket(p)
}

predicate CPacketSeqIsAbstractable(cps:seq<CPacket>)
{
    forall p :: p in cps ==> CPacketIsAbstractable(p)
}

function {:opaque} AbstractifySeqOfCPacketsToSetOfShtPackets(cps:seq<CPacket>) : set<Packet>
    requires CPacketSeqIsAbstractable(cps);
    ensures forall p :: p in cps ==> AbstractifyCPacketToShtPacket(p) in AbstractifySeqOfCPacketsToSetOfShtPackets(cps);
{
    set p | p in cps :: AbstractifyCPacketToShtPacket(p)
}

predicate OptionCPacketIsAbstractable(cp:Option<CPacket>)
{
    match cp {
        case Some(p) => CPacketIsAbstractable(p)
        case None => true
    }
}

function AbstractifyOptionCPacketToOptionShtPacket(cp:Option<CPacket>) : Option<Packet>
    requires OptionCPacketIsAbstractable(cp);
{
    match cp {
        case Some(p) => Some(AbstractifyCPacketToShtPacket(p))
        case None => None()
    }
}
}
