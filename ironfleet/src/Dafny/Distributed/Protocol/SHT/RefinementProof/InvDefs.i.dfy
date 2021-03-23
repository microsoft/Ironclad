include "SHT.i.dfy"

module SHT__InvDefs_i {
import opened SHT__SHT_i
import opened Concrete_NodeIdentity_i`Spec
import opened SHT__Network_i
import opened AppInterface_i`Spec
import opened SHT__HT_s
import opened SHT__SingleDelivery_i
import opened SHT__Host_i
import opened Logic__Option_i
import opened SHT__Keys_i
import opened SHT__Delegations_i

// The Refinement definition (Lamport's Bar()) is trusted.
// Ugh. That makes the entire Host.i definition ... trusted! Aaagh!
// What a mess. Instead, can't we exists something?

//////////////////////////////////////////////////////////////////////////////
// These welformedness conditions are needed to define the refinement
// mapping, so they get floated up here 

function AllHostIdentities(s:SHT_State) : seq<NodeIdentity>
    requires SHT_MapsComplete(s);
    ensures forall id :: id in AllHostIdentities(s) ==> id in s.hosts;
{
    s.config.hostIds
}

predicate MapComplete(s:SHT_State)
{
       SHT_MapsComplete(s)
    && (forall id :: id in AllHostIdentities(s)
            ==> DelegationMapComplete(s.hosts[id].delegationMap))
}

predicate AllDelegationsToKnownHosts(s:SHT_State)
    requires MapComplete(s);
{
    forall id,k :: id in AllHostIdentities(s)
        ==> DelegateForKey(s.hosts[id].delegationMap, k) in AllHostIdentities(s)
}

//////////////////////////////////////////////////////////////////////////////
// Unacked list

predicate NoAcksInUnAckedLists(acct:SingleDeliveryAcct)
{
    forall id, i :: var unAcked := AckStateLookup(id, acct.sendState).unAcked;
              0 <= i < |unAcked| ==> unAcked[i].SingleMessage?
}

predicate UnAckedListsSequential(acct:SingleDeliveryAcct)
    requires NoAcksInUnAckedLists(acct);
{
    forall id, i, j :: var unAcked := AckStateLookup(id, acct.sendState).unAcked;
                 0 <= i && j == i + 1 && j < |unAcked|
                 ==> unAcked[i].seqno + 1 == unAcked[j].seqno
}

predicate UnAckedDstsConsistent(acct:SingleDeliveryAcct)
    requires NoAcksInUnAckedLists(acct);
{
    forall id, i :: var unAcked := AckStateLookup(id, acct.sendState).unAcked;
              0 <= i < |unAcked| ==> unAcked[i].dst == id
}

predicate UnAckedListExceedsNumPacketsAcked(acct:SingleDeliveryAcct)
    requires NoAcksInUnAckedLists(acct);
{
    forall id :: var ackState := AckStateLookup(id, acct.sendState);
        |ackState.unAcked| > 0 ==> ackState.unAcked[0].seqno == ackState.numPacketsAcked + 1
}

predicate {:opaque} UnAckedListInNetwork(s:SHT_State)
    requires MapComplete(s);
{
    forall id,msg,dst {:trigger msg in AckStateLookup(dst, s.hosts[id].sd.sendState).unAcked } :: 
        id  in AllHostIdentities(s)
     && msg in AckStateLookup(dst, s.hosts[id].sd.sendState).unAcked
     && NoAcksInUnAckedLists(s.hosts[id].sd)
     && dst == msg.dst
     ==> Packet(msg.dst, s.hosts[id].me, msg) in s.network
}

predicate UnAckedListProperties(acct:SingleDeliveryAcct)
{
       NoAcksInUnAckedLists(acct)
    && UnAckedListsSequential(acct)
    && UnAckedListExceedsNumPacketsAcked(acct)
    && UnAckedDstsConsistent(acct)
}

predicate AckListsInv(s:SHT_State)
    requires MapComplete(s);
{
        UnAckedListInNetwork(s)
    && (forall id :: id in AllHostIdentities(s) ==> UnAckedListProperties(s.hosts[id].sd))
}

/*
predicate NoAcksInUnAckedLists(s:SHT_State)
    requires MapComplete(s);
{
   forall id, id' :: id in AllHostIdentities() && id' in AllHostIdentities() 
      ==> (var unAcked := AckStateLookup(id', s.hosts[id].sd.sendState).unAcked;
           forall i :: 0 <= i < |unAcked| ==> unAcked[i].SingleMessage?)
}

predicate UnAckedListsSequential(s:SHT_State)
    requires MapComplete(s);
    requires NoAcksInUnAckedLists(s);
{
   forall id, id' :: id in AllHostIdentities() && id' in AllHostIdentities() 
        ==> (var unAcked := AckStateLookup(id', s.hosts[id].sd.sendState).unAcked;
             forall i, j :: 0 <= i && j == i + 1 && j < |unAcked|
                ==> unAcked[i].seqno + 1 == unAcked[j].seqno)
}

predicate UnAckedListExceedsNumPacketsAcked(s:SHT_State)
    requires MapComplete(s);
    requires NoAcksInUnAckedLists(s);
{
   forall id, id' :: id in AllHostIdentities() && id' in AllHostIdentities() 
        ==> (var ackState := AckStateLookup(id', s.hosts[id].sd.sendState);
             |ackState.unAcked| > 0 ==> ackState.unAcked[0].seqno == ackState.numPacketsAcked + 1)
}
*/

//////////////////////////////////////////////////////////////////////////////
// Hosts claim keys

predicate DelegationPacket(p:Option<Packet>)
{
    p.Some? && p.v.msg.SingleMessage? && p.v.msg.m.Delegate?
}

predicate BufferedPacketClaimsKey(s:Host, k:Key)
{
    DelegationPacket(s.receivedPacket) && KeyRangeContains(s.receivedPacket.v.msg.m.range, KeyPlus(k))
 && s.receivedPacket.v.src in s.constants.hostIds
 && s.receivedPacket.v.dst in s.constants.hostIds
}

predicate HostClaimsKey(s:Host, k:Key)
    requires DelegationMapComplete(s.delegationMap);
{
    // My map tells me I own the key
    DelegateForKey(s.delegationMap, k)==s.me
 || // or I have a buffered delegation message that gives me ownership of the key
    BufferedPacketClaimsKey(s, k)
}

//////////////////////////////////////////////////////////////////////////////
// Packets claim keys

predicate PacketsHaveSaneHeaders(s:SHT_State)
    requires MapComplete(s);
{
    true
//  Can't establish this once we start letting clients send packets
//    forall pkt :: pkt in s.network
//        ==> pkt.src in AllHostIdentities(s) && pkt.dst in AllHostIdentities(s)
}

predicate PacketInFlight(s:SHT_State, pkt:Packet)
    requires MapComplete(s);
{
       pkt in s.network 
    && pkt.src in AllHostIdentities(s)
    && pkt.dst in AllHostIdentities(s)
    && MessageNotReceived(s.hosts[pkt.dst].sd, pkt.src, pkt.msg)
}

predicate InFlightPacketClaimsKey(s:SHT_State, pkt:Packet, k:Key)
    requires MapComplete(s);
{
       pkt.msg.SingleMessage?
    && pkt.msg.m.Delegate?
    && PacketInFlight(s, pkt)
    && KeyRangeContains(pkt.msg.m.range, KeyPlus(k))
}

// TODO Explicitly name these CHOOSE invocations to work around Dafny bug
function ThePacketThatClaimsKey(s:SHT_State, k:Key) : Packet
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
    requires exists pkt :: InFlightPacketClaimsKey(s,pkt,k);
    ensures  var p := ThePacketThatClaimsKey(s,k);
             p.msg.SingleMessage? && p.msg.m.Delegate?;
{
    var pkt :| InFlightPacketClaimsKey(s,pkt,k); pkt
}

function TheHostThatClaimsKey(s:SHT_State, k:Key) : NodeIdentity
    requires MapComplete(s);
    requires AllDelegationsToKnownHosts(s);
    requires exists id {:trigger HostClaimsKey(s.hosts[id], k)} :: id in AllHostIdentities(s) && HostClaimsKey(s.hosts[id], k);
{
    var id :| id in AllHostIdentities(s) && HostClaimsKey(s.hosts[id], k); id
}

function FindHostHashTable(s:SHT_State, k:Key) : Hashtable
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
    requires AllDelegationsToKnownHosts(s);
    requires exists id {:trigger HostClaimsKey(s.hosts[id], k)} ::
             id in AllHostIdentities(s) && HostClaimsKey(s.hosts[id], k);
{
    var id := TheHostThatClaimsKey(s, k);
    if BufferedPacketClaimsKey(s.hosts[id], k) then
       // && NewSingleMessage(s.hosts[id].sd, s.hosts[id].receivedPacket.v) then
        s.hosts[id].receivedPacket.v.msg.m.h
    else // assert DelegateForKey(s.hosts[id].delegationMap, k)==s.hosts[id]..me 
        s.hosts[id].h
}

function FindHashTable(s:SHT_State, k:Key) : Hashtable
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
    requires AllDelegationsToKnownHosts(s);
{
    if exists pkt :: InFlightPacketClaimsKey(s,pkt,k) then
        ThePacketThatClaimsKey(s,k).msg.m.h
    else if exists id {:trigger HostClaimsKey(s.hosts[id], k)} :: 
                   id in AllHostIdentities(s) && HostClaimsKey(s.hosts[id], k) then
        FindHostHashTable(s, k)
    else
        // Inv ==> this case is false
        map []
}

} 
