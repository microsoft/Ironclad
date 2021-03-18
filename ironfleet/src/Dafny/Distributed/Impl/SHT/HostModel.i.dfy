include "HostState.i.dfy"
include "SingleDeliveryModel.i.dfy"
include "PacketParsing.i.dfy"
include "DelegationLookup.i.dfy"

module SHT__HostModel_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened SHT__HostState_i
import opened SHT__SingleDeliveryModel_i
import opened SHT__PacketParsing_i
import opened DelegationLookup_i
import opened Environment_s
import opened SHT__Host_i
import opened SHT__SingleDeliveryState_i
import opened Impl__Delegations_i
import opened SHT__ConstantsState_i
import opened SHT__HT_s
import opened Logic__Option_i
import opened AbstractServiceSHT_s`All
import opened SHT__CMessage_i
import opened Common__UdpClient_i
import opened AppInterface_i`Spec
import opened Common__NodeIdentity_i
import opened Impl_Parameters_i
import opened SHT__Keys_i
import opened SHT__Network_i
import opened SHT__Delegations_i
import opened SHT__Message_i
import opened SHT__SingleMessage_i
import opened SHT__SingleDelivery_i

function method mapremove<KT,VT>(m:map<KT,VT>, k:KT) : map<KT,VT>
{
    map ki | ki in m && ki != k :: m[ki]
}

function method mapdomain<KT,VT>(m:map<KT,VT>) : set<KT>
{
    set k | k in m :: k
}

function method BulkUpdateDomain(h:Hashtable, kr:KeyRange, u:Hashtable) : set<Key>
{
   set k | k in mapdomain(h)+mapdomain(u) && (KeyRangeContains(kr, KeyPlus(k)) ==> k in u)
}

function method BulkUpdateHashtable(h:Hashtable, kr:KeyRange, u:Hashtable) : Hashtable
{
    map k {:auto_trigger} | k in BulkUpdateDomain(h, kr, u) :: if (k in u) then u[k] else h[k]
}

function method BulkRemoveHashtable(h:Hashtable, kr:KeyRange) : Hashtable {
    map k | (k in h && !KeyRangeContains(kr, KeyPlus(k))) :: h[k]
}

function method ExtractRange(h:Hashtable, kr:KeyRange) : Hashtable 
    requires ValidKeyRange(kr);
    requires forall k :: k in h ==> ValidKey(k) && ValidValue(h[k]);
    ensures forall k :: k in ExtractRange(h, kr) ==> k in h && ExtractRange(h, kr)[k] == h[k];
    ensures (forall k :: k in ExtractRange(h, kr) ==> ValidKey(k) && ValidValue(ExtractRange(h, kr)[k]))
    //ensures ValidHashtable(ExtractRange(h, kr));
{
    map k | (k in h && KeyRangeContains(kr, KeyPlus(k))) :: h[k]
}

method InitHostState(constants:ConstantsState, me:EndPoint) returns (host:HostState)
    requires ConstantsStateIsValid(constants);
    requires EndPointIsAbstractable(me);
    ensures InitHostStatePostconditions(constants, host);
    ensures host.me == me;
    ensures host.constants == constants;
{
    var sd := CSingleDeliveryAcctInit(constants.params);
    var delegationMap := CDelegationMap([Mapping(KeyZero(), constants.rootIdentity)]);

    //host := HostState(constants, me, delegationMap, map[], sd, None(), |delegationMap.lows| as uint64);
    host := HostState(constants, me, delegationMap, map[], sd, None(), |delegationMap.lows| as uint64, []);
    
    assert AbstractifyCDelegationMapToDelegationMap(delegationMap) == DelegationMap_Init(AbstractifyEndPointToNodeIdentity(constants.rootIdentity));
    assert Host_Init(AbstractifyHostStateToHost(host), AbstractifyEndPointToNodeIdentity(me), AbstractifyEndPointToNodeIdentity(constants.rootIdentity), AbstractifyEndPointsToNodeIdentities(constants.hostIds), AbstractifyCParametersToParameters(constants.params));
}

// TODO: move this method to Delegations.i.dfy once it stabilizes
method DelegateForKeyImpl(m:CDelegationMap, k:Key) returns (ep:EndPoint)
    requires 0<|m.lows|;
     requires CDelegationMapIsValid(m);
     ensures EndPointIsValidIPV4(ep);
     ensures AbstractifyCDelegationMapToDelegationMap(m)[k] == AbstractifyEndPointToNodeIdentity(ep);
     ensures AbstractifyEndPointToNodeIdentity(ep) == DelegateForKey(AbstractifyCDelegationMapToDelegationMap(m), k);
{
    ep := m.lows[CDM_IndexForKey(m,KeyPlus(k))].id;
}

method {:timeLimitMultiplier 2} HostModelNextGetRequest(host:HostState, cpacket:CPacket) returns (host':HostState, sent_packets:seq<CPacket>)
    requires NextGetRequestPreconditions(host, cpacket);
    ensures NextGetRequestPostconditions(host, cpacket, host', sent_packets);
{
    var k := cpacket.msg.m.k_getrequest;
    var owner := DelegateForKeyImpl(host.delegationMap, k);

    var m;
    ghost var receivedRequest := AppGetRequest(cpacket.msg.seqno as int, k);
    ghost var newReceivedRequests:seq<AppRequest>;
    
    if (owner == host.me) {
        m := CReply(k, HashtableLookup(host.h, k));
        newReceivedRequests := host.receivedRequests + [receivedRequest];   
    } else {
        m := CRedirect(k, owner);
        newReceivedRequests := host.receivedRequests;
    }
    assert MessageMarshallable(m);     

    var sd', sm, shouldSend  := SendSingleCMessage(host.sd, m, cpacket.src, host.constants.params);
    
    host' := host.(sd := sd', receivedPacket := None);
    var p := CPacket(cpacket.src, host.me, sm);
    if shouldSend {
        host' := host.(sd := sd', receivedPacket := None, receivedRequests := newReceivedRequests);
        sent_packets := [p];
    } else {
        host' := host.(receivedPacket := None);
        sent_packets := [];
    }

    ghost var s := AbstractifyHostStateToHost(host);
    ghost var s' := AbstractifyHostStateToHost(host');
    ghost var g_m := AbstractifyCMessageToRslMessage(m);
    ghost var g_sm := AbstractifyCSingleMessageToSingleMessage(sm);
    ghost var g_src := AbstractifyEndPointToNodeIdentity(cpacket.src);
    ghost var g_out := AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets);
       
    lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
    reveal_AbstractifySeqOfCPacketsToSetOfShtPackets();

    assert AbstractifyCPacketToShtPacket(p) == Packet(g_src, s.me, g_sm); // OBSERVE
      
    assert NextGetRequest_Reply(s, s', g_src, cpacket.msg.seqno as int,  cpacket.msg.m.k_getrequest, g_sm, g_m, g_out, shouldSend);
}

method {:timeLimitMultiplier 2} HostModelNextSetRequest(host:HostState, cpacket:CPacket) returns (host':HostState, sent_packets:seq<CPacket>)
    requires NextSetRequestPreconditions(host, cpacket);
    ensures NextSetRequestPostconditions(host, cpacket, host', sent_packets);
{   
    var k := cpacket.msg.m.k_setrequest;
    var ov := cpacket.msg.m.v_setrequest;
    var owner := DelegateForKeyImpl(host.delegationMap, k);
    var m;
    var h';
    
    var marshallable := IsMessageMarshallable(cpacket.msg.m);
    if !marshallable {
        assert !ValidKey(k) || !ValidOptionalValue(ov);
        host' := host.(receivedPacket := None);
        sent_packets := [];

        ghost var s := AbstractifyHostStateToHost(host);
        ghost var s' := AbstractifyHostStateToHost(host');
        reveal_AbstractifySeqOfCPacketsToSetOfShtPackets();
        assert AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets) == {};
        assert NextSetRequest_Complete(s, s', AbstractifyCPacketToShtPacket(cpacket).src, AbstractifyCPacketToShtPacket(cpacket).msg.seqno, 
                                       AbstractifyCPacketToShtPacket(cpacket).msg.m, Ack(0), Reply(k, ov), {}, true);
        //                                                              ^        ^
        // Because we're in the else clause of SetRequest_Complete      |        |
        // these arguments don't matter ------------------------------------------
        return;
    }

    if (owner == host.me) {
        /*if ov.ValueAbsent? {
            h' := mapremove(host.h, k); 
        } else {
            h' := host.h[k:=ov.v];
        }*/

        m := CReply(k, ov);
        
    } else {
        //h' := host.h;
        m := CRedirect(k, owner);
    }
    var sd', sm, shouldSend := SendSingleCMessage(host.sd, m, cpacket.src, host.constants.params);

    ghost var receivedRequest := AppSetRequest(cpacket.msg.seqno as int, k, ov);
    ghost var newReceivedRequests:seq<AppRequest>;

    if (shouldSend) {
        if (owner == host.me) {
            if ov.ValueAbsent? {
                h' := mapremove(host.h, k); 
            } else {
                h' := host.h[k:=ov.v];
            }
            
            newReceivedRequests := host.receivedRequests + [receivedRequest];
        } else {
            h' := host.h;
            newReceivedRequests := host.receivedRequests;
        }
        
        host' := host.(h := h', sd := sd', receivedPacket := None, receivedRequests := newReceivedRequests);
    } else {
        host' := host.(receivedPacket := None);
    }
    
    

    var p := CPacket(cpacket.src, host.me, sm);
    if shouldSend {
        sent_packets := [p];
    } else {
        sent_packets := [];
    }

    ghost var s := AbstractifyHostStateToHost(host);
    ghost var s' := AbstractifyHostStateToHost(host');
    ghost var g_m := AbstractifyCMessageToRslMessage(m);
    ghost var g_sm := AbstractifyCSingleMessageToSingleMessage(sm);
    ghost var g_src := AbstractifyEndPointToNodeIdentity(cpacket.src);
    ghost var g_seqno := cpacket.msg.seqno as int;
    ghost var g_out := AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets);
    
    lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
    reveal_AbstractifySeqOfCPacketsToSetOfShtPackets();
    assert AbstractifyCPacketToShtPacket(p) == Packet(g_src, s.me, g_sm); // OBSERVE
    assert NextSetRequest_Complete(s, s', g_src, g_seqno, AbstractifyCMessageToRslMessage(cpacket.msg.m), g_sm, g_m, g_out, shouldSend);
}

predicate HostIgnoringUnParseable(host:Host, host':Host, packets:set<Packet>)
{
    packets == {}
 && host' == host.(receivedPacket := None)
 && host.receivedPacket.Some? 
 && host.receivedPacket.v.msg.SingleMessage? 
 && host.receivedPacket.v.msg.m.Delegate?
 && var msg := host.receivedPacket.v.msg.m;
    !(ValidKeyRange(msg.range) && ValidHashtable(msg.h) && !EmptyKeyRange(msg.range))
}

method {:timeLimitMultiplier 4} HostModelNextDelegate(host:HostState, cpacket:CPacket) returns (host':HostState, sent_packets:seq<CPacket>)
    requires NextDelegatePreconditions(host, cpacket);
    requires CSingleMessageIs64Bit(cpacket.msg);
    requires host.receivedPacket.Some? && host.receivedPacket.v == cpacket;
    requires host.numDelegations < host.constants.params.max_delegations - 2;
    ensures NextDelegatePostconditions(host, cpacket, host', sent_packets);
    ensures NextDelegate(AbstractifyHostStateToHost(host), AbstractifyHostStateToHost(host'), 
                         AbstractifyCPacketToShtPacket(cpacket), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets)) 
            || HostIgnoringUnParseable(AbstractifyHostStateToHost(host), AbstractifyHostStateToHost(host'), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets));
{   
    sent_packets := [];
    reveal_AbstractifySeqOfCPacketsToSetOfShtPackets();

    var marshallable := IsCSingleMessageMarshallable(cpacket.msg);
    if !marshallable {
        host' := host.(receivedPacket := None);
        assert HostIgnoringUnParseable(AbstractifyHostStateToHost(host), AbstractifyHostStateToHost(host'), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets));
        return;
    }
   
    if cpacket.src in host.constants.hostIds {
        var ok, delegationMap' := UpdateCDelegationMap(host.delegationMap, cpacket.msg.m.range, host.me);
        var h' := BulkUpdateHashtable(host.h, cpacket.msg.m.range, cpacket.msg.m.h);
        host' := host.(h := h', delegationMap := delegationMap', receivedPacket := None, numDelegations := host.numDelegations + 1);
    } else {
        host' := host.(receivedPacket := None);
    }
    lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
    //reveal_AbstractifySeqOfCPacketsToSetOfShtPackets();
}

method {:timeLimitMultiplier 4} HostModelNextShard(host:HostState, cpacket:CPacket) returns (host':HostState, sent_packets:seq<CPacket>)
    requires NextShardPreconditions(host, cpacket);
    requires host.numDelegations < host.constants.params.max_delegations - 2;
    ensures NextShardPostconditions(host, cpacket, host', sent_packets);
{ 
    var recipient := cpacket.msg.m.recipient;
    var kr := cpacket.msg.m.kr;
    sent_packets := [];
    host' := host.(receivedPacket := None);
    lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
    reveal_AbstractifySeqOfCPacketsToSetOfShtPackets();
    var marshallable := IsMessageMarshallable(cpacket.msg.m);
    if (!marshallable || cpacket.msg.m.recipient == host.me || cpacket.msg.m.recipient !in host.constants.hostIds) {
        assert EndPointIsAbstractable(cpacket.msg.m.recipient);
        return;
    }
        
    var b:= DelegateForKeyRangeIsHostImpl(host.delegationMap, cpacket.msg.m.kr, host.me);
    if (!b) {
        assert !DelegateForKeyRangeIsHost(AbstractifyCDelegationMapToDelegationMap(host.delegationMap), cpacket.msg.m.kr, AbstractifyEndPointToNodeIdentity(host.me));
        return;
    }

    var h := ExtractRange(host.h, cpacket.msg.m.kr);
    if (|h| >= 62) { // max_hashtable_size()
        return;
    }

    var m := CDelegate(kr, ExtractRange(host.h, kr));
    
    var sd', sm, shouldSend := SendSingleCMessage(host.sd, m, recipient, host.constants.params);
    var p;    
    
    if shouldSend {
        var ok, delegationMap' := UpdateCDelegationMap(host.delegationMap, kr, recipient);
        var h' := BulkRemoveHashtable(host.h, kr);
    
        host' := host.(h := h', delegationMap := delegationMap', sd := sd', receivedPacket := None, numDelegations := host.numDelegations + 1);

        p := CPacket(recipient, host.me, sm);
        sent_packets := [p];
        
    } else {
        host' := host.(receivedPacket := None, numDelegations := host.numDelegations + 1);
        sent_packets := [];
    }
  
    
    ghost var s := AbstractifyHostStateToHost(host);
    ghost var s' := AbstractifyHostStateToHost(host');
    ghost var g_sm := AbstractifyCSingleMessageToSingleMessage(sm);
    ghost var g_out := AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets);
    ghost var g_pkt := AbstractifyCPacketToShtPacket(cpacket);
        
    if shouldSend {
        assert AbstractifyCPacketToShtPacket(p) == Packet(AbstractifyEndPointToNodeIdentity(recipient), s.me, g_sm); // OBSERVE
        //assert g_out == { Packet(recipient, s.me, sm) }
    }
    
    assert NextShard(s, s', g_out, g_pkt.msg.m.kr, g_pkt.msg.m.recipient, g_sm, shouldSend); 
}


method {:timeLimitMultiplier 2} HostModelNextReceiveMessage(host:HostState, cpacket:CPacket)  returns (host':HostState, sent_packets:seq<CPacket>)
    requires cpacket.msg.CSingleMessage?;
    requires CSingleDeliveryAccountIsValid(host.sd, host.constants.params)
    requires CPacketIsAbstractable(cpacket);
    requires CSingleMessageIs64Bit(cpacket.msg);
    requires host.receivedPacket.Some? && host.receivedPacket.v == cpacket;
    requires HostState_common_preconditions(host, cpacket);
    requires cpacket.msg.m.CGetRequest? ==> NextGetRequestPreconditions(host, cpacket);
    requires cpacket.msg.m.CSetRequest? ==> NextSetRequestPreconditions(host, cpacket) 
    requires cpacket.msg.m.CDelegate? ==> NextDelegatePreconditions(host, cpacket) && (host.numDelegations < host.constants.params.max_delegations - 2);
    requires cpacket.msg.m.CShard? ==> NextShardPreconditions(host, cpacket) && (host.numDelegations < host.constants.params.max_delegations - 2);

    ensures HostStateIsAbstractable(host');
    ensures CPacketSeqIsAbstractable(sent_packets);
    ensures HostState_common_postconditions(host, cpacket, host', sent_packets)
    ensures  Process_Message(AbstractifyHostStateToHost(host), AbstractifyHostStateToHost(host'), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets))
          || HostIgnoringUnParseable(AbstractifyHostStateToHost(host), AbstractifyHostStateToHost(host'), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets));
    ensures AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets) == ExtractPacketsFromLSHTPackets(AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets));
    ensures host'.receivedPacket.None?
{
    if (cpacket.msg.CInvalidMessage?) {
        host' := host;
        sent_packets := [];
    } else if (cpacket.msg.m.CGetRequest?) {
        host', sent_packets := HostModelNextGetRequest(host, cpacket);
        assert NextGetRequest(AbstractifyHostStateToHost(host), AbstractifyHostStateToHost(host'), AbstractifyCPacketToShtPacket(cpacket), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets));
    } else if (cpacket.msg.m.CSetRequest?) {
        host', sent_packets := HostModelNextSetRequest(host, cpacket);
    } else if (cpacket.msg.m.CDelegate?) {
        host', sent_packets := HostModelNextDelegate(host, cpacket);
    } else if (cpacket.msg.m.CShard?) {
        host', sent_packets := HostModelNextShard(host, cpacket);
    } else if (cpacket.msg.m.CReply? || cpacket.msg.m.CRedirect?) {
        host' := host.(receivedPacket := None);
        sent_packets := [];
        assert |sent_packets| == 0;
        reveal_AbstractifySeqOfCPacketsToSetOfShtPackets();
        assert |AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets)| == |sent_packets|;
        assert AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets) == {};
    } else {
        assert false;
    }
    
 }

method ShouldProcessReceivedMessageImpl(s:HostState) returns (b:bool)
    requires HostStateIsValid(s)
    ensures b == ShouldProcessReceivedMessage(AbstractifyHostStateToHost(s))
{
    if (   s.receivedPacket.Some?
        && s.receivedPacket.v.msg.CSingleMessage?
        && ((s.receivedPacket.v.msg.m.CDelegate? || s.receivedPacket.v.msg.m.CShard?) ==> s.numDelegations < s.constants.params.max_delegations - 2)) {
        b := true;
    } else {
        b := false;
    }
}

method HostModelReceivePacket(host:HostState, cpacket:CPacket) returns (host':HostState, sent_packets:seq<CPacket>, ack:CPacket)
    requires HostStateIsValid(host)
    requires CSingleDeliveryAccountIsValid(host.sd, host.constants.params)
    requires CPacketIsAbstractable(cpacket) && CSingleMessageIs64Bit(cpacket.msg) && !cpacket.msg.CInvalidMessage?; // CSingleMessageMarshallable(pkt.msg); 
    requires !cpacket.msg.CInvalidMessage?;
    requires HostState_common_preconditions(host, cpacket);
    requires cpacket.dst == host.me;
    ensures HostStateIsValid(host');
    ensures HostStateIsValid(host') && OutboundPacketsSeqIsValid(sent_packets)
    ensures CPacketIsAbstractable(ack);
    ensures ReceivePacket(AbstractifyHostStateToHost(host), AbstractifyHostStateToHost(host'), AbstractifyCPacketToShtPacket(cpacket), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets), AbstractifyCPacketToShtPacket(ack))
    ensures OutboundPacketsSeqIsValid(sent_packets);
    ensures HostState_common_postconditions(host, cpacket, host', sent_packets);
    ensures |sent_packets| >= 1 ==> sent_packets == [ack];
    ensures sent_packets == [] ==> ack == cpacket;
{
    sent_packets := [];
    
    reveal_AbstractifySeqOfCPacketsToSetOfShtPackets();
    
    if (host.receivedPacket.None?) {
        var b, sd';
        b, sd', ack := ReceiveSingleMessageImpl(host.sd, cpacket, host.constants.params);
        
        
        if (b) {
            var b' := NewSingleMessageImpl(host.sd, cpacket, host.constants.params);
            sent_packets := [ack];        
            
            if (b') {
                host' := host.(receivedPacket := Some(cpacket), sd := sd');
            } else {
                host' := host.(receivedPacket := None, sd := sd');
            }
            
        } else {
            host' := host.(sd := sd');
            ack := cpacket;
            sent_packets := [];
        }
    } else {
        host' := host;
        ack := cpacket;
    }

}

method {:timeLimitMultiplier 2} HostModelSpontaneouslyRetransmit(host:HostState) returns (host':HostState, sent_packets:seq<CPacket>)
    requires SpontaneouslyRetransmitPreconditions(host);
    ensures SpontaneouslyRetransmitPostconditions(host, host', sent_packets);
    ensures UnAckedMessages(AbstractifyHostStateToHost(host).sd, AbstractifyHostStateToHost(host).me) == ExtractPacketsFromLSHTPackets(AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets));
{ 
    host' := host;
    sent_packets := RetransmitUnAckedPackets(host.sd, host.me, host.constants.params);


    assert AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets) == UnAckedMessages(AbstractifyHostStateToHost(host).sd, AbstractifyHostStateToHost(host).me);
    
    reveal_AbstractifySeqOfCPacketsToSetOfShtPackets();
    
    assert forall p :: p in sent_packets ==> AbstractifyCPacketToShtPacket(p) in AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets);
    assert forall p :: p in sent_packets ==> AbstractifyCPacketToShtPacket(p) in ExtractPacketsFromLSHTPackets(AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets));
    
    ghost var sent_packets' := AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets);
    
    lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
    assert forall p :: p in sent_packets ==> CPacketIsAbstractable(p) && EndPointIsValidIPV4(p.dst) && EndPointIsValidIPV4(p.src);
    assert forall p :: p in sent_packets ==> LPacket(AbstractifyEndPointToNodeIdentity(p.dst), AbstractifyEndPointToNodeIdentity(p.src), AbstractifyCSingleMessageToSingleMessage(p.msg)) in sent_packets';
    
    assert forall p':: p' in sent_packets' ==> exists p :: p in sent_packets && LPacket(AbstractifyEndPointToNodeIdentity(p.dst), AbstractifyEndPointToNodeIdentity(p.src), AbstractifyCSingleMessageToSingleMessage(p.msg)) == p';
    assert AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets) == ExtractPacketsFromLSHTPackets(sent_packets');
    assert UnAckedMessages(AbstractifyHostStateToHost(host).sd, AbstractifyHostStateToHost(host).me) == ExtractPacketsFromLSHTPackets(AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets));
}
} 
