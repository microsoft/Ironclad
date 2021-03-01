include "InvDefs.i.dfy"

module SHT__InvProof_i {
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
import opened SHT__InvDefs_i
import opened SHT__Message_i
import opened SHT__SingleMessage_i
import opened Protocol_Parameters_i
import opened SHT__Configuration_i

lemma lemma_AllDelegationsToKnownHosts(s:SHT_State, k:Key, id:NodeIdentity, nextId:NodeIdentity)
    requires MapComplete(s);
    requires AllDelegationsToKnownHosts(s);
    requires id in AllHostIdentities(s);
    requires nextId == DelegateForKey(s.hosts[id].delegationMap, k);
    ensures nextId in AllHostIdentities(s);
{
    var dm := s.hosts[id].delegationMap;
}

predicate NoHostsStoreEmptyValues(s:SHT_State)
    requires MapComplete(s);
{
    forall id,k ::
        id in AllHostIdentities(s) && HostClaimsKey(s.hosts[id], k) && k in s.hosts[id].h
        ==> HashtableLookup(s.hosts[id].h, k) != ValueAbsent()
}

predicate BufferedDelegationPacketPresent(pkt:Option<Packet>)
    requires DelegationPacket(pkt);
{
    forall k {:trigger HashtableLookup(pkt.v.msg.m.h, k) }:: 
        k in pkt.v.msg.m.h ==> HashtableLookup(pkt.v.msg.m.h, k) != ValueAbsent()
}

predicate BufferedPacketsInv(s:SHT_State)
    requires MapComplete(s);
{
    forall id :: id in AllHostIdentities(s) ==> 
        (s.hosts[id].receivedPacket.Some? ==> s.hosts[id].receivedPacket.v in s.network)
         &&
        (s.hosts[id].receivedPacket.Some? ==> s.hosts[id].receivedPacket.v.dst == id)
         &&
        (DelegationPacket(s.hosts[id].receivedPacket) ==> BufferedDelegationPacketPresent(s.hosts[id].receivedPacket))
        
}

predicate DestinationsConsistent(s:SHT_State) 
    requires MapComplete(s);
{
    forall pkt :: pkt in s.network && pkt.msg.SingleMessage? && pkt.src in AllHostIdentities(s)
        ==> pkt.msg.dst == pkt.dst
}

predicate DelegationMessagesCarryNoEmptyValues(s:SHT_State)
{
    forall pkt, k :: pkt in s.network && pkt.msg.SingleMessage? && pkt.msg.m.Delegate? && k in pkt.msg.m.h
        ==> HashtableLookup(pkt.msg.m.h, k) != ValueAbsent()
}

predicate DelegationMessagesCarryOnlyClaimedKeys(s:SHT_State)
    requires MapComplete(s);
{
    forall pkt, k :: pkt in s.network && pkt.src in AllHostIdentities(s)
                  && pkt.msg.SingleMessage? && pkt.msg.m.Delegate? && k in pkt.msg.m.h
                  ==> KeyRangeContains(pkt.msg.m.range, KeyPlus(k))
}

//////////////////////////////////////////////////////////////////////////////
// EachKeyClaimedInExactlyOnePlace (one Host or one Packet)

predicate SomeHostClaimsKey(s:SHT_State, k:Key)
    requires MapComplete(s);
{
   exists id
        {:trigger HostClaimsKey(s.hosts[id], k)}
        :: id in AllHostIdentities(s) && HostClaimsKey(s.hosts[id], k)
}

predicate OnlyOneHostClaimsKey(s:SHT_State, k:Key)
    requires MapComplete(s);
{
    forall i1,i2
        {:trigger HostClaimsKey(s.hosts[i1], k), HostClaimsKey(s.hosts[i2], k)}
        ::
           i1 in AllHostIdentities(s) && HostClaimsKey(s.hosts[i1], k)
        && i2 in AllHostIdentities(s) && HostClaimsKey(s.hosts[i2], k)
        ==> i1==i2
}

predicate UniqueHostClaimsKey(s:SHT_State, k:Key)
    requires MapComplete(s);
{
    SomeHostClaimsKey(s,k) && OnlyOneHostClaimsKey(s,k)
}

predicate NoHostClaimsKey(s:SHT_State, k:Key)
    requires MapComplete(s);
{
    forall id
        {:trigger HostClaimsKey(s.hosts[id], k)}
        :: id in AllHostIdentities(s) ==> !HostClaimsKey(s.hosts[id], k)
}

predicate SomePacketClaimsKey(s:SHT_State, k:Key)
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
{
    exists pkt
        {:trigger InFlightPacketClaimsKey(s, pkt, k)}
        :: InFlightPacketClaimsKey(s, pkt, k)
}

predicate OnlyOnePacketClaimsKey(s:SHT_State, k:Key)
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
{
    forall p1,p2
//            {:trigger InFlightPacketClaimsKey(s, p1, k), InFlightPacketClaimsKey(s, p2, k)}
            {:auto_trigger}
            :: InFlightPacketClaimsKey(s, p1, k) && InFlightPacketClaimsKey(s, p2, k) ==> p1==p2
}

predicate UniqueInFlightPacketClaimsKey(s:SHT_State, k:Key)
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
{
    SomePacketClaimsKey(s, k) && OnlyOnePacketClaimsKey(s, k)
}

predicate NoInFlightPacketClaimsKey(s:SHT_State, k:Key)
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
{
    forall pkt
        {:trigger InFlightPacketClaimsKey(s, pkt, k)}
        :: !InFlightPacketClaimsKey(s, pkt, k)
}

// Lots of exists in here seem to make this a brittle invariant to expose.
predicate {:opaque} EachKeyClaimedInExactlyOnePlace(s:SHT_State)
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
{
    forall k ::
           (UniqueInFlightPacketClaimsKey(s, k) && NoHostClaimsKey(s, k))
        || (NoInFlightPacketClaimsKey(s, k) && UniqueHostClaimsKey(s, k))
}

//////////////////////////////////////////////////////////////////////////////

predicate InvConstants(s:SHT_State)
    requires MapComplete(s);
{
    forall id {:auto_trigger} :: id in AllHostIdentities(s)
        ==> s.hosts[id].me == id && s.hosts[id].constants.hostIds == s.config.hostIds
}

predicate HostsStoreOnlyOwnedKeys(s:SHT_State)
    requires MapComplete(s);
{
    forall id,k :: id in AllHostIdentities(s) && k in s.hosts[id].h
        ==> HostClaimsKey(s.hosts[id], k)
}

predicate {:opaque} PacketsHaveSenderUniqueSeqnos(s:SHT_State)
    requires MapComplete(s);
{
    forall p1,p2 ::
        p1 in s.network && p2 in s.network
        && p1.msg.SingleMessage? && p2.msg.SingleMessage? 
        && p1.src == p2.src && p1.dst == p2.dst
        && p1.src in AllHostIdentities(s) && p1.dst in AllHostIdentities(s)
        && p2.src in AllHostIdentities(s) && p2.dst in AllHostIdentities(s)
        && p1.msg.seqno == p2.msg.seqno
        ==> p1 == p2
}

// Need this invariant to prove ReceiverHasCanceledNoUnsentSeqnos
predicate NoPacketContainsUnsentSeqno(s:SHT_State)
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
{
    forall pkt :: pkt in s.network && pkt.msg.SingleMessage? 
               && pkt.src in AllHostIdentities(s) && pkt.dst in AllHostIdentities(s)
        ==> pkt.msg.seqno <= HighestSeqnoSent(s.hosts[pkt.src].sd, pkt.dst)
}

// Need this invariant to ensure that, at the moment we send a packet,
// it isn't DOA because the recipient had inflated his receive seqno
predicate ReceiverHasNotCanceledUnsentSeqno(s:SHT_State, dst:NodeIdentity, src:NodeIdentity, seqno:int)
    requires MapComplete(s);
{
       dst in AllHostIdentities(s)
    && src in AllHostIdentities(s)
    && HighestSeqnoSent(s.hosts[src].sd, dst) < seqno
    ==> seqno > TombstoneTableLookup(src, s.hosts[dst].sd.receiveState)
}

predicate ReceiverHasCanceledNoUnsentSeqnos(s:SHT_State)
    requires MapComplete(s);
{
    forall dst, src, seqno :: ReceiverHasNotCanceledUnsentSeqno(s, dst, src, seqno)
}

///////////////////////////////////////////////////////
//      The ultimate invariant
//////////////////////////////////////////////////////

predicate Inv(s:SHT_State)
{
       MapComplete(s)
    && InvConstants(s)
    && AckListsInv(s)
    && AllDelegationsToKnownHosts(s)
    && HostsStoreOnlyOwnedKeys(s)
    && BufferedPacketsInv(s)
    && DestinationsConsistent(s)
    && NoHostsStoreEmptyValues(s)
    && DelegationMessagesCarryNoEmptyValues(s)
    && DelegationMessagesCarryOnlyClaimedKeys(s)
    && PacketsHaveSaneHeaders(s)
    && PacketsHaveSenderUniqueSeqnos(s)
//    && NoHostClaimsInFlightKeys(s)
    && NoPacketContainsUnsentSeqno(s)
    && ReceiverHasCanceledNoUnsentSeqnos(s)
    && EachKeyClaimedInExactlyOnePlace(s)
}

predicate {:opaque} HiddenInv(s:SHT_State)
{
    Inv(s)
}

///////////////////////////////////////////////////////
//      AckList 
//////////////////////////////////////////////////////

lemma TruncateAckPreservesUnAckListProperties<MT>(unAcked:seq<SingleMessage<MT>>, old_seqno:nat, new_seqno:nat, id:NodeIdentity)
    requires forall i :: 0 <= i < |unAcked| ==> unAcked[i].SingleMessage?
    requires forall i, j :: 0 <= i && j == i + 1 && j < |unAcked|
                ==> unAcked[i].seqno + 1 == unAcked[j].seqno;
    requires |unAcked| > 0 ==> unAcked[0].seqno == old_seqno + 1;
    requires new_seqno >= old_seqno;
    requires forall i :: 0 <= i < |unAcked| ==> unAcked[i].dst == id;
    ensures  var truncated := TruncateUnAckList(unAcked, new_seqno);
             forall i :: 0 <= i < |truncated| ==> truncated[i].SingleMessage?;
    ensures  var truncated := TruncateUnAckList(unAcked, new_seqno);
             forall i, j :: 0 <= i && j == i + 1 && j < |truncated|
                ==> truncated[i].seqno + 1 == truncated[j].seqno;
    ensures  var truncated := TruncateUnAckList(unAcked, new_seqno);
             |truncated| > 0 ==> truncated[0].seqno == new_seqno + 1;
    ensures  var truncated := TruncateUnAckList(unAcked, new_seqno);
             |unAcked| - |truncated| <= new_seqno - old_seqno;
    ensures  var truncated := TruncateUnAckList(unAcked, new_seqno);
             forall i :: 0 <= i < |truncated| ==> truncated[i].dst == id;
{
    assert |unAcked| > 0 ==> unAcked[0].SingleMessage?;
    if |unAcked| > 0 && unAcked[0].SingleMessage? && unAcked[0].seqno <= new_seqno {
        TruncateAckPreservesUnAckListProperties(unAcked[1..], old_seqno + 1, new_seqno, id);
    } else {
        if |unAcked| == 0 {
        } else {
            assert unAcked[0].seqno > new_seqno;
        }
    }
}

lemma TruncateAckPreservesSubset<MT>(unAcked:seq<SingleMessage<MT>>)
    ensures  forall m, seqno:nat :: var truncated := TruncateUnAckList(unAcked, seqno);
                                    m in truncated ==> m in unAcked;
{
    forall m, seqno:nat | var truncated := TruncateUnAckList(unAcked, seqno);
                          m in truncated 
        ensures m in unAcked;
    {
                          
    }
    
}

lemma UnAckedListFinalEntry<MT>(unAcked:seq<SingleMessage<MT>>, old_seqno:nat)
    requires forall i :: 0 <= i < |unAcked| ==> unAcked[i].SingleMessage?
    requires forall i, j :: 0 <= i && j == i + 1 && j < |unAcked|
                ==> unAcked[i].seqno + 1 == unAcked[j].seqno
    requires |unAcked| > 0 ==> unAcked[0].seqno == old_seqno + 1;
    ensures  |unAcked| > 0 ==> unAcked[|unAcked|-1].seqno == old_seqno + |unAcked|;
{
    if |unAcked| == 0 {
    } else {
        UnAckedListFinalEntry(unAcked[1..], old_seqno+1);
    }
}

lemma SendSingleMessagePreservesUnAckListProperties<MT>(s:SingleDeliveryAcct, s':SingleDeliveryAcct, m:MT, sm:SingleMessage<MT>, params:Parameters, shouldSend:bool)
    requires UnAckedListProperties(s);
    requires ReceiveNoMessage(s, s');
    requires SendSingleMessage(s, s', m, sm, params, shouldSend);
    ensures  UnAckedListProperties(s');
{
    // Prove NoAcksInUnAckedLists
    assert forall id :: var unAcked := AckStateLookup(id, s.sendState).unAcked;
                        forall i :: 0 <= i < |unAcked| ==> unAcked[i].SingleMessage?;
    forall id 
        ensures var unAcked := AckStateLookup(id, s'.sendState).unAcked;
                forall i :: 0 <= i < |unAcked| ==> unAcked[i].SingleMessage?;
    {
        var unAcked := AckStateLookup(id, s'.sendState).unAcked;
        if sm.dst == id {
            assert shouldSend ==> unAcked == AckStateLookup(id, s.sendState).unAcked + [ sm ]; // OBSERVE: Key fact, I think
        } else {
            assert unAcked == AckStateLookup(id, s.sendState).unAcked; 
        }
    }

    // Prove UnAckedListsSequential
    forall id 
        ensures var unAcked := AckStateLookup(id, s'.sendState).unAcked;
                forall i, j :: 0 <= i && j == i + 1 && j < |unAcked|
                    ==> unAcked[i].seqno + 1 == unAcked[j].seqno
    {
        var numPacketsAcked := AckStateLookup(id, s.sendState).numPacketsAcked;
        var unAcked  := AckStateLookup(id, s.sendState).unAcked;
        var unAcked' := AckStateLookup(id, s'.sendState).unAcked;
        if sm.dst == id {
            assert shouldSend ==> unAcked' == unAcked + [ sm ];
            if unAcked == [] {
            } else {
                assert unAcked[0].seqno == numPacketsAcked+1;
                UnAckedListFinalEntry(unAcked, numPacketsAcked);
                assert unAcked[|unAcked|-1].seqno == numPacketsAcked+1+|unAcked|-1;
            }
            assert shouldSend ==> sm.seqno == numPacketsAcked + |unAcked| + 1;
        } else {
            assert unAcked' == unAcked; 
        }
    }

    // Prove UnAckedListExceedsNumPacketsAcked
    forall id 
        ensures var ackState := AckStateLookup(id, s'.sendState);
                |ackState.unAcked| > 0 ==> ackState.unAcked[0].seqno == ackState.numPacketsAcked + 1;
        ensures var ackState := AckStateLookup(id, s'.sendState);
                forall i :: 0 <= i < |ackState.unAcked| ==> ackState.unAcked[i].dst == id;
    {
        var unAcked  := AckStateLookup(id, s.sendState).unAcked;
        var unAcked' := AckStateLookup(id, s'.sendState).unAcked;

        if sm.dst == id {
            assert shouldSend ==> unAcked' == unAcked + [ sm ]; // OBSERVE: Key fact, I think
        } else {
            assert unAcked' == unAcked; 
        }
        

    }

}

lemma ReceiveAckPreservesUnAckListProperties(s:SingleDeliveryAcct, s':SingleDeliveryAcct, pkt:Packet, acks:set<Packet>)
    requires UnAckedListProperties(s);
    requires pkt.msg.Ack?;
    requires ReceiveAck(s, s', pkt, acks);
    ensures  UnAckedListProperties(s');
{
    var oldAckState := AckStateLookup(pkt.src, s.sendState);
    var newAckState := AckStateLookup(pkt.src, s'.sendState);
    if pkt.msg.ack_seqno > oldAckState.numPacketsAcked {
        TruncateAckPreservesUnAckListProperties(oldAckState.unAcked, oldAckState.numPacketsAcked, pkt.msg.ack_seqno, pkt.src);
        assert forall id :: id != pkt.src ==>                               // OBSERVE
            var unAcked :=  AckStateLookup(id, s.sendState ).unAcked;
            var unAcked' := AckStateLookup(id, s'.sendState).unAcked;
            unAcked == unAcked';
    } else {
    }
}

lemma HighestSeqnoSent_Monotonic(s:SingleDeliveryAcct, s':SingleDeliveryAcct, pkt:Packet, acks:set<Packet>)
    requires UnAckedListProperties(s);
    requires pkt.msg.Ack?;
    requires ReceiveAck(s, s', pkt, acks);
    ensures  forall dst :: HighestSeqnoSent(s', dst) >= HighestSeqnoSent(s, dst);
{
    ReceiveAckPreservesUnAckListProperties(s, s', pkt, acks);

    forall dst 
        ensures HighestSeqnoSent(s', dst) >= HighestSeqnoSent(s, dst);
    {
        if dst != pkt.src {
            assert HighestSeqnoSent(s', dst) == HighestSeqnoSent(s, dst);
        } else {
            var oldAckState := AckStateLookup(dst, s.sendState);

            if pkt.msg.ack_seqno > oldAckState.numPacketsAcked {
                var newAckState := oldAckState.(numPacketsAcked := pkt.msg.ack_seqno,
                                              unAcked := TruncateUnAckList(oldAckState.unAcked, pkt.msg.ack_seqno));
                assert s'.sendState[dst] == newAckState;
                TruncateAckPreservesUnAckListProperties(oldAckState.unAcked, oldAckState.numPacketsAcked, pkt.msg.ack_seqno, dst);
                calc {
                    HighestSeqnoSent(s, dst);
                    oldAckState.numPacketsAcked + |oldAckState.unAcked|;
                    <=  
                    newAckState.numPacketsAcked + |newAckState.unAcked|;
                    HighestSeqnoSent(s', dst);
                }
            } else {
            }
        }
    }
    var oldAckState := AckStateLookup(pkt.src, s.sendState);
}


lemma ReceivePacket_UnsentSeqnos(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, rpkt:Packet, out:set<Packet>, ack:Packet)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires ReceivePacket(s.hosts[id], s'.hosts[id], rpkt, out, ack);
    requires s.hosts[id].receivedPacket.None?;
    requires rpkt in recv;
    ensures ReceiverHasCanceledNoUnsentSeqnos(s');
{
    var h := s.hosts[id];
    var h' := s'.hosts[id];

    assert ReceiveSingleMessage(h.sd, h'.sd, rpkt, ack, out);
    assert forall pkt :: pkt in s'.network && pkt.msg.SingleMessage?
               ==> pkt in s.network;
    assert NoPacketContainsUnsentSeqno(s);
    assert forall other_id :: other_id in AllHostIdentities(s) && other_id != id ==> s.hosts[other_id] == s'.hosts[other_id];
    reveal_PacketsHaveSenderUniqueSeqnos();

    // Prove ReceiverHasCanceledNoUnsentSeqnos(s')
    forall dst, src, seqno {:trigger ReceiverHasNotCanceledUnsentSeqno(s', dst, src, seqno)} | dst in AllHostIdentities(s') && src in AllHostIdentities(s')
                          && HighestSeqnoSent(s'.hosts[src].sd, dst) < seqno
        ensures seqno > TombstoneTableLookup(src, s'.hosts[dst].sd.receiveState);
    {
        assert ReceiverHasNotCanceledUnsentSeqno(s, dst, src, seqno);       // OBSERVE: Need to trigger to expand the definition
        var seqno_sent  := HighestSeqnoSent(s.hosts[src].sd, dst);
        var seqno_sent' := HighestSeqnoSent(s'.hosts[src].sd, dst);
        var seqno_recv  := TombstoneTableLookup(src, s.hosts[dst].sd.receiveState);
        var seqno_recv' := TombstoneTableLookup(src, s'.hosts[dst].sd.receiveState);

        assert forall i :: i in AllHostIdentities(s') && i != id ==> s'.hosts[i] == s.hosts[i];
        //assert rpkt.src != rpkt.dst;
        if src != id {
            assert seqno_sent == seqno_sent';
        } else {
            assert src == id == rpkt.dst;
            var oldAckState := AckStateLookup(dst, h.sd.sendState);
            var ackState' := AckStateLookup(dst, h'.sd.sendState);
            assert seqno_sent' == ackState'.numPacketsAcked + |ackState'.unAcked|;
            if rpkt.msg.Ack? && ReceiveAck(h.sd, h'.sd, rpkt, out) {
                if dst != rpkt.src {
                    assert seqno_sent' == seqno_sent;
                } else {
                    HighestSeqnoSent_Monotonic(h.sd, h'.sd, rpkt, out);
                    if rpkt.msg.ack_seqno > oldAckState.numPacketsAcked {
                        assert seqno_sent' >= seqno_sent;
                    } else {
                        assert seqno_sent' == seqno_sent;
                    }
                    assert seqno_sent' >= seqno_sent;
                }
            } else {
                assert h'.sd.sendState == h.sd.sendState;
                assert seqno_sent' == seqno_sent;
            }
        }

        if NewSingleMessage(h.sd, rpkt) {
            if rpkt.src == src && dst == id {
                assert seqno_recv' == seqno_recv + 1;
            } else {
                assert seqno_recv' == seqno_recv;
            }
        } else {
            assert seqno_recv == seqno_recv';
        }

        assert seqno > seqno_recv';
    }
}

lemma ReceivePacket_EachKeyClaimed(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, rpkt:Packet, out:set<Packet>, ack:Packet)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires ReceivePacket(s.hosts[id], s'.hosts[id], rpkt, out, ack);
    requires s.hosts[id].receivedPacket.None?;
    requires rpkt in recv;
    ensures EachKeyClaimedInExactlyOnePlace(s');
{
    var h := s.hosts[id];
    var h' := s'.hosts[id];

    assert ReceiveSingleMessage(h.sd, h'.sd, rpkt, ack, out);

    if NewSingleMessage(h.sd, rpkt) {
        assert h' == h.(sd := h'.sd, receivedPacket := Some(rpkt));
    } else {
        assert h' == h.(sd := h'.sd, receivedPacket := None);
    }

    // Prove EachKeyClaimedInExactlyOnePlace(s');
    forall () ensures EachKeyClaimedInExactlyOnePlace(s');
    {
        reveal_EachKeyClaimedInExactlyOnePlace();
        assert forall k :: (UniqueInFlightPacketClaimsKey(s, k) && NoHostClaimsKey(s, k))
                        || (NoInFlightPacketClaimsKey(s, k) && UniqueHostClaimsKey(s, k));
        forall k 
            ensures (UniqueInFlightPacketClaimsKey(s', k) && NoHostClaimsKey(s', k))
                 || (NoInFlightPacketClaimsKey(s', k) && UniqueHostClaimsKey(s', k))
        {
            if UniqueInFlightPacketClaimsKey(s, k) {
                assert exists pkt :: InFlightPacketClaimsKey(s, pkt, k);        // OBSERVE
                var pkt :| InFlightPacketClaimsKey(s, pkt, k);        
                var last_seqno :=  TombstoneTableLookup(pkt.src, s.hosts[pkt.dst].sd.receiveState);
                var last_seqno' := TombstoneTableLookup(pkt.src, s'.hosts[pkt.dst].sd.receiveState);
                assert pkt.msg.seqno > last_seqno;
                if pkt != rpkt {
                    assert pkt in s'.network;
                    if pkt.dst != id {
                        assert pkt.msg.SingleMessage? && pkt.msg.seqno > last_seqno';
                    } else {
                        if NewSingleMessage(h.sd, rpkt) {
                            assert h' == h.(sd := h'.sd, receivedPacket := Some(rpkt));
                            if rpkt.src == pkt.src {
                                forall () ensures pkt.msg.seqno != rpkt.msg.seqno; {
                                    reveal_PacketsHaveSenderUniqueSeqnos();
                                }
                                assert pkt.msg.SingleMessage? && pkt.msg.seqno > last_seqno';
                            } else {
                                assert pkt.msg.SingleMessage? && pkt.msg.seqno > last_seqno';
                            }
                        } else {
                            assert h' == h.(sd := h'.sd, receivedPacket := None);
                            assert pkt.msg.SingleMessage? && pkt.msg.seqno > last_seqno';
                        }
                    }
                    assert PacketInFlight(s', pkt);
                    assert InFlightPacketClaimsKey(s', pkt, k);    // OBSERVE, exists trigger for SomePacketClaimsKey(s, k)
                    assert forall p1,p2 {:auto_trigger} ::  // OBSERVE  for OnlyOnePacketClaimsKey(s', k)
                        InFlightPacketClaimsKey(s, p1, k) && InFlightPacketClaimsKey(s, p2, k) ==> p1==p2;
                    forall p1,p2 {:auto_trigger} | InFlightPacketClaimsKey(s', p1, k)   // OBSERVE for OnlyOnePacketClaimsKey(s', k)
                                                && InFlightPacketClaimsKey(s', p2, k)
                        ensures p1==p2;
                    {
                        assert InFlightPacketClaimsKey(s, p1, k) && InFlightPacketClaimsKey(s, p2, k); 
                    }
                    assert OnlyOnePacketClaimsKey(s', k);
                    assert UniqueInFlightPacketClaimsKey(s', k);

                    forall i {:trigger HostClaimsKey(s'.hosts[i], k)} | i in AllHostIdentities(s') 
                        ensures !HostClaimsKey(s'.hosts[i], k);        // OBSERVE for NoHostClaimsKey(s', k);
                    {
                        assert !HostClaimsKey(s.hosts[i], k);
                        assert !(DelegateForKey(s'.hosts[i].delegationMap, k)==s'.hosts[i].me);
                        if i != id {
                            assert !BufferedPacketClaimsKey(s'.hosts[i], k);
                        } else {
                            if s'.hosts[i].receivedPacket.None? {
                                assert !BufferedPacketClaimsKey(s'.hosts[i], k);
                            } else {
                                assert s'.hosts[i].receivedPacket == Some(rpkt);
                                if BufferedPacketClaimsKey(s'.hosts[i], k) {
                                    assert InFlightPacketClaimsKey(s, rpkt, k);
                                    assert false;
                                }
                                assert !BufferedPacketClaimsKey(s'.hosts[i], k);
                            }
                        }
                    }
                    assert NoHostClaimsKey(s', k);
                    assert UniqueInFlightPacketClaimsKey(s', k) && NoHostClaimsKey(s', k);
                } else {  // pkt == rpkt
                    assert !pkt.msg.Ack?;

                    if NewSingleMessage(s.hosts[id].sd, pkt) {
                        assert s'.hosts[id].receivedPacket.v == pkt;
                        var last_seqno := TombstoneTableLookup(pkt.src, h.sd.receiveState);
                        assert pkt.msg.seqno == last_seqno + 1;
                        assert h'.sd == h.sd.(receiveState := h.sd.receiveState[pkt.src := (last_seqno + 1) as nat_t]);
                        assert !NewSingleMessage(s'.hosts[id].sd, pkt);
                        assert BufferedPacketClaimsKey(s'.hosts[id], k);
                        assert HostClaimsKey(s'.hosts[id], k);
                        assert UniqueHostClaimsKey(s', k);

                        forall p 
                            ensures !InFlightPacketClaimsKey(s', p, k)
                        {
                            if p != pkt {
                                assert !InFlightPacketClaimsKey(s, p, k);
                                assert !InFlightPacketClaimsKey(s', p, k);
                            } else {
                                assert !PacketInFlight(s', p);
                                assert !InFlightPacketClaimsKey(s', p, k);
                            }
                        }
                        assert NoInFlightPacketClaimsKey(s', k) && UniqueHostClaimsKey(s', k);
                    } else {
                        assert PacketInFlight(s', pkt);
                        assert InFlightPacketClaimsKey(s', pkt, k);
                        assert NoHostClaimsKey(s', k);

                        forall p1,p2 {:auto_trigger} | InFlightPacketClaimsKey(s', p1, k) && InFlightPacketClaimsKey(s', p2, k) 
                            ensures p1==p2;
                        {
                            assert InFlightPacketClaimsKey(s, p1, k);
                            assert InFlightPacketClaimsKey(s, p2, k);
                        }
                        assert SomePacketClaimsKey(s', k) && OnlyOnePacketClaimsKey(s', k);

                        assert UniqueInFlightPacketClaimsKey(s', k) && NoHostClaimsKey(s', k);
                    }
                }
            } else if NoInFlightPacketClaimsKey(s, k) {
                forall pkt 
                    ensures !InFlightPacketClaimsKey(s', pkt, k);
                {
                    assert !InFlightPacketClaimsKey(s, pkt, k);
                }
                assert NoInFlightPacketClaimsKey(s', k);

                assert SomeHostClaimsKey(s, k);
                assert exists id :: id in AllHostIdentities(s) && HostClaimsKey(s.hosts[id], k);
                var i :| i in AllHostIdentities(s) && HostClaimsKey(s.hosts[i], k);
                assert HostClaimsKey(s'.hosts[i], k);

                forall i1,i2 | i1 in AllHostIdentities(s') && HostClaimsKey(s'.hosts[i1], k) 
                            && i2 in AllHostIdentities(s') && HostClaimsKey(s'.hosts[i2], k)
                    ensures i1==i2;
                {
                    if i1 == id {
                        if BufferedPacketClaimsKey(s'.hosts[i1], k) {
                            assert InFlightPacketClaimsKey(s, rpkt, k);
                            assert false;
                        } else {
                            assert HostClaimsKey(s.hosts[id], k);
                        }
                        assert HostClaimsKey(s.hosts[id], k);
                    } else {
                        assert HostClaimsKey(s.hosts[i1], k);
                    }

                    if i2 == id {
                        if BufferedPacketClaimsKey(s'.hosts[i2], k) {
                            assert InFlightPacketClaimsKey(s, rpkt, k);
                            assert false;
                        } else {
                            assert HostClaimsKey(s.hosts[id], k);
                        }
                        assert HostClaimsKey(s.hosts[id], k);
                    } else {
                        assert HostClaimsKey(s.hosts[i2], k);
                    }
                }
                assert SomeHostClaimsKey(s',k) && OnlyOneHostClaimsKey(s',k);
                assert UniqueHostClaimsKey(s', k);
            } else {
                assert false;       // Not a viable option
            }
        }
    }
}

lemma ReceivePacket_Properties(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, rpkt:Packet, out:set<Packet>, ack:Packet)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires ReceivePacket(s.hosts[id], s'.hosts[id], rpkt, out, ack);
    requires s.hosts[id].receivedPacket.None?;
    requires rpkt in recv;
    ensures AckListsInv(s');
    ensures PacketsHaveSenderUniqueSeqnos(s');
    ensures NoPacketContainsUnsentSeqno(s');
    ensures ReceiverHasCanceledNoUnsentSeqnos(s');
    ensures EachKeyClaimedInExactlyOnePlace(s');
{
    var h := s.hosts[id];
    var h' := s'.hosts[id];

    assert ReceiveSingleMessage(h.sd, h'.sd, rpkt, ack, out);
    assert forall pkt :: pkt in s'.network && pkt.msg.SingleMessage?
               ==> pkt in s.network;
    assert NoPacketContainsUnsentSeqno(s);
    assert forall other_id :: other_id in AllHostIdentities(s) && other_id != id ==> s.hosts[other_id] == s'.hosts[other_id];

    ReceivePacket_UnsentSeqnos(s, s', id, recv, rpkt, out, ack);
    ReceivePacket_EachKeyClaimed(s, s', id, recv, rpkt, out, ack);

    reveal_UnAckedListInNetwork();
    if rpkt.msg.Ack? {
        assert out == {};
        ReceiveAckPreservesUnAckListProperties(h.sd, h'.sd, rpkt, out);
        var oldAckState := AckStateLookup(rpkt.src, h.sd.sendState);
        var newAckState := AckStateLookup(rpkt.src, h'.sd.sendState);
        assert newAckState.unAcked == TruncateUnAckList(oldAckState.unAcked, rpkt.msg.ack_seqno);
        TruncateAckPreservesSubset(oldAckState.unAcked); 

        forall id',msg,dst | id'  in AllHostIdentities(s)
                         && msg in AckStateLookup(dst, s'.hosts[id'].sd.sendState).unAcked
                         && NoAcksInUnAckedLists(s'.hosts[id'].sd)
                         && dst == msg.dst
            ensures Packet(msg.dst, s'.hosts[id'].me, msg) in s'.network
        {
            var p := Packet(msg.dst, s'.hosts[id'].me, msg);
            if id' == id {
                assert msg in AckStateLookup(dst, s.hosts[id'].sd.sendState).unAcked;
                assert p in s'.network;
            } else {
                assert p in s'.network;
            }
        }

        HighestSeqnoSent_Monotonic(h.sd, h'.sd, rpkt, out);
        assert AckListsInv(s');
    } else {
    }

    reveal_PacketsHaveSenderUniqueSeqnos(); // ==>
    assert PacketsHaveSenderUniqueSeqnos(s');
}

/*
lemma ReceiveSingleMessageNew_Properties(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, rpkt:Packet, out:set<Packet>, ack:Packet)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires rpkt in recv;
    requires ReceivePacket(s.hosts[id], s'.hosts[id], rpkt, out, ack);
    requires NewSingleMessage(s.hosts[id].sd, rpkt);
    ensures ReceiverHasCanceledNoUnsentSeqnos(s');
{
    var h := s.hosts[id];
    var h' := s'.hosts[id];
    assert ReceiveSingleMessage(h.sd, h'.sd, rpkt, ack, out);
    assert forall other_id :: other_id in AllHostIdentities(s) && other_id != id ==> s.hosts[other_id] == s'.hosts[other_id];

    // Remind Dafny what ReceiverHasCanceledNoUnsentSeqnos(s) means for s
    forall dst, src, seqno 
        ensures dst in AllHostIdentities(s) && src in AllHostIdentities(s)
                                     && HighestSeqnoSent(s.hosts[src].sd, dst) < seqno
        ==> seqno > TombstoneTableLookup(src, s.hosts[dst].sd.receiveState);
    {
        assert ReceiverHasNotCanceledUnsentSeqno(s, dst, src, seqno);       // OBSERVE: Need to trigger to expand the definition
    }

    forall dst, src, seqno | dst in AllHostIdentities(s) && src in AllHostIdentities(s)
                             && HighestSeqnoSent(s'.hosts[src].sd, dst) < seqno
        ensures seqno > TombstoneTableLookup(src, s'.hosts[dst].sd.receiveState);
    {
        if rpkt.src == src {
        } else {
            if dst == id {
                assert HighestSeqnoSent(s'.hosts[src].sd, dst) == HighestSeqnoSent(s.hosts[src].sd, dst);   // OBSERVE
                assert seqno > TombstoneTableLookup(src, s'.hosts[dst].sd.receiveState);
            } else {
            }
        }
    }
}
*/

predicate DelegationPacketStable(s:SHT_State, s':SHT_State, id:NodeIdentity)
    requires id in s.hosts && id in s'.hosts;
    requires DelegationPacket(s.hosts[id].receivedPacket);
{
    s'.hosts[id].receivedPacket == s.hosts[id].receivedPacket
}

lemma DelegateStability(s:SHT_State, s':SHT_State)
    requires MapComplete(s) && InvConstants(s);
    requires MapComplete(s') && InvConstants(s');
    requires s.config == s'.config;
    requires forall id :: id in AllHostIdentities(s) && DelegationPacket(s.hosts[id].receivedPacket) 
                ==> DelegationPacketStable(s, s', id);
//              ==> s'.hosts[id].receivedPacket == s.hosts[id].receivedPacket
//               && NewSingleMessage(s.hosts[id].sd, s.hosts[id].receivedPacket.v) ==
//                  NewSingleMessage(s'.hosts[id].sd, s'.hosts[id].receivedPacket.v);
    requires forall id :: id in AllHostIdentities(s) && !DelegationPacket(s.hosts[id].receivedPacket) 
              ==> !DelegationPacket(s'.hosts[id].receivedPacket); 
    requires forall id :: id in AllHostIdentities(s)
             ==> s'.hosts[id].delegationMap == s.hosts[id].delegationMap;
    ensures forall id, k :: id in AllHostIdentities(s)
             ==> (HostClaimsKey(s.hosts[id], k) <==> HostClaimsKey(s'.hosts[id],k));
{
    forall id, k | id in AllHostIdentities(s)
        ensures HostClaimsKey(s.hosts[id], k) <==> HostClaimsKey(s'.hosts[id],k);
    {
        var h  := s.hosts[id];
        var h' := s'.hosts[id];
        
        if BufferedPacketClaimsKey(h, k) {
            assert BufferedPacketClaimsKey(h', k);
        }
        if BufferedPacketClaimsKey(h', k) {
            assert DelegationPacket(h.receivedPacket);
            assert KeyRangeContains(h.receivedPacket.v.msg.m.range, KeyPlus(k));
            assert BufferedPacketClaimsKey(h, k);
        }

        calc {
            HostClaimsKey(h, k);
            DelegateForKey(h.delegationMap,  k) == h.me || BufferedPacketClaimsKey(h, k);
            DelegateForKey(h.delegationMap,  k) == id || BufferedPacketClaimsKey(h, k);
            DelegateForKey(h'.delegationMap, k) == id || BufferedPacketClaimsKey(h', k);
            DelegateForKey(h'.delegationMap, k) == h'.me || BufferedPacketClaimsKey(h', k);
            HostClaimsKey(h', k);
        }
    }
}

///////////////////////////////////////////////////////
//      Delegation
//////////////////////////////////////////////////////

lemma DelegateStabilitySpecific(s:SHT_State, s':SHT_State, k:Key, id:NodeIdentity)
    requires MapComplete(s) && InvConstants(s);
    requires MapComplete(s') && InvConstants(s');
    requires NoConfigChanged(s, s');
    requires forall id :: id in AllHostIdentities(s) && DelegationPacket(s.hosts[id].receivedPacket) 
              ==> s'.hosts[id].receivedPacket == s.hosts[id].receivedPacket
               && NewSingleMessage(s.hosts[id].sd, s.hosts[id].receivedPacket.v) ==
                  NewSingleMessage(s'.hosts[id].sd, s'.hosts[id].receivedPacket.v);
    requires forall id :: id in AllHostIdentities(s) && !DelegationPacket(s.hosts[id].receivedPacket) 
              ==> s'.hosts[id].receivedPacket.None?; 
    requires forall id :: id in AllHostIdentities(s)
        ==> s'.hosts[id].delegationMap == s.hosts[id].delegationMap;
    requires id in AllHostIdentities(s);
    ensures HostClaimsKey(s.hosts[id], k) <==> HostClaimsKey(s'.hosts[id],k);
{
    DelegateStability(s, s');
}

// Trigger loop!?
lemma NoHostClaimsKeySpecific(s:SHT_State, k:Key, id:NodeIdentity)
    requires MapComplete(s);
    requires NoHostClaimsKey(s, k);
    requires id in AllHostIdentities(s);
    ensures !HostClaimsKey(s.hosts[id], k);
{
}

predicate NoDelegationPacketsChangedAboutKey(s:SHT_State, s':SHT_State, k:Key)
    requires MapComplete(s) && InvConstants(s) && PacketsHaveSaneHeaders(s);
    requires MapComplete(s') && InvConstants(s') && PacketsHaveSaneHeaders(s');
{
    forall pkt:Packet ::
        pkt.msg.SingleMessage? && pkt.msg.m.Delegate? && KeyRangeContains(pkt.msg.m.range, KeyPlus(k))
        ==> (PacketInFlight(s, pkt) <==> PacketInFlight(s', pkt))
}

predicate NoConfigChanged(s:SHT_State, s':SHT_State)
    requires MapComplete(s);
    requires MapComplete(s');
{
    s'.config == s.config
}


// TODO I think I can just dispense with this disjunct.
predicate NoDelegationMapsChanged(s:SHT_State, s':SHT_State)
    requires MapComplete(s);
    requires MapComplete(s');
    requires NoConfigChanged(s, s');
{
    forall id {:auto_trigger} :: id in AllHostIdentities(s)
        ==> s'.hosts[id].delegationMap == s.hosts[id].delegationMap
}

predicate NoDelegationMapsChangedAboutKey(s:SHT_State, s':SHT_State, k:Key)
    requires MapComplete(s);
    requires MapComplete(s');
    requires NoConfigChanged(s, s');
{
    forall id {:trigger DelegateForKey(s.hosts[id].delegationMap, k)} 
              {:trigger DelegateForKey(s'.hosts[id].delegationMap, k)} :: 
              id in AllHostIdentities(s) ==> 
                   DelegateForKey(s'.hosts[id].delegationMap, k)
                == DelegateForKey(s.hosts[id].delegationMap, k)
}

lemma NonDelegationsEachKeyClaimedInExactlyOnePlace_case1(s:SHT_State, s':SHT_State, k:Key)
    requires MapComplete(s) && InvConstants(s) && PacketsHaveSaneHeaders(s);
    requires MapComplete(s') && InvConstants(s') && PacketsHaveSaneHeaders(s');
    requires NoDelegationPacketsChangedAboutKey(s, s', k);
    requires NoConfigChanged(s, s');
    requires NoDelegationMapsChanged(s, s')
        || NoDelegationMapsChangedAboutKey(s, s', k);
    requires forall id :: id in AllHostIdentities(s) && DelegationPacket(s.hosts[id].receivedPacket) 
                ==> DelegationPacketStable(s, s', id) || s'.hosts[id].receivedPacket.None?;
    requires forall id :: id in AllHostIdentities(s) && !DelegationPacket(s.hosts[id].receivedPacket) 
              ==> !DelegationPacket(s'.hosts[id].receivedPacket); 
    requires UniqueInFlightPacketClaimsKey(s, k) && NoHostClaimsKey(s, k);
    ensures UniqueInFlightPacketClaimsKey(s', k) && NoHostClaimsKey(s', k);
{
    // Some unfortunate triggering required by new conservative triggers.
    // I'm not certain why.
//    assert exists pkt :: InFlightPacketClaimsKey(s, pkt, k);
    var pkt :| InFlightPacketClaimsKey(s, pkt, k);
    assert InFlightPacketClaimsKey(s', pkt, k);
    assert exists pkt :: InFlightPacketClaimsKey(s', pkt, k);

//    assert SomePacketClaimsKey(s', k);

    forall p1,p2
        | InFlightPacketClaimsKey(s', p1, k) && InFlightPacketClaimsKey(s', p2, k)
        ensures p1==p2;
    {
        assert InFlightPacketClaimsKey(s, p1, k);
        assert InFlightPacketClaimsKey(s, p2, k);
    }
//    assert OnlyOnePacketClaimsKey(s', k);
    assert forall id :: id in AllHostIdentities(s) ==> !HostClaimsKey(s.hosts[id], k);
}

// This was easy to prove until I tightened the precondition.
lemma NonDelegationsEachKeyClaimedInExactlyOnePlace_case2(s:SHT_State, s':SHT_State, k:Key)
    requires HiddenInv(s);
    requires MapComplete(s) && InvConstants(s) && PacketsHaveSaneHeaders(s);
    requires MapComplete(s') && InvConstants(s') && PacketsHaveSaneHeaders(s');
    requires NoDelegationPacketsChangedAboutKey(s, s', k);
    requires NoConfigChanged(s, s')
    requires forall id :: id in AllHostIdentities(s) && DelegationPacket(s.hosts[id].receivedPacket) 
                ==> DelegationPacketStable(s, s', id);
    requires forall id :: id in AllHostIdentities(s) && !DelegationPacket(s.hosts[id].receivedPacket) 
              ==> !DelegationPacket(s'.hosts[id].receivedPacket); 
    requires NoDelegationMapsChanged(s, s')
        || NoDelegationMapsChangedAboutKey(s, s', k);
    requires NoInFlightPacketClaimsKey(s, k) && UniqueHostClaimsKey(s, k);
    ensures NoInFlightPacketClaimsKey(s', k) && UniqueHostClaimsKey(s', k);
{
    if (NoDelegationMapsChanged(s, s')) {
        DelegateStability(s, s');
    }
//    assert NoInFlightPacketClaimsKey(s, k);
    assert forall pkt :: !InFlightPacketClaimsKey(s, pkt, k);
//    assert NoInFlightPacketClaimsKey(s', k);
    assert UniqueHostClaimsKey(s, k);
    var id :| id in AllHostIdentities(s) && HostClaimsKey(s.hosts[id], k);
    assert id in AllHostIdentities(s) && HostClaimsKey(s'.hosts[id], k);
    forall i1,i2 |
           i1 in AllHostIdentities(s) && HostClaimsKey(s'.hosts[i1], k)
        && i2 in AllHostIdentities(s) && HostClaimsKey(s'.hosts[i2], k)
        ensures i1==i2;
    {
        assert HostClaimsKey(s.hosts[i1], k);
        assert HostClaimsKey(s.hosts[i2], k);
        assert i1==i2;
    }
    assert UniqueHostClaimsKey(s', k);

    forall pkt ensures !InFlightPacketClaimsKey(s', pkt, k)
    {
        assert !InFlightPacketClaimsKey(s, pkt, k);
    }
    assert NoInFlightPacketClaimsKey(s', k);
}

lemma NonDelegationsEachKeyClaimedInExactlyOnePlace_case2'(s:SHT_State, s':SHT_State, k:Key)
    requires HiddenInv(s);
    requires MapComplete(s) && InvConstants(s) && PacketsHaveSaneHeaders(s);
    requires MapComplete(s') && InvConstants(s') && PacketsHaveSaneHeaders(s');
    requires NoDelegationPacketsChangedAboutKey(s, s', k);
    requires NoConfigChanged(s, s')
    requires forall id :: id in AllHostIdentities(s) && DelegationPacket(s.hosts[id].receivedPacket) 
              ==> s'.hosts[id].receivedPacket == s.hosts[id].receivedPacket || s'.hosts[id].receivedPacket.None?;
    requires forall id :: id in AllHostIdentities(s) && DelegationPacket(s.hosts[id].receivedPacket) 
              && s'.hosts[id].receivedPacket.None? ==> !BufferedPacketClaimsKey(s.hosts[id], k);
    requires forall id :: id in AllHostIdentities(s') ==> s'.hosts[id].sd == s.hosts[id].sd;
    requires forall id :: id in AllHostIdentities(s) && !DelegationPacket(s.hosts[id].receivedPacket) 
              ==> !DelegationPacket(s'.hosts[id].receivedPacket); 
    requires NoDelegationMapsChanged(s, s')
        || NoDelegationMapsChangedAboutKey(s, s', k);
    requires NoInFlightPacketClaimsKey(s, k) && UniqueHostClaimsKey(s, k);
    ensures NoInFlightPacketClaimsKey(s', k) && UniqueHostClaimsKey(s', k);
{
    assert forall pkt :: !InFlightPacketClaimsKey(s, pkt, k);
    assert UniqueHostClaimsKey(s, k);
    var id :| id in AllHostIdentities(s) && HostClaimsKey(s.hosts[id], k);
    assert id in AllHostIdentities(s) && HostClaimsKey(s'.hosts[id], k);
    forall i1,i2 |
           i1 in AllHostIdentities(s) && HostClaimsKey(s'.hosts[i1], k)
        && i2 in AllHostIdentities(s) && HostClaimsKey(s'.hosts[i2], k)
        ensures i1==i2;
    {
        assert HostClaimsKey(s.hosts[i1], k);
        assert HostClaimsKey(s.hosts[i2], k);
        assert i1==i2;
    }
    assert UniqueHostClaimsKey(s', k);

    forall pkt ensures !InFlightPacketClaimsKey(s', pkt, k)
    {
        assert !InFlightPacketClaimsKey(s, pkt, k);
    }
    assert NoInFlightPacketClaimsKey(s', k);
}

predicate NotADelegateStep(s:SHT_State, s':SHT_State)
    requires MapComplete(s);
    requires MapComplete(s');
    requires PacketsHaveSaneHeaders(s);
    requires PacketsHaveSaneHeaders(s');
{
    forall pkt:Packet :: pkt.msg.SingleMessage? && pkt.msg.m.Delegate?
        ==> (PacketInFlight(s, pkt) <==> PacketInFlight(s', pkt))
}

lemma NonDelegationsEachKeyClaimedInExactlyOnePlace(s:SHT_State, s':SHT_State)
    requires Inv(s);
    requires MapComplete(s) && InvConstants(s) && PacketsHaveSaneHeaders(s);
    requires MapComplete(s') && InvConstants(s') && PacketsHaveSaneHeaders(s');
    requires NoConfigChanged(s, s');
    requires NotADelegateStep(s, s');
    requires forall id :: id in AllHostIdentities(s)
        ==> s'.hosts[id].delegationMap == s.hosts[id].delegationMap;
    requires forall id :: id in AllHostIdentities(s) && DelegationPacket(s.hosts[id].receivedPacket) 
                ==> DelegationPacketStable(s, s', id);
    requires forall id :: id in AllHostIdentities(s) && !DelegationPacket(s.hosts[id].receivedPacket) 
              ==> !DelegationPacket(s'.hosts[id].receivedPacket); 
    ensures EachKeyClaimedInExactlyOnePlace(s');
{
    forall k
        ensures
           (UniqueInFlightPacketClaimsKey(s', k) && NoHostClaimsKey(s', k))
        || (NoInFlightPacketClaimsKey(s', k) && UniqueHostClaimsKey(s', k));
    {
        if (UniqueInFlightPacketClaimsKey(s, k) && NoHostClaimsKey(s, k)) {
            reveal_EachKeyClaimedInExactlyOnePlace();
            NonDelegationsEachKeyClaimedInExactlyOnePlace_case1(s, s', k);
        } else {
            reveal_EachKeyClaimedInExactlyOnePlace();
            reveal_HiddenInv();
            NonDelegationsEachKeyClaimedInExactlyOnePlace_case2(s, s', k);
        }
    }
    reveal_EachKeyClaimedInExactlyOnePlace();
    assert EachKeyClaimedInExactlyOnePlace(s');
}

lemma NextInv_Get_NotADelegateStep(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.GetRequest? && NextGetRequest(s.hosts[id], s'.hosts[id], rpkt, out);
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    ensures  NotADelegateStep(s, s');
{
}

lemma {:timeLimitMultiplier 3} NextInv_Get(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires s'.hosts[id].receivedPacket.None?;
    requires Some(rpkt) == s.hosts[id].receivedPacket;
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.GetRequest? && NextGetRequest(s.hosts[id], s'.hosts[id], rpkt, out);
    requires NotADelegateStep(s, s');
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    ensures Inv(s');
{
    var k := rpkt.msg.m.k_getrequest;
    var sm,m,b :| NextGetRequest_Reply(s.hosts[id], s'.hosts[id], rpkt.src, rpkt.msg.seqno, k, sm, m, out, b);
    
    if b {
        assert forall id' :: id' in AllHostIdentities(s) && id' != id 
                  ==> s'.hosts[id'] == s.hosts[id'];

        NonDelegationsEachKeyClaimedInExactlyOnePlace(s, s');

        assert SendSingleMessage(s.hosts[id].sd, s'.hosts[id].sd, m, sm, s.hosts[id].constants.params, b);    
        assert NoHostsStoreEmptyValues(s');

        reveal_PacketsHaveSenderUniqueSeqnos();
        reveal_UnAckedListInNetwork();

        forall dst, src, seqno ensures ReceiverHasNotCanceledUnsentSeqno(s', dst, src, seqno);
        {
            assert ReceiverHasNotCanceledUnsentSeqno(s, dst, src, seqno);   // OBSERVE trigger
        } // assert ReceiverHasCanceledNoUnsentSeqnos(s');

    
        SendSingleMessagePreservesUnAckListProperties(s.hosts[id].sd, s'.hosts[id].sd, m, sm, s.hosts[id].constants.params, b);

        // Prove UnAckedListInNetwork 
        reveal_UnAckedListInNetwork();
        forall id,msg,dst |
                id  in AllHostIdentities(s)
             && msg in AckStateLookup(dst, s'.hosts[id].sd.sendState).unAcked
             && NoAcksInUnAckedLists(s'.hosts[id].sd)
             && dst == msg.dst
            ensures Packet(msg.dst, s'.hosts[id].me, msg) in s'.network;
        {
            var unAcked  := AckStateLookup(dst, s.hosts[id].sd.sendState).unAcked;
            var unAcked' := AckStateLookup(dst, s'.hosts[id].sd.sendState).unAcked;
            var i :| 0 <= i < |unAcked'| && unAcked'[i] == msg;
            if i < |unAcked| {
                assert msg in AckStateLookup(dst, s.hosts[id].sd.sendState).unAcked;
            } else {
                var oldAckState := AckStateLookup(dst, s.hosts[id].sd.sendState); 
                var new_seqno := oldAckState.numPacketsAcked + |oldAckState.unAcked| + 1;
                if new_seqno > s.hosts[id].constants.params.max_seqno {
                    assert out == {};
                } else {
                    assert out == {Packet(msg.dst, s'.hosts[id].me, msg)};
                }
            }
        }
    } else {
        forall dst, src, seqno ensures ReceiverHasNotCanceledUnsentSeqno(s', dst, src, seqno);
        {
            assert ReceiverHasNotCanceledUnsentSeqno(s, dst, src, seqno);   // OBSERVE trigger
        } 
        reveal_UnAckedListInNetwork();
        reveal_PacketsHaveSenderUniqueSeqnos();
        NonDelegationsEachKeyClaimedInExactlyOnePlace(s, s');
    }
}

lemma NextInv_Set_NotADelegateStep(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.SetRequest? && NextSetRequest(s.hosts[id], s'.hosts[id], rpkt, out);
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    ensures NotADelegateStep(s, s');
{
}

lemma NextInv_Set(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires Some(rpkt) == s.hosts[id].receivedPacket;
    requires s'.hosts[id].receivedPacket.None?;
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.SetRequest? && NextSetRequest(s.hosts[id], s'.hosts[id], rpkt, out);
    requires NotADelegateStep(s, s');
    //requires ReceivePacket(s.hosts[id], s'.hosts[id], rpkt, out, ack);
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    ensures Inv(s');
{
    var sm,m,b :| NextSetRequest_Complete(s.hosts[id], s'.hosts[id], rpkt.src, rpkt.msg.seqno, rpkt.msg.m, sm, m, out, b);

    NonDelegationsEachKeyClaimedInExactlyOnePlace(s, s');

    if b && ValidKey(rpkt.msg.m.k_setrequest) && ValidOptionalValue(rpkt.msg.m.v_setrequest) {
        assert SendSingleMessage(s.hosts[id].sd, s'.hosts[id].sd, m, sm, s.hosts[id].constants.params, b);
        assert NoHostsStoreEmptyValues(s');

        //ReceiveSingleMessageNew_Properties(s, s', id, recv, rpkt, out, ack);
        reveal_PacketsHaveSenderUniqueSeqnos();
        reveal_UnAckedListInNetwork();

        forall dst, src, seqno ensures ReceiverHasNotCanceledUnsentSeqno(s', dst, src, seqno);
        {
            assert ReceiverHasNotCanceledUnsentSeqno(s, dst, src, seqno);   // OBSERVE trigger
        } // assert ReceiverHasCanceledNoUnsentSeqnos(s');

    
        SendSingleMessagePreservesUnAckListProperties(s.hosts[id].sd, s'.hosts[id].sd, m, sm, s.hosts[id].constants.params, b);

        // Prove UnAckedListInNetwork 
        reveal_UnAckedListInNetwork();
        forall id,msg,dst |
                id  in AllHostIdentities(s)
             && msg in AckStateLookup(dst, s'.hosts[id].sd.sendState).unAcked
             && NoAcksInUnAckedLists(s'.hosts[id].sd)
             && dst == msg.dst
            ensures Packet(msg.dst, s'.hosts[id].me, msg) in s'.network;
        {
            var unAcked  := AckStateLookup(dst, s.hosts[id].sd.sendState).unAcked;
            var unAcked' := AckStateLookup(dst, s'.hosts[id].sd.sendState).unAcked;
            var i :| 0 <= i < |unAcked'| && unAcked'[i] == msg;
            if i < |unAcked| {
                assert msg in AckStateLookup(dst, s.hosts[id].sd.sendState).unAcked;
            } else {
                var oldAckState := AckStateLookup(dst, s.hosts[id].sd.sendState); 
                var new_seqno := oldAckState.numPacketsAcked + |oldAckState.unAcked| + 1;
                if new_seqno > s.hosts[id].constants.params.max_seqno {
                    assert out == {};
                } else {
                    assert out == {Packet(msg.dst, s'.hosts[id].me, msg)};
                }
            }
        }
    } else {
        forall dst, src, seqno ensures ReceiverHasNotCanceledUnsentSeqno(s', dst, src, seqno);
        {
            assert ReceiverHasNotCanceledUnsentSeqno(s, dst, src, seqno);   // OBSERVE trigger
        } 
        reveal_UnAckedListInNetwork();
        reveal_PacketsHaveSenderUniqueSeqnos();
    }
}

lemma PacketStillInFlightForward_ReceiveSingle(s:SHT_State, s':SHT_State, id:NodeIdentity, out:set<Packet>, rpkt:Packet, p:Packet, ack:Packet)
    requires HiddenInv(s);
    requires MapComplete(s);
    requires MapComplete(s');
    requires PacketsHaveSaneHeaders(s');
    requires NoConfigChanged(s, s');
    requires id in AllHostIdentities(s);
    requires rpkt in s.network;
    requires rpkt.dst == id;
    requires ReceiveSingleMessage(s.hosts[id].sd, s'.hosts[id].sd, rpkt, ack, out);
    requires NewSingleMessage(s.hosts[id].sd, rpkt);
    requires p!=rpkt;
    requires Network_Send(s.network, s'.network, id, out);
    requires !(p in out);
    requires forall oid :: oid in AllHostIdentities(s) && oid!=id ==> s'.hosts[oid]==s.hosts[oid];
    requires PacketInFlight(s, p);
    ensures PacketInFlight(s', p);
{
    reveal_HiddenInv();
    reveal_PacketsHaveSenderUniqueSeqnos();
}

lemma PacketStillInFlightReverse(s:SHT_State, s':SHT_State, id:NodeIdentity, rpkt:Packet, out:set<Packet>, p:Packet, ack:Packet)
    requires Inv(s);
    requires MapComplete(s');
    requires NoConfigChanged(s, s');
    requires PacketsHaveSaneHeaders(s');
    requires PacketsHaveSenderUniqueSeqnos(s');
    requires Network_Send(s.network, s'.network, id, out);
    requires rpkt in s.network;
    requires id in AllHostIdentities(s);
    requires ReceiveSingleMessage(s.hosts[id].sd, s'.hosts[id].sd, rpkt, ack, out);
    requires forall oid :: oid in AllHostIdentities(s) && oid!=id ==> s'.hosts[oid]==s.hosts[oid];
    requires rpkt.dst == id;
    requires PacketInFlight(s', p);
    requires forall po :: po in out ==> p!=po;
    requires rpkt != p;
    ensures PacketInFlight(s, p);
{
  assert MessageNotReceived(s'.hosts[p.dst].sd, p.src, p.msg);
}


lemma NextInv_Delegate_EachKeyClaimedInExactlyOnePlace_NoInFlightPacketClaimsKey(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, pkt:Packet, k:Key)
    requires HiddenInv(s);
    requires MapComplete(s);
    requires MapComplete(s');
    requires PacketsHaveSaneHeaders(s');
    requires PacketsHaveSenderUniqueSeqnos(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires Some(pkt) == s.hosts[id].receivedPacket;
    requires s'.hosts[id].receivedPacket.None?;
    requires pkt in s.network && pkt.msg.SingleMessage? && pkt.msg.m.Delegate? && NextDelegate(s.hosts[id], s'.hosts[id], pkt, out);
    requires KeyRangeContains(pkt.msg.m.range, KeyPlus(k));
    requires NoInFlightPacketClaimsKey(s, k);
    requires UniqueHostClaimsKey(s, k);
    ensures NoInFlightPacketClaimsKey(s', k);
    ensures UniqueHostClaimsKey(s', k);
{
    reveal_HiddenInv();
    // OBSERVE Unfortunate conservative triggers
    forall ipkt
        ensures !InFlightPacketClaimsKey(s', ipkt, k);
    {
        if ipkt.msg.Ack? || ipkt.msg.InvalidMessage? {  // Can't claim a key
        } else if (!ipkt.msg.m.Delegate?) { // fine
        } else if (!KeyRangeContains(ipkt.msg.m.range, KeyPlus(k))) { // fine
        } else if (!PacketInFlight(s', ipkt)) { // fine
        } else {
            assert ipkt.msg.SingleMessage?;
            assert ipkt.msg.m.Delegate?;
            assert PacketInFlight(s', ipkt);
            assert KeyRangeContains(ipkt.msg.m.range, KeyPlus(k));
            assert InFlightPacketClaimsKey(s', ipkt, k);

            if PacketInFlight(s, ipkt) {
                assert InFlightPacketClaimsKey(s, ipkt, k);
                assert false;
            } else {
                assert false;
            }
        }
    }
    assert forall pkt :: !InFlightPacketClaimsKey(s', pkt, k);   // OBSERVE unfortunate trigger
    assert exists id
        :: id in AllHostIdentities(s) && HostClaimsKey(s'.hosts[id], k);   // OBSERVE unfortunate trigger
    assert forall i1,i2
        :: i1 in AllHostIdentities(s) && HostClaimsKey(s.hosts[i1], k)
        && i2 in AllHostIdentities(s) && HostClaimsKey(s.hosts[i2], k)
        ==> i1==i2;   // OBSERVE unfortunate trigger
}

// This shouldn't take a lemma; Dafny's set reasoning managed
// to stumble herewith:
//
//  assert rpkt in recv;
//  assert recv == PacketsTo(s.network, id);
//  assert rpkt in PacketsTo(s.network, id);    // on *This* line!!
//  assert rpkt in s.network;
// Thus, I present:
lemma NetworkReceive_ImpliesMembership(s:SHT_State, id:NodeIdentity, recv:set<Packet>, rpkt:Packet)
    requires Network_Receive(s.network, id, recv);
    requires rpkt in recv;
    ensures rpkt in s.network;
{
}
// And then it lost:
//  assert out=={};
//  assert !(pkt in out);
// !!!

lemma NextInv_Delegate_EachKeyClaimedInExactlyOnePlace(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet)
    requires HiddenInv(s);
    requires MapComplete(s);
//    requires PacketsHaveSenderUniqueSeqnos(s');
    requires MapComplete(s');
    requires PacketsHaveSaneHeaders(s');
    requires InvConstants(s');
    requires PacketsHaveSenderUniqueSeqnos(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires Network_Receive(s.network, id, recv);
    requires Some(rpkt) == s.hosts[id].receivedPacket;
    requires s'.hosts[id].receivedPacket.None?;
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.Delegate? && NextDelegate(s.hosts[id], s'.hosts[id], rpkt, out);
    ensures EachKeyClaimedInExactlyOnePlace(s');
{
    forall k
        ensures
           (UniqueInFlightPacketClaimsKey(s', k) && NoHostClaimsKey(s', k))
        || (NoInFlightPacketClaimsKey(s', k) && UniqueHostClaimsKey(s', k));
    {
        //if (KeyRangeContains(rpkt.msg.m.range, KeyPlus(k))) {
        if BufferedPacketClaimsKey(s.hosts[id], k) {
            reveal_HiddenInv();
            assert HostClaimsKey(s.hosts[id], k);
            reveal_EachKeyClaimedInExactlyOnePlace();
            NextInv_Delegate_EachKeyClaimedInExactlyOnePlace_NoInFlightPacketClaimsKey(s, s', id, recv, out, rpkt, k);
        } else {
            if (UniqueInFlightPacketClaimsKey(s, k) && NoHostClaimsKey(s, k)) {
                forall pkt | pkt!=rpkt
                    ensures (PacketInFlight(s, pkt) <==> PacketInFlight(s', pkt));
                {
                        reveal_PacketsHaveSenderUniqueSeqnos();
                }
                forall xid | xid in AllHostIdentities(s)
                    ensures DelegateForKey(s'.hosts[xid].delegationMap, k)
                            == DelegateForKey(s.hosts[xid].delegationMap, k);
                {
                    var dm := s.hosts[xid].delegationMap;   // OBSERVE trigger
                    var dm' := s'.hosts[xid].delegationMap;   // OBSERVE trigger
                    if rpkt.src !in s.hosts[xid].constants.hostIds {
                        assert dm == dm';
                    } else {
                        calc ==> {
                            true;
                                { reveal_HiddenInv(); }
                            rpkt.dst in s.hosts[xid].constants.hostIds;
                        }
                        assert rpkt.src in s.hosts[xid].constants.hostIds;
                        assert DelegationPacket(Some(rpkt));
                        assert !KeyRangeContains(rpkt.msg.m.range, KeyPlus(k));
                    }
                }
                assert NoDelegationMapsChangedAboutKey(s, s', k);
                NonDelegationsEachKeyClaimedInExactlyOnePlace_case1(s, s', k);
            } else {
                reveal_HiddenInv();
                reveal_EachKeyClaimedInExactlyOnePlace();
                forall pkt:Packet |
                    pkt.msg.SingleMessage? && pkt.msg.m.Delegate? && KeyRangeContains(pkt.msg.m.range, KeyPlus(k))
                    ensures (PacketInFlight(s, pkt) <==> PacketInFlight(s', pkt));
                {
                    reveal_PacketsHaveSenderUniqueSeqnos();
                }
                assert NoDelegationPacketsChangedAboutKey(s, s', k);
                NonDelegationsEachKeyClaimedInExactlyOnePlace_case2'(s, s', k);
            }
        }
    }
    reveal_EachKeyClaimedInExactlyOnePlace();
    assert EachKeyClaimedInExactlyOnePlace(s');
}

lemma NextInv_Delegate(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires Some(rpkt) == s.hosts[id].receivedPacket;
    requires s'.hosts[id].receivedPacket.None?;
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.Delegate? && NextDelegate(s.hosts[id], s'.hosts[id], rpkt, out);
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    ensures Inv(s');
{
    reveal_PacketsHaveSenderUniqueSeqnos();
    forall () ensures EachKeyClaimedInExactlyOnePlace(s');
    {
        reveal_HiddenInv();
        NextInv_Delegate_EachKeyClaimedInExactlyOnePlace(s, s', id, recv, out, rpkt);
        reveal_EachKeyClaimedInExactlyOnePlace();
    }

    // NoHostsStoreEmptyValues:
    forall (i,k |
        i in AllHostIdentities(s) && HostClaimsKey(s'.hosts[i], k) && k in s'.hosts[i].h)
        ensures  HashtableLookup(s'.hosts[i].h, k) != ValueAbsent()
    {
        if (i==id && KeyRangeContains(rpkt.msg.m.range, KeyPlus(k))) {
            reveal_EachKeyClaimedInExactlyOnePlace();
        } else {
            assert HashtableLookup(s.hosts[i].h, k) != ValueAbsent(); // OBSERVE trigger
        }
    }

    forall id,k:Key | id in AllHostIdentities(s)
        ensures DelegateForKey(s'.hosts[id].delegationMap, k) in AllHostIdentities(s);
    {
        assert DelegateForKey(s.hosts[id].delegationMap, k) in AllHostIdentities(s); // OBSERVE trigger
    }

    forall i,k | i in AllHostIdentities(s) && k in s'.hosts[i].h
        ensures HostClaimsKey(s'.hosts[i], k)
    {
        if !(i==id && KeyRangeContains(rpkt.msg.m.range, KeyPlus(k))) {
            assert DelegateForKey(s.hosts[i].delegationMap, k)==s.hosts[i].me || BufferedPacketClaimsKey(s.hosts[i], k);    // OBSERVE trigger
        }
    }
    assert HostsStoreOnlyOwnedKeys(s');

    forall dst, src, seqno ensures ReceiverHasNotCanceledUnsentSeqno(s', dst, src, seqno);
    {
        assert ReceiverHasNotCanceledUnsentSeqno(s, dst, src, seqno);   // OBSERVE trigger
    } // assert ReceiverHasCanceledNoUnsentSeqnos(s');

    reveal_UnAckedListInNetwork();
}

lemma NextInv_NextShard_EachKeyClaimedInExactlyOnePlace(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, kr:KeyRange, recipient:NodeIdentity, sm:SingleMessage<Message>, shouldSend:bool)
    requires Inv(s);
//    requires PacketsHaveSenderUniqueSeqnos(s');
    requires MapComplete(s');
    requires PacketsHaveSaneHeaders(s');
    requires PacketsHaveSenderUniqueSeqnos(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires recipient in AllHostIdentities(s);
    requires NextShard(s.hosts[id], s'.hosts[id], out, kr, recipient, sm, shouldSend);
    requires s'.hosts[id].receivedPacket.None?;
    requires var pkt := s.hosts[id].receivedPacket;
             pkt.Some? && pkt.v.msg.SingleMessage? && pkt.v.msg.m.Shard?;
    requires s.hosts[id].constants.hostIds == s.config.hostIds;
    ensures EachKeyClaimedInExactlyOnePlace(s');
{
    var spkt := Packet(recipient, s.hosts[id].me, sm);
    forall k
        ensures
           (UniqueInFlightPacketClaimsKey(s', k) && NoHostClaimsKey(s', k))
        || (NoInFlightPacketClaimsKey(s', k) && UniqueHostClaimsKey(s', k));
    {
        if shouldSend {
            if (KeyRangeContains(kr, KeyPlus(k))) {
                assert ReceiverHasNotCanceledUnsentSeqno(s, spkt.dst, spkt.src, spkt.msg.seqno);    // OBSERVE trigger
                //PacketInFlight(s', spkt);
                forall () ensures NoInFlightPacketClaimsKey(s, k);
                { reveal_EachKeyClaimedInExactlyOnePlace();
                    assert HostClaimsKey(s.hosts[id], k);
                    assert SomeHostClaimsKey(s, k);
                }
                if InFlightPacketClaimsKey(s', spkt, k) { // OBSERVE unfortunate trigger
                    forall p1,p2 |
                        InFlightPacketClaimsKey(s', p1, k) && InFlightPacketClaimsKey(s', p2, k)
                        ensures p1==p2;
                    {
                        // OBSERVE unfortunate triggers: tickle NoInFlightPacketClaimsKey
                        if (PacketInFlight(s, p1)) {
                            assert InFlightPacketClaimsKey(s, p1, k);
                        }
                        if (PacketInFlight(s, p2)) {
                            assert InFlightPacketClaimsKey(s, p2, k);
                        }
                    }
                    assert SomePacketClaimsKey(s', k) && OnlyOnePacketClaimsKey(s', k);
                    assert UniqueInFlightPacketClaimsKey(s', k);
                    forall i | i in AllHostIdentities(s)
                        ensures !HostClaimsKey(s'.hosts[i], k);
                    {
                        reveal_EachKeyClaimedInExactlyOnePlace();
                        if (i!=id) {    // OBSERVE unfortunate trigger
                            assert HostClaimsKey(s.hosts[id], k);
                        } else {
                            assert !(DelegateForKey(s'.hosts[id].delegationMap, k)==s'.hosts[id].me);
                            assert !BufferedPacketClaimsKey(s'.hosts[id], k);
                            assert !HostClaimsKey(s'.hosts[id], k);
                        }
                    }
                    assert NoHostClaimsKey(s', k);
                }
            } else {
                if (UniqueInFlightPacketClaimsKey(s, k) && NoHostClaimsKey(s, k)) {
                    reveal_EachKeyClaimedInExactlyOnePlace();
                    NonDelegationsEachKeyClaimedInExactlyOnePlace_case1(s, s', k);
                } else {
                    reveal_EachKeyClaimedInExactlyOnePlace();
                    reveal_HiddenInv();
                    NonDelegationsEachKeyClaimedInExactlyOnePlace_case2(s, s', k);
                }
            }
        } else {
            NonDelegationsEachKeyClaimedInExactlyOnePlace(s, s');
            reveal_EachKeyClaimedInExactlyOnePlace();
        }
    }
    reveal_EachKeyClaimedInExactlyOnePlace();
    assert EachKeyClaimedInExactlyOnePlace(s');
}

lemma NextInv_Shard(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, kr:KeyRange, recipient:NodeIdentity, sm:SingleMessage<Message>, shouldSend:bool)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires NextShard(s.hosts[id], s'.hosts[id], out, kr, recipient, sm, shouldSend);
    requires s'.hosts[id].receivedPacket.None?;
    requires var pkt := s.hosts[id].receivedPacket;
             pkt.Some? && pkt.v.msg.SingleMessage? && pkt.v.msg.m.Shard?;
    requires s.hosts[id].constants.hostIds == s.config.hostIds;
    ensures Inv(s');
{
    assert NoHostsStoreEmptyValues(s');
    assert DelegationMessagesCarryNoEmptyValues(s');
    var m := Delegate(kr, ExtractRange(s.hosts[id].h, kr));    
    reveal_PacketsHaveSenderUniqueSeqnos();
    assert PacketsHaveSenderUniqueSeqnos(s');

    forall () ensures EachKeyClaimedInExactlyOnePlace(s');
    {
        NextInv_NextShard_EachKeyClaimedInExactlyOnePlace(s, s', id, recv, out, kr, recipient, sm, shouldSend);
        reveal_EachKeyClaimedInExactlyOnePlace();
    }

    forall id,k:Key | id in AllHostIdentities(s)
        ensures DelegateForKey(s'.hosts[id].delegationMap, k) in AllHostIdentities(s);
    {
        assert AllDelegationsToKnownHosts(s);
        assert DelegateForKey(s.hosts[id].delegationMap, k) in AllHostIdentities(s); // OBSERVE trigger
    } //assert AllDelegationsToKnownHosts(s');

    forall dst, src, seqno ensures ReceiverHasNotCanceledUnsentSeqno(s', dst, src, seqno);
    {
        assert ReceiverHasNotCanceledUnsentSeqno(s, dst, src, seqno);   // OBSERVE trigger
    } // assert ReceiverHasCanceledNoUnsentSeqnos(s');

    SendSingleMessagePreservesUnAckListProperties(s.hosts[id].sd, s'.hosts[id].sd, m, sm, s.hosts[id].constants.params, shouldSend);

    // Prove UnAckedListInNetwork
    reveal_UnAckedListInNetwork();
    forall id,msg,dst |
            id  in AllHostIdentities(s)
         && msg in AckStateLookup(dst, s'.hosts[id].sd.sendState).unAcked
         && NoAcksInUnAckedLists(s'.hosts[id].sd)
         && dst == msg.dst
        ensures Packet(msg.dst, s'.hosts[id].me, msg) in s'.network;
    {
        var unAcked  := AckStateLookup(dst, s.hosts[id].sd.sendState).unAcked;
        var unAcked' := AckStateLookup(dst, s'.hosts[id].sd.sendState).unAcked;
        var i :| 0 <= i < |unAcked'| && unAcked'[i] == msg;
        if i < |unAcked| {
            assert msg in AckStateLookup(dst, s.hosts[id].sd.sendState).unAcked;
        } else {
            var oldAckState := AckStateLookup(dst, s.hosts[id].sd.sendState); 
            var new_seqno := oldAckState.numPacketsAcked + |oldAckState.unAcked| + 1;
            if new_seqno > s.hosts[id].constants.params.max_seqno {
                assert out == {};
            } else {
                assert out == {Packet(msg.dst, s'.hosts[id].me, msg)};
            }
        }
    }
}

lemma NextInv_Process_Boring_Message(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires s.hosts[id].receivedPacket.Some? && s.hosts[id].receivedPacket.v.msg.SingleMessage?
             ==> !s.hosts[id].receivedPacket.v.msg.m.Delegate?;
    //requires s'.hosts[id].receivedPacket.None?;
    requires s'.hosts[id] == s.hosts[id].(receivedPacket := None);
    requires out == {};
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    ensures Inv(s');
{
    var h := s.hosts[id];
    var h' := s'.hosts[id];

    assert out == {};
    assert h' == h.(receivedPacket := None);
    reveal_UnAckedListInNetwork(); // ==>
    assert AckListsInv(s');
    reveal_PacketsHaveSenderUniqueSeqnos(); // ==>
    assert PacketsHaveSenderUniqueSeqnos(s');
    // Prove ReceiverHasCanceledNoUnsentSeqnos(s')
    forall dst, src, seqno {:trigger ReceiverHasNotCanceledUnsentSeqno(s', dst, src, seqno)}
        ensures dst in AllHostIdentities(s) && src in AllHostIdentities(s)
                                     && HighestSeqnoSent(s.hosts[src].sd, dst) < seqno
        ==> seqno > TombstoneTableLookup(src, s.hosts[dst].sd.receiveState);
    {
        assert ReceiverHasNotCanceledUnsentSeqno(s, dst, src, seqno);       // OBSERVE: Need to trigger to expand the definition
    }
    assert ReceiverHasCanceledNoUnsentSeqnos(s');
    reveal_EachKeyClaimedInExactlyOnePlace(); // ==>
    assert NotADelegateStep(s, s');
    NonDelegationsEachKeyClaimedInExactlyOnePlace(s, s'); // Prove EachKeyClaimedInExactlyOnePlace
    assert EachKeyClaimedInExactlyOnePlace(s');
}

lemma NextInv_Process_Message(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires s'.hosts[id].receivedPacket.None?;
    requires ShouldProcessReceivedMessage(s.hosts[id]);
    requires s.hosts[id].receivedPacket.v in s.network;
    requires Process_Message(s.hosts[id], s'.hosts[id], out);
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    ensures Inv(s');
{
    var h := s.hosts[id];
    var h' := s'.hosts[id];
    var rpkt := s.hosts[id].receivedPacket.v;

    if (NextGetRequest(h, h', rpkt, out)) {
        NextInv_Get_NotADelegateStep(s, s', id, recv, out, rpkt);
        NextInv_Get(s, s', id, recv, out, rpkt);
        assert Inv(s');
    } else if (NextSetRequest(h, h', rpkt, out)) {
        NextInv_Set_NotADelegateStep(s, s', id, recv, out, rpkt);
        NextInv_Set(s, s', id, recv, out, rpkt);
    } else if (NextDelegate(h, h', rpkt, out)) {
        NextInv_Delegate(s, s', id, recv, out, rpkt);
    } else if (NextShard_Wrapper(h, h', rpkt, out)) {
        if (   rpkt.msg.m.recipient == h.me 
            || !ValidKeyRange(rpkt.msg.m.kr)
            || EmptyKeyRange(rpkt.msg.m.kr)
            || rpkt.msg.m.recipient !in h.constants.hostIds 
            || !DelegateForKeyRangeIsHost(h.delegationMap, rpkt.msg.m.kr, h.me)
            || |ExtractRange(h.h, rpkt.msg.m.kr)| >= max_hashtable_size()) {
            //s' == s.(receivedPacket := s'.receivedPacket) && out == {}   
            NextInv_Process_Boring_Message(s, s', id, recv, out);
        } else {
            var sm,b :| NextShard(h, h', out, rpkt.msg.m.kr, rpkt.msg.m.recipient, sm, b);
            NextInv_Shard(s, s', id, recv, out, rpkt.msg.m.kr, rpkt.msg.m.recipient, sm, b);
        }
    } else if NextReply(h, h', rpkt, out) {
        NextInv_Process_Boring_Message(s, s', id, recv, out);
        assert Inv(s');
    } else if NextRedirect(h, h', rpkt, out) {
        NextInv_Process_Boring_Message(s, s', id, recv, out);
        assert Inv(s');
    } else {
        assert false;
    }
}

lemma NextInv_ReceivePacket(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, rpkt:Packet, out:set<Packet>, ack:Packet)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires rpkt in recv;
    requires ReceivePacket(s.hosts[id], s'.hosts[id], rpkt, out, ack);
    ensures Inv(s');
{
    var h := s.hosts[id];
    var h' := s'.hosts[id];

    if h.receivedPacket.None? {
        assert ReceiveSingleMessage(h.sd, h'.sd, rpkt, ack, out);
        ReceivePacket_Properties(s, s', id, recv, rpkt, out, ack);
    } else {
        assert s.hosts == s'.hosts;     // OBSERVE (extensionality)
        assert s.network == s'.network; // OBSERVE (extensionality?)
        assert s == s';
    }
}

/*
lemma NextInv_ProcessReceivedPacket_BoringPacket(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires ProcessReceivedPacket(s.hosts[id], s'.hosts[id], out);
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    requires var h := s.hosts[id]; h.receivedPacket.Some? && !NewSingleMessage(h.sd, h.receivedPacket.v);
    ensures Inv(s');
{
    var h := s.hosts[id];
    var h' := s'.hosts[id];

    assert out == {};
    assert h' == h.(receivedPacket := None);
    reveal_UnAckedListInNetwork(); // ==>
    assert AckListsInv(s');
    reveal_PacketsHaveSenderUniqueSeqnos(); // ==>
    assert PacketsHaveSenderUniqueSeqnos(s');
    // Prove ReceiverHasCanceledNoUnsentSeqnos(s')
    forall dst, src, seqno 
        ensures dst in AllHostIdentities(s) && src in AllHostIdentities(s)
                                     && HighestSeqnoSent(s.hosts[src].sd, dst) < seqno
        ==> seqno > TombstoneTableLookup(src, s.hosts[dst].sd.receiveState);
    {
        assert ReceiverHasNotCanceledUnsentSeqno(s, dst, src, seqno);       // OBSERVE: Need to trigger to expand the definition
    }
    assert ReceiverHasCanceledNoUnsentSeqnos(s');
    reveal_EachKeyClaimedInExactlyOnePlace(); // ==>
    assert NotADelegateStep(s, s');
    NonDelegationsEachKeyClaimedInExactlyOnePlace(s, s'); // Prove EachKeyClaimedInExactlyOnePlace
    assert EachKeyClaimedInExactlyOnePlace(s');
}
*/

lemma NextInv_ProcessReceivedPacket(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires ProcessReceivedPacket(s.hosts[id], s'.hosts[id], out);
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    ensures Inv(s');
{
    var h := s.hosts[id];
    var h' := s'.hosts[id];

    //assert ReceiveSingleMessage(h.sd, h'.sd, rpkt, ack, ack_packets);

    if ShouldProcessReceivedMessage(h) {
        NextInv_Process_Message(s, s', id, recv, out);
    } else {
        assert s.hosts == s'.hosts;     // OBSERVE (extensionality)
        assert s.network == s'.network; // OBSERVE (extensionality?)
        assert s == s';
    }
}

lemma NextInv_SpontaneouslyRetransmit(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out)
    ensures Inv(s');
{
    var h := s.hosts[id];
    var h' := s'.hosts[id];

    reveal_UnAckedListInNetwork();
    assert h == h';
    forall p | p in out 
        ensures p in s.network;
    {
        var dst, i :| dst in h.sd.sendState && 0 <= i < |h.sd.sendState[dst].unAcked| && h.sd.sendState[dst].unAcked[i].SingleMessage? && (var sm := h.sd.sendState[dst].unAcked[i]; p.dst == sm.dst && p.src == s.hosts[id].me && p.msg == sm); // Needed for the OBSERVE on the next line
        assert AckStateLookup(dst, h.sd.sendState) == h.sd.sendState[dst];  // OBSERVE
        assert UnAckedMsgForDst(h.sd, p.msg, p.dst);    // OBSERVE
    }
    reveal_PacketsHaveSenderUniqueSeqnos();


    // Prove ReceiverHasCanceledNoUnsentSeqnos(s')
    forall dst, src, seqno {:trigger ReceiverHasNotCanceledUnsentSeqno(s', dst, src, seqno)}
        ensures dst in AllHostIdentities(s) && src in AllHostIdentities(s)
                                     && HighestSeqnoSent(s.hosts[src].sd, dst) < seqno
        ==> seqno > TombstoneTableLookup(src, s.hosts[dst].sd.receiveState);
    {
        assert ReceiverHasNotCanceledUnsentSeqno(s, dst, src, seqno);       // OBSERVE: Need to trigger to expand the definition
    }

    NonDelegationsEachKeyClaimedInExactlyOnePlace(s, s');
}

lemma NextInv_NextPred(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_NextPred(s, s', id, recv, out);
    ensures Inv(s');
{

    var h := s.hosts[id];
    var h' := s'.hosts[id];
    
    if (exists pkt, ack :: pkt in recv && ReceivePacket(h, h', pkt, out, ack)) {
        var pkt, ack :| pkt in recv && ReceivePacket(h, h', pkt, out, ack);
        NextInv_ReceivePacket(s, s', id, recv, pkt, out, ack);
    } else if SpontaneouslyRetransmit(h, h', out) {
        NextInv_SpontaneouslyRetransmit(s, s', id, recv, out);
    } else if ProcessReceivedPacket(h, h', out) {
        NextInv_ProcessReceivedPacket(s, s', id, recv, out);
    }
}

lemma NextInv_NextExternal(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_NextExternal(s, s', id, recv, out);
    ensures Inv(s');
{
    reveal_UnAckedListInNetwork(); // ==>
    assert AckListsInv(s');

    reveal_PacketsHaveSenderUniqueSeqnos(); // ==>
    assert PacketsHaveSenderUniqueSeqnos(s');

    forall dst, src, seqno 
        ensures ReceiverHasNotCanceledUnsentSeqno(s', dst, src, seqno);  // <== Prove this subinvariant
    {
        assert ReceiverHasNotCanceledUnsentSeqno(s, dst, src, seqno);
    }

    NonDelegationsEachKeyClaimedInExactlyOnePlace(s, s');   // ==> 
    assert EachKeyClaimedInExactlyOnePlace(s');

}

lemma NextInv(s:SHT_State, s':SHT_State)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    ensures Inv(s');
{
    if (exists id, recv, out :: SHT_NextPred(s, s', id, recv, out)) {
        var id, recv, out :| SHT_NextPred(s, s', id, recv, out);
        NextInv_NextPred(s, s', id, recv, out);
    } else if (exists id, recv, out :: SHT_NextExternal(s, s', id, recv, out)) {
        var id, recv, out :| SHT_NextExternal(s, s', id, recv, out);
        NextInv_NextExternal(s, s', id, recv, out);
    } else {
        assert false;   // There should be no other cases
    }
}

lemma InitInv(c:SHTConfiguration, s:SHT_State)
    requires WFSHTConfiguration(c);
    requires SHT_Init(c, s);
    ensures  Inv(s);
{
    reveal_UnAckedListInNetwork();
    reveal_EachKeyClaimedInExactlyOnePlace();
    forall k
        ensures NoInFlightPacketClaimsKey(s, k);
        ensures UniqueHostClaimsKey(s, k);
    {
        var id := s.config.rootIdentity;
        assert HostClaimsKey(s.hosts[id], k);
    }
    reveal_PacketsHaveSenderUniqueSeqnos();
}

} 
