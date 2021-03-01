include "SingleDeliveryState.i.dfy"
include "Parameters.i.dfy"
include "../../Protocol/SHT/RefinementProof/InvProof.i.dfy"
include "PacketParsing.i.dfy"

module SHT__SingleDeliveryModel_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened SHT__Network_i
import opened SHT__CMessage_i
import opened SHT__SingleDeliveryState_i
import opened Impl_Parameters_i
import opened SHT__InvProof_i
import opened SHT__PacketParsing_i
import opened Common__SeqIsUnique_i
import opened Common__NodeIdentity_i
import opened GenericRefinement_i
import opened SHT__SingleDelivery_i

method CTombstoneTableLookup(src:EndPoint, t:CTombstoneTable) returns (last_seqno:uint64)
    requires EndPointIsAbstractable(src);
    requires CTombstoneTableIsAbstractable(t);
    ensures  last_seqno as int == TombstoneTableLookup(AbstractifyEndPointToNodeIdentity(src), AbstractifyCTombstoneTableToTombstoneTable(t));
{
    lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
    lemma_AbstractifyMap_properties(t, AbstractifyEndPointToNodeIdentity, uint64_to_nat_t, RefineNodeIdentityToEndPoint);
    if src in t {
        last_seqno := t[src];
    } else {
        last_seqno := 0;
    }
}

method CAckStateLookup(src:EndPoint, sendState:CSendState, ghost params:CParameters) returns (ackState:CAckState)
    requires EndPointIsAbstractable(src);
    requires CSendStateIsAbstractable(sendState);
    requires CSendStateIsValid(sendState, params);
    ensures  CAckStateIsAbstractable(ackState);
    ensures  CAckStateIsValid(ackState, src, params);
    ensures  AbstractifyCAskStateToAckState(ackState) == AckStateLookup(AbstractifyEndPointToNodeIdentity(src), AbstractifyCSendStateToSendState(sendState));
{
    lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
    lemma_AbstractifyMap_properties(sendState, AbstractifyEndPointToNodeIdentity, AbstractifyCAskStateToAckState, RefineNodeIdentityToEndPoint);
    if src in sendState {
        ackState := sendState[src];
    } else {
        ackState := CAckState(0, []);
    }
}

method CSingleDeliveryAcctInit(ghost params:CParameters) returns (acct:CSingleDeliveryAcct)
    ensures  CSingleDeliveryAccountIsValid(acct, params);
    ensures  SingleDelivery_Init() == AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct);
{
    acct := CSingleDeliveryAcct(map[], map[]);
    lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
    lemma_AbstractifyMap_properties(acct.receiveState, AbstractifyEndPointToNodeIdentity, uint64_to_nat_t, RefineNodeIdentityToEndPoint);
    lemma_AbstractifyMap_properties(acct.sendState, AbstractifyEndPointToNodeIdentity, AbstractifyCAskStateToAckState, RefineNodeIdentityToEndPoint);
}

method MessageNotReceivedImpl(acct:CSingleDeliveryAcct, src:EndPoint, sm:CSingleMessage, ghost params:CParameters) returns (b:bool)
    requires CSingleDeliveryAccountIsValid(acct, params);
    requires EndPointIsAbstractable(src);
    requires CSingleMessageIsAbstractable(sm);
    ensures  b == MessageNotReceived(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct), AbstractifyEndPointToNodeIdentity(src), AbstractifyCSingleMessageToSingleMessage(sm));
{
    var last_seqno := CTombstoneTableLookup(src, acct.receiveState);
    b := sm.CSingleMessage? && sm.seqno > last_seqno;
}

method NewSingleMessageImpl(acct:CSingleDeliveryAcct, pkt:CPacket, ghost params:CParameters) returns (b:bool)
    requires CSingleDeliveryAccountIsValid(acct, params);
    requires CPacketIsAbstractable(pkt) && CSingleMessageIs64Bit(pkt.msg) && !pkt.msg.CInvalidMessage?; // CSingleMessageMarshallable(pkt.msg);
    ensures  b == NewSingleMessage(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct), AbstractifyCPacketToShtPacket(pkt));
{
    if pkt.msg.CSingleMessage?
    {
        var last_seqno := CTombstoneTableLookup(pkt.src, acct.receiveState);
        b := if pkt.msg.seqno > 0 then pkt.msg.seqno - 1 == last_seqno else false;
    }
    else
    {
        b := false;
    }
}


method TruncateUnAckListImpl(unAcked:seq<CSingleMessage>, seqnoAcked:uint64, e:EndPoint, ghost old_seqno:int, ghost bound:int) returns (truncated:seq<CSingleMessage>)
    requires CSingleMessageSeqIsAbstractable(unAcked);
    requires CUnAckedListValidForDst(unAcked, e);
    requires UnAckedListSequential(unAcked);
    requires (|unAcked| > 0 ==> unAcked[0].seqno as int == old_seqno + 1);
    requires old_seqno <= seqnoAcked as int <= bound;
    requires |unAcked| + old_seqno <= bound;
    ensures  CSingleMessageSeqIsAbstractable(truncated);
    ensures  CUnAckedListValidForDst(truncated, e);
    ensures  UnAckedListSequential(truncated);
    ensures  AbstractifySeqOfCSingleMessageToSeqOfSingleMessage(truncated) == TruncateUnAckList(AbstractifySeqOfCSingleMessageToSeqOfSingleMessage(unAcked), seqnoAcked as int);
    ensures (|truncated| > 0 ==> truncated[0].seqno as int == seqnoAcked as int + 1)
    ensures |truncated| + seqnoAcked as int <= bound;
{
    if |unAcked| > 0 && unAcked[0].CSingleMessage? && unAcked[0].seqno <= seqnoAcked {
        assert AbstractifySeqOfCSingleMessageToSeqOfSingleMessage(unAcked[1..]) == AbstractifySeqOfCSingleMessageToSeqOfSingleMessage(unAcked)[1..];        // OBSERVE
        truncated := TruncateUnAckListImpl(unAcked[1..], seqnoAcked, e, old_seqno + 1, bound);
    } else {
        truncated := unAcked;
    }
}

method ReceiveAckImpl(acct:CSingleDeliveryAcct, pkt:CPacket, ghost params:CParameters) returns (acct':CSingleDeliveryAcct)
    requires CSingleDeliveryAccountIsValid(acct, params);
    requires CPacketIsAbstractable(pkt) && CSingleMessageMarshallable(pkt.msg);
    requires pkt.msg.CAck?;
    requires CParametersIsValid(params);
    ensures  CSingleDeliveryAccountIsValid(acct', params);
    ensures  ReceiveAck(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct), AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct'), AbstractifyCPacketToShtPacket(pkt), {});
{
    var oldAckState := CAckStateLookup(pkt.src, acct.sendState, params);
    assert CUnAckedListValidForDst(oldAckState.unAcked, pkt.src);
    assert CUnAckedListValid(oldAckState.unAcked);

    if pkt.msg.ack_seqno > oldAckState.numPacketsAcked {
        var newUnAcked := TruncateUnAckListImpl(oldAckState.unAcked, pkt.msg.ack_seqno, pkt.src, oldAckState.numPacketsAcked as int, params.max_seqno as int);
        assert CUnAckedListValidForDst(newUnAcked, pkt.src);
        var newAckState := oldAckState.(numPacketsAcked := pkt.msg.ack_seqno, unAcked := newUnAcked);
        lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
        lemma_AbstractifyMap_properties(acct.sendState, AbstractifyEndPointToNodeIdentity, AbstractifyCAskStateToAckState, RefineNodeIdentityToEndPoint);
        assert AbstractifyCAskStateToAckState(newAckState) == 
               AbstractifyCAskStateToAckState(oldAckState).(numPacketsAcked := AbstractifyCPacketToShtPacket(pkt).msg.ack_seqno,
                                            unAcked := AbstractifySeqOfCSingleMessageToSeqOfSingleMessage(newUnAcked));
//        if newAckState.unAcked == [] {
//            assert pkt.msg.ack_seqno as int < params.max_seqno as int;
//            assert newAckState.numPacketsAcked as int + |newAckState.unAcked| <= params.max_seqno as int;
//        } else {
//            assert newAckState.numPacketsAcked as int + |newAckState.unAcked| <= params.max_seqno as int;
//        }
        acct' := acct.(sendState := acct.sendState[pkt.src := newAckState]);
    } else {
        acct' := acct;
    }
}

method ShouldAckSingleMessageImpl(acct:CSingleDeliveryAcct, pkt:CPacket, ghost params:CParameters) returns (b:bool)
    requires CSingleDeliveryAccountIsValid(acct, params);
    requires CPacketIsAbstractable(pkt);
    ensures  b == ShouldAckSingleMessage(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct), AbstractifyCPacketToShtPacket(pkt));
{
    var last_seqno := CTombstoneTableLookup(pkt.src, acct.receiveState);

    b := pkt.msg.CSingleMessage? && pkt.msg.seqno <= last_seqno;
}

method SendAckImpl(acct:CSingleDeliveryAcct, pkt:CPacket, ghost params:CParameters) returns (ack:CPacket)
    requires CSingleDeliveryAccountIsValid(acct, params);
    requires CPacketIsAbstractable(pkt);
    requires pkt.msg.CSingleMessage?;
    requires ShouldAckSingleMessage(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct), AbstractifyCPacketToShtPacket(pkt));
    ensures  CPacketIsAbstractable(ack);
    ensures  SendAck(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct), AbstractifyCPacketToShtPacket(pkt), AbstractifyCPacketToShtPacket(ack), { AbstractifyCPacketToShtPacket(ack) });
    ensures ack.src == pkt.dst && ack.dst == pkt.src;
{
    ack := CPacket(pkt.src,  pkt.dst, CAck(pkt.msg.seqno));
}

method MaybeAckPacketImpl(acct:CSingleDeliveryAcct, pkt:CPacket, ghost params:CParameters) returns (b:bool, ack:CPacket)
    requires CSingleDeliveryAccountIsValid(acct, params);
    requires CPacketIsAbstractable(pkt);
    ensures  CPacketIsAbstractable(ack);
    ensures  MaybeAckPacket(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct), AbstractifyCPacketToShtPacket(pkt), AbstractifyCPacketToShtPacket(ack), 
                            if b then { AbstractifyCPacketToShtPacket(ack) } else {});
    ensures b ==> ack.src == pkt.dst && ack.dst == pkt.src;
{
    var should_ack := ShouldAckSingleMessageImpl(acct, pkt, params);
    if should_ack {
        b := true;
        ack := SendAckImpl(acct, pkt, params);
    } else {
        b := false;
        ack := pkt;
    }
}

method ReceiveRealPacketImpl(acct:CSingleDeliveryAcct, pkt:CPacket, ghost params:CParameters) returns (acct':CSingleDeliveryAcct)
    requires CSingleDeliveryAccountIsValid(acct, params);
    requires CPacketIsAbstractable(pkt) && CSingleMessageIs64Bit(pkt.msg) && !pkt.msg.CInvalidMessage?; // CSingleMessageMarshallable(pkt.msg); 
    requires pkt.msg.CSingleMessage?;
    ensures  CSingleDeliveryAccountIsValid(acct', params);
    ensures  ReceiveRealPacket(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct), AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct'), AbstractifyCPacketToShtPacket(pkt));
{
    var b := NewSingleMessageImpl(acct, pkt, params);
    if b {
        var last_seqno := CTombstoneTableLookup(pkt.src, acct.receiveState);
        acct' := acct.(receiveState := acct.receiveState[pkt.src := last_seqno + 1]);

        lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
        lemma_AbstractifyMap_properties(acct.receiveState, AbstractifyEndPointToNodeIdentity, uint64_to_nat_t, RefineNodeIdentityToEndPoint);
    } else {
        acct' := acct;
    }
}

method ReceiveSingleMessageImpl(acct:CSingleDeliveryAcct, pkt:CPacket, ghost params:CParameters) 
    returns (b:bool, acct':CSingleDeliveryAcct, ack:CPacket)
    requires CSingleDeliveryAccountIsValid(acct, params);
    requires CPacketIsAbstractable(pkt) && CSingleMessageIs64Bit(pkt.msg) && !pkt.msg.CInvalidMessage?; // CSingleMessageMarshallable(pkt.msg); 
    requires CParametersIsValid(params);
    ensures  CSingleDeliveryAccountIsValid(acct', params);
    ensures  CPacketIsAbstractable(ack);
    ensures  ReceiveSingleMessage(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct), AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct'), AbstractifyCPacketToShtPacket(pkt),
                                  AbstractifyCPacketToShtPacket(ack), if b then { AbstractifyCPacketToShtPacket(ack) } else {});
    ensures b ==> ack.src == pkt.dst && ack.dst == pkt.src;
{
    if pkt.msg.CAck? {
        acct' := ReceiveAckImpl(acct, pkt, params);
        b := false;
    } else if pkt.msg.CSingleMessage? {
        acct' := ReceiveRealPacketImpl(acct, pkt, params);
        b, ack := MaybeAckPacketImpl(acct', pkt, params);
    }
    else {
        assert pkt.msg.CInvalidMessage?;
        b := false;
        acct' := acct;
    }

    if !b {
        ack := pkt;     // Ensures ack is refinable
    }
}


method SendSingleCMessage(acct:CSingleDeliveryAcct, m:CMessage, dst:EndPoint, params:CParameters) 
    returns (acct':CSingleDeliveryAcct, sm:CSingleMessage, shouldSend:bool)
    requires CSingleDeliveryAccountIsValid(acct, params);
    requires CMessageIsAbstractable(m);
    requires MessageMarshallable(m);
    requires EndPointIsAbstractable(dst);
    requires CParametersIsValid(params);
    ensures  CSingleDeliveryAccountIsValid(acct', params);
    ensures  CSingleMessageIsAbstractable(sm);
    ensures  sm.CSingleMessage? ==> sm.dst == dst;
    ensures  SendSingleMessage(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct), AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct'),
                               AbstractifyCMessageToRslMessage(m), AbstractifyCSingleMessageToSingleMessage(sm), AbstractifyCParametersToParameters(params), shouldSend);
{
    lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
    lemma_AbstractifyMap_properties(acct.sendState, AbstractifyEndPointToNodeIdentity, AbstractifyCAskStateToAckState, RefineNodeIdentityToEndPoint);

    var oldAckState := CAckStateLookup(dst, acct.sendState, params);
    assert CAckStateIsValid(oldAckState, dst, params);

    assert oldAckState.numPacketsAcked as int + |oldAckState.unAcked| <= params.max_seqno as int;
    if oldAckState.numPacketsAcked + |oldAckState.unAcked| as uint64 == params.max_seqno {
        shouldSend := false;
        acct' := acct;
        sm := CSingleMessage(0, dst, m);        // Dummy message to simplify postconditions
    } else {
        var sm_new := CSingleMessage((oldAckState.numPacketsAcked + |oldAckState.unAcked| as uint64 + 1) as uint64, dst, m);
        //assert CSingleMessageMarshallable(sm);
        assert MapSeqToSeq(oldAckState.unAcked + [sm_new], AbstractifyCSingleMessageToSingleMessage) == 
               MapSeqToSeq(oldAckState.unAcked, AbstractifyCSingleMessageToSingleMessage) + [AbstractifyCSingleMessageToSingleMessage(sm_new)];

        var newAckState := oldAckState.(unAcked := oldAckState.unAcked + [sm_new]);
        var acctInt := acct.sendState[dst := newAckState];
        acct' := acct.(sendState := acctInt);
        sm := sm_new;
        shouldSend := true;
        UnAckedListFinalEntry(AbstractifySeqOfCSingleMessageToSeqOfSingleMessage(oldAckState.unAcked), oldAckState.numPacketsAcked as int);
    }
}

predicate CombinedPreImage<T>(seqs:seq<seq<T>>, combined:seq<T>, index:int)
    requires 0 <= index < |combined|;
{
    exists j, k {:trigger seqs[j][k]} :: 0 <= j < |seqs| && 0 <= k < |seqs[j]| && seqs[j][k] == combined[index]
}

method ConcatenateSeqs<T(==)>(seqs:seq<seq<T>>) returns (combined:seq<T>)
    ensures forall j, k :: 0 <= j < |seqs| && 0 <= k < |seqs[j]| 
                           ==> seqs[j][k] in combined;
    ensures forall m :: 0 <= m < |combined| ==> CombinedPreImage(seqs, combined, m);
{
    combined := [];
    var i := 0;

    while i < |seqs|
        invariant 0 <= i <= |seqs|;
        invariant forall j, k :: 0 <= j < i && 0 <= k < |seqs[j]| 
                                 ==> seqs[j][k] in combined;
        invariant forall m :: 0 <= m < |combined| ==> CombinedPreImage(seqs, combined, m);
    {
        ghost var old_combined := combined;
        combined := combined + seqs[i];
        i := i + 1;
        forall m | 0 <= m < |combined| 
            ensures CombinedPreImage(seqs, combined, m);
        {
            if m < |old_combined| {
                // Loop invariant should cover this
                assert CombinedPreImage(seqs, old_combined, m);
            } else {
                var m_offset := m - |old_combined|;
                assert seqs[i - 1][m_offset] == combined[m];
                assert CombinedPreImage(seqs, combined, m);
            }
        }
    }

}

lemma lemma_AbstractifyCPacketsToPackets_reverse(cps:set<CPacket>, p:Packet) returns (cp:CPacket)
    requires CPacketsIsAbstractable(cps);
    requires p in AbstractifyCPacketsToPackets(cps);
    ensures  CPacketIsAbstractable(cp);
    ensures  AbstractifyCPacketToShtPacket(cp) == p
    ensures  cp in cps;
{
    reveal_AbstractifyCPacketsToPackets();
    cp :| cp in cps && CPacketIsAbstractable(cp) && AbstractifyCPacketToShtPacket(cp) == p;
}

lemma lemma_AbstractifySeqOfCPacketsToSetOfShtPackets_reverse(cps:seq<CPacket>, p:Packet) returns (cp:CPacket)
    requires CPacketSeqIsAbstractable(cps);
    requires p in AbstractifySeqOfCPacketsToSetOfShtPackets(cps);
    ensures  CPacketIsAbstractable(cp);
    ensures  AbstractifyCPacketToShtPacket(cp) == p
    ensures  cp in cps;
{
    reveal_AbstractifySeqOfCPacketsToSetOfShtPackets();
    cp :| cp in cps && CPacketIsAbstractable(cp) && AbstractifyCPacketToShtPacket(cp) == p;
}

method RetransmitUnAckedPackets(acct:CSingleDeliveryAcct, src:EndPoint, ghost params:CParameters) returns (pkts:seq<CPacket>)
    requires CSingleDeliveryAccountIsValid(acct, params);
    requires EndPointIsAbstractable(src);
    ensures  CPacketSeqIsAbstractable(pkts);
    ensures  AbstractifySeqOfCPacketsToSetOfShtPackets(pkts) == UnAckedMessages(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct), AbstractifyEndPointToNodeIdentity(src));
    ensures (forall p :: p in pkts ==> p.src == src && p.msg.CSingleMessage? && CSingleMessageMarshallable(p.msg));
    ensures (forall i :: 0 <= i < |pkts| ==> CPacketIsSendable(pkts[i]));
    ensures (forall i :: 0 <= i < |pkts| ==> pkts[i].msg.CSingleMessage?);
    ensures (forall i :: 0 <= i < |pkts| ==> CSingleMessageMarshallable(pkts[i].msg));
{
    var pkt_set := set dst, i | dst in acct.sendState && 0 <= i < |acct.sendState[dst].unAcked| && acct.sendState[dst].unAcked[i].CSingleMessage? :: 
        var sm := acct.sendState[dst].unAcked[i];
        CPacket(sm.dst, src, sm);
    pkts := SetToUniqueSeqConstruct(pkt_set);

    // Prove that everything behaves as expected
    lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
    lemma_AbstractifyMap_properties(acct.sendState, AbstractifyEndPointToNodeIdentity, AbstractifyCAskStateToAckState, RefineNodeIdentityToEndPoint);

    ghost var r_pkt_set := AbstractifyCPacketsToPackets(pkt_set);
    ghost var r_acct := AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct);
    ghost var r_src := AbstractifyEndPointToNodeIdentity(src);
    ghost var g_set := UnAckedMessages(r_acct, r_src);

    forall p | p in g_set
        ensures p in r_pkt_set;
    {
        var dst, i :| dst in r_acct.sendState && 0 <= i < |r_acct.sendState[dst].unAcked| && r_acct.sendState[dst].unAcked[i].SingleMessage? && (var sm := r_acct.sendState[dst].unAcked[i]; p.dst == sm.dst && p.src == r_src && p.msg == sm); // Needed for the OBSERVE on the next line
        assert AckStateLookup(dst, r_acct.sendState) == r_acct.sendState[dst];  // OBSERVE
        assert UnAckedMsgForDst(r_acct, p.msg, p.dst);    // OBSERVE

        var c_dst :| c_dst in acct.sendState && AbstractifyEndPointToNodeIdentity(c_dst) == dst;
        var c_sm := acct.sendState[c_dst].unAcked[i];
        var cp := CPacket(c_sm.dst, src, c_sm);
        assert c_sm.CSingleMessage?;
        assert CSingleMessageMarshallable(c_sm);
        assert cp in pkt_set;       // OBSERVE
    }
    forall p | p in r_pkt_set
        ensures p in g_set;
    {
        var c_p := lemma_AbstractifyCPacketsToPackets_reverse(pkt_set, p);
        var dst, i :| dst in acct.sendState && 0 <= i < |acct.sendState[dst].unAcked| && acct.sendState[dst].unAcked[i].CSingleMessage? && (var sm := acct.sendState[dst].unAcked[i]; c_p.dst == sm.dst && c_p.src == src && c_p.msg == sm); // Needed for the OBSERVE below
        var r_dst := AbstractifyEndPointToNodeIdentity(dst);
        var r_sm := r_acct.sendState[r_dst].unAcked[i];
        assert Packet(r_sm.dst, r_src, r_sm) in g_set;  // OBSERVE
    }

    assert r_pkt_set == g_set;

    ghost var r_pkt_set' := AbstractifySeqOfCPacketsToSetOfShtPackets(pkts);

    forall p | p in r_pkt_set
        ensures p in r_pkt_set';
    {
        var c_p := lemma_AbstractifyCPacketsToPackets_reverse(pkt_set, p);
        assert c_p in pkt_set;
        assert c_p in pkts;      // OBSERVE
    }
    forall p | p in r_pkt_set'
        ensures p in r_pkt_set;
    {
        var c_p := lemma_AbstractifySeqOfCPacketsToSetOfShtPackets_reverse(pkts, p);
        assert c_p in pkts;
        assert c_p in pkt_set;      // OBSERVE
    }
}
                                     
} 
