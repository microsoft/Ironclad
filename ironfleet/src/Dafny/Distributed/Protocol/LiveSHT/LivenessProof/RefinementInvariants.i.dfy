include "Constants.i.dfy"
include "Actions.i.dfy"
include "../../SHT/RefinementProof/RefinementProof.i.dfy"
include "../RefinementProof/SHTRefinement.i.dfy"
include "../RefinementProof/SHTLemmas.i.dfy"

module LivenessProof__RefinementInvariants_i {
import opened LivenessProof__Constants_i
import opened LivenessProof__Actions_i
import opened SHT__RefinementProof_i
import opened LiveSHT__SHTRefinement_i
import opened RefinementProof__DistributedSystemLemmas_i

function PacketToLSHTPacket(p:Packet) : LSHTPacket
{
    LPacket(p.dst, p.src, p.msg)
}

lemma Lemma_ActionMaintainsMapComplete(
    ss:LSHT_State,
    ss':LSHT_State,
    ap:SHTActionParams
    )
    requires SHTActionOccurred(ss, ss', ap);
    requires LSHTState_RefinementInvariant(ss);
    requires MapComplete(LSHTState_Refine(ss));
    requires ss'.config == ss.config;
    requires LSHT_Next(ss, ss');
    ensures  LSHTState_RefinementInvariant(ss');
    ensures  MapComplete(LSHTState_Refine(ss'));
{
    var h_s := LSHTState_Refine(ss);

    forall idx | 0 <= idx < |ss'.config.hostIds|
        ensures DelegationMapComplete(ss'.hosts[idx].host.delegationMap);
    {
        var id := ss.config.hostIds[idx];
        Lemma_GetHostIndexIsUnique(ss.config, idx);
        assert DelegationMapComplete(h_s.hosts[id].delegationMap);
        assert DelegationMapComplete(ss.hosts[idx].host.delegationMap);
    }
}

lemma Lemma_RefinementInvariantHolds(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int
    )
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    ensures  LSHTState_RefinementInvariant(b[i]);
    ensures  Inv(LSHTState_Refine(b[i]));
{
    if i == 0
    {
        InitInv(c, LSHTState_Refine(b[i]));
        return;
    }

    Lemma_RefinementInvariantHolds(b, c, i-1);
    Lemma_AssumptionsMakeValidTransition(b, c, i-1);
    Lemma_ConstantsAllConsistent(b, c, i-1);

    var h_s := LSHTState_Refine(b[i-1]);
    var h_s' := LSHTState_Refine(b[i]);

    if b[i-1].environment.nextStep.LEnvStepHostIos?
    {
        if b[i-1].environment.nextStep.actor in b[i-1].config.hostIds {
            var ap := Lemma_GetParametersOfAction(b, c, i-1);
            Lemma_ActionMaintainsMapComplete(b[i-1], b[i], ap);
            var id := c.hostIds[ap.idx];
            assert ap.out == LSHTIoSeq_RefineAsSends(ap.ios);

            if ap.nextActionIndex == 0
            {
                if ap.ios[0].LIoOpTimeoutReceive?
                {
                    assert h_s'.hosts == h_s.hosts;
                    assert h_s'.network == h_s.network;
                    assert h_s == h_s';
                }
                else
                {
                    assert SHT_NextPred(h_s, h_s', id, ap.recv, ap.out);
                    NextInv(h_s, h_s');
                }
            }
            else if ap.nextActionIndex == 1
            {
                assert SHT_NextPred(h_s, h_s', id, ap.recv, ap.out);
                NextInv(h_s, h_s');
            }
            else if ap.nextActionIndex == 2
            {
                if ap.resendCount == 0
                {
                    assert SHT_NextPred(h_s, h_s', id, ap.recv, ap.out);
                    NextInv(h_s, h_s');
                }
                else
                {
                    assert h_s'.hosts == h_s.hosts;
                    assert h_s'.network == h_s.network;
                    assert h_s == h_s';
                }
            }
            else
            {
                assert false;
            }
        } else {
            var s := b[i-1];
            var s' := b[i];

            assert exists idx, ios :: LSHT_NextExternal(s, s', idx, ios);
            var idx, ios :| LSHT_NextExternal(s, s', idx, ios);
            assert SHT_NextExternal(h_s, h_s', idx, {}, LSHTIoSeq_RefineAsSends(ios));
            NextInv(h_s, h_s');
        }
    }
    else
    {
        assert LSHT_NextEnvironment(b[i-1], b[i]);
        assert h_s'.hosts == h_s.hosts;
        assert h_s'.network == h_s.network;
    }
}

lemma Lemma_PacketsHaveSenderUniqueSeqnos(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    p1:LSHTPacket,
    p2:LSHTPacket
    )
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires p1 in b[i].environment.sentPackets;
    requires p2 in b[i].environment.sentPackets;
    requires p1.msg.SingleMessage?;
    requires p2.msg.SingleMessage?;
    requires p1.src == p2.src;
    requires p1.dst == p2.dst;
    requires p1.src in b[i].config.hostIds && p1.dst in b[i].config.hostIds;
    requires p2.src in b[i].config.hostIds && p2.dst in b[i].config.hostIds;
    requires p1.msg.seqno == p2.msg.seqno;
    ensures  p1 == p2;
{
    Lemma_RefinementInvariantHolds(b, c, i);

    var s := LSHTState_Refine(b[i]);
    reveal_PacketsHaveSenderUniqueSeqnos();

    assert LSHTPacketToPacket(p1) in s.network;
    assert LSHTPacketToPacket(p2) in s.network;
}

lemma Lemma_ReceiverHasCanceledNoUnsentSeqno(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    src_idx:int,
    dst_idx:int
    )
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= src_idx < |c.hostIds|;
    requires 0 <= dst_idx < |c.hostIds|;
    ensures  0 <= src_idx < |b[i].hosts|;
    ensures  0 <= dst_idx < |b[i].hosts|;
    ensures  HighestSeqnoSent(b[i].hosts[src_idx].host.sd, c.hostIds[dst_idx]) >=
                 TombstoneTableLookup(c.hostIds[src_idx], b[i].hosts[dst_idx].host.sd.receiveState);
{
    Lemma_ConstantsAllConsistent(b, c, i);

    var s := LSHTState_Refine(b[i]);

    Lemma_GetHostIndexIsUnique(b[i].config, src_idx);
    Lemma_GetHostIndexIsUnique(b[i].config, dst_idx);

    var src := c.hostIds[src_idx];
    var dst := c.hostIds[dst_idx];
    var seqno := HighestSeqnoSent(b[i].hosts[src_idx].host.sd, c.hostIds[dst_idx]) + 1;

    Lemma_RefinementInvariantHolds(b, c, i);
    assert ReceiverHasNotCanceledUnsentSeqno(s, dst, src, seqno);
    assert seqno > TombstoneTableLookup(src, s.hosts[dst].sd.receiveState);
}

lemma Lemma_MessageInUnackedListHasParticularSeqno(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    src_idx:int,
    dst:NodeIdentity,
    m:SingleMessage<Message>,
    pos:int
    )
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= src_idx < |c.hostIds|;
    requires 0 <= src_idx < |b[i].hosts|;
    requires dst in c.hostIds;
    requires dst in b[i].hosts[src_idx].host.sd.sendState;
    requires 0 <= pos < |b[i].hosts[src_idx].host.sd.sendState[dst].unAcked|;
    requires m == b[i].hosts[src_idx].host.sd.sendState[dst].unAcked[pos];
    ensures  m.SingleMessage?;
    ensures  m.seqno == b[i].hosts[src_idx].host.sd.sendState[dst].numPacketsAcked + pos + 1;
    decreases pos;
{
    Lemma_ConstantsAllConsistent(b, c, i);

    var s := LSHTState_Refine(b[i]);
    Lemma_GetHostIndexIsUnique(b[i].config, src_idx);

    var src := c.hostIds[src_idx];
    var ackState := s.hosts[src].sd;
    var unAcked := AckStateLookup(dst, ackState.sendState).unAcked;

    Lemma_RefinementInvariantHolds(b, c, i);
    assert AckListsInv(s);
    assert dst in AllHostIdentities(s);
    assert UnAckedListProperties(ackState);

    assert NoAcksInUnAckedLists(ackState);
    assert 0 <= pos < |unAcked|;
    assert unAcked[pos].SingleMessage?;

    if pos == 0
    {
        assert UnAckedListExceedsNumPacketsAcked(ackState);
    }
    else
    {
        Lemma_MessageInUnackedListHasParticularSeqno(b, c, i, src_idx, dst, unAcked[pos-1], pos-1);
        assert UnAckedListsSequential(ackState);
        assert unAcked[pos].seqno == unAcked[pos-1].seqno + 1;
    }
}

lemma Lemma_GetPositionOfMessageInUnackedList(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    src_idx:int,
    dst:NodeIdentity,
    m:SingleMessage<Message>
    )
    returns
    (pos:int)
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= src_idx < |c.hostIds|;
    requires 0 <= src_idx < |b[i].hosts|;
    requires dst in c.hostIds;
    requires dst in b[i].hosts[src_idx].host.sd.sendState;
    requires m in b[i].hosts[src_idx].host.sd.sendState[dst].unAcked;
    ensures  0 <= pos < |b[i].hosts[src_idx].host.sd.sendState[dst].unAcked|;
    ensures  m == b[i].hosts[src_idx].host.sd.sendState[dst].unAcked[pos];
    ensures  m.SingleMessage?;
    ensures  pos == m.seqno - b[i].hosts[src_idx].host.sd.sendState[dst].numPacketsAcked - 1;
{
    Lemma_ConstantsAllConsistent(b, c, i);
    pos :| 0 <= pos < |b[i].hosts[src_idx].host.sd.sendState[dst].unAcked| && b[i].hosts[src_idx].host.sd.sendState[dst].unAcked[pos] == m;
    Lemma_MessageInUnackedListHasParticularSeqno(b, c, i, src_idx, dst, m, pos);
}

lemma Lemma_MessageInUnackedListHasParticularDestination(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    src_idx:int,
    dst:NodeIdentity,
    m:SingleMessage<Message>
    )
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= src_idx < |c.hostIds|;
    requires 0 <= src_idx < |b[i].hosts|;
    requires dst in b[i].hosts[src_idx].host.sd.sendState;
    requires m in b[i].hosts[src_idx].host.sd.sendState[dst].unAcked;
    ensures  m.SingleMessage?;
    ensures  m.dst == dst;
{
    Lemma_ConstantsAllConsistent(b, c, i);

    var s := LSHTState_Refine(b[i]);
    Lemma_GetHostIndexIsUnique(b[i].config, src_idx);

    var src := c.hostIds[src_idx];
    var ackState := s.hosts[src].sd;
    var unAcked := AckStateLookup(dst, ackState.sendState).unAcked;

    Lemma_RefinementInvariantHolds(b, c, i);
    assert AckListsInv(s);
    assert UnAckedListProperties(ackState);

    var pos :| 0 <= pos < |unAcked| && unAcked[pos] == m;
    assert NoAcksInUnAckedLists(ackState);
    assert 0 <= pos < |unAcked|;
    assert unAcked[pos].SingleMessage?;

    assert UnAckedDstsConsistent(ackState);
    assert m.dst == dst;
}

lemma Lemma_HostConstantsMeHasAppropriateValue(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    idx:int
    )
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= idx < |c.hostIds|;
    ensures  0 <= idx < |b[i].hosts|;
    ensures  b[i].hosts[idx].host.me == c.hostIds[idx];
{
    Lemma_ConstantsAllConsistent(b, c, i);

    var s := LSHTState_Refine(b[i]);

    Lemma_RefinementInvariantHolds(b, c, i);
    assert InvConstants(s);
    var id := c.hostIds[idx];
    assert id in AllHostIdentities(s);
}

lemma Lemma_ReceivedPacketWasSent(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    idx:int
    )
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= idx < |b[i].hosts|;
    requires b[i].hosts[idx].host.receivedPacket.Some?;
    ensures  PacketToLSHTPacket(b[i].hosts[idx].host.receivedPacket.v) in b[i].environment.sentPackets;
{
    Lemma_ConstantsAllConsistent(b, c, i);

    var s := LSHTState_Refine(b[i]);

    Lemma_RefinementInvariantHolds(b, c, i);
    assert BufferedPacketsInv(s);
    var id := c.hostIds[idx];
    Lemma_GetHostIndexIsUnique(c, idx);
    assert id in AllHostIdentities(s);
}

lemma Lemma_UnAckedPacketInNetwork(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    idx:int,
    p:LSHTPacket
    )
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= idx < |b[i].hosts|;
    requires 0 <= idx < |c.hostIds|;
    requires p.msg in AckStateLookup(p.dst, b[i].hosts[idx].host.sd.sendState).unAcked;
    requires p.src == c.hostIds[idx];
    ensures  p in b[i].environment.sentPackets;
{
    Lemma_ConstantsAllConsistent(b, c, i);

    var s := LSHTState_Refine(b[i]);

    Lemma_RefinementInvariantHolds(b, c, i);

    var id := c.hostIds[idx];
    Lemma_GetHostIndexIsUnique(c, idx);
    assert UnAckedListProperties(s.hosts[id].sd);
    assert NoAcksInUnAckedLists(s.hosts[id].sd);
    assert UnAckedListInNetwork(s);
    reveal_UnAckedListInNetwork();

    assert id in AllHostIdentities(s);
    assert p.msg in AckStateLookup(p.dst, s.hosts[id].sd.sendState).unAcked;
    assert Packet(p.msg.dst, s.hosts[id].me, p.msg) in s.network;
    Lemma_HostConstantsMeHasAppropriateValue(b, c, i, idx);
}

}
