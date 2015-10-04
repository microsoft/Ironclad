include "InfiniteSends.i.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"

module LivenessProof__Seqno_i {

import opened LivenessProof__InfiniteSends_i
import opened Temporal__Rules_i

lemma Lemma_IfRecipientSequenceNumberNeverBeyondThenPacketReceived(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    current_step:int,
    src_idx:int,
    dst_idx:int,
    m:SingleMessage<Message>
    ) returns
    (receive_step:int,
     ap:SHTActionParams)
    requires LivenessAssumptions(b, asp);
    requires 0 <= src_idx < |asp.c.hostIds|;
    requires 0 <= dst_idx < |asp.c.hostIds|;
    requires 0 <= src_idx < |b[current_step].hosts|;
    requires 0 <= current_step;
    requires m.SingleMessage?;
    requires m.dst == asp.c.hostIds[dst_idx];
    requires sat(current_step, always(RecipientSequenceNumberBelowTemporal(b, src_idx, dst_idx, m.seqno)));
    requires m.dst in b[current_step].hosts[src_idx].host.sd.sendState;
    requires m in b[current_step].hosts[src_idx].host.sd.sendState[m.dst].unAcked;
    ensures  current_step <= receive_step;
    ensures  SHTActionOccurred(b[receive_step], b[receive_step+1], ap);
    ensures  ap.idx == dst_idx;
    ensures  ap.nextActionIndex == 0;
    ensures  b[receive_step].hosts[dst_idx].host.receivedPacket.None?;
    ensures  |ap.ios| > 0;
    ensures  ap.ios[0] == LIoOpReceive(LPacket(m.dst, asp.c.hostIds[src_idx], m));
{
    var p := LPacket(m.dst, asp.c.hostIds[src_idx], m);
    Lemma_IfRecipientSequenceNumberNeverBeyondThenPacketSentInfinitelyOften(b, asp, current_step, src_idx, dst_idx, m);
    receive_step, ap := Lemma_PacketSentInfinitelyOftenEventuallyReceived(b, asp, current_step, src_idx, dst_idx, p);
}

lemma Lemma_IfTheresAnUnackedPacketThenRecipientSequenceNumberIncreases(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    current_step:int,
    src_idx:int,
    dst_idx:int,
    m:SingleMessage<Message>
    ) returns
    (next_step:int)
    requires LivenessAssumptions(b, asp);
    requires 0 <= src_idx < |asp.c.hostIds|;
    requires 0 <= dst_idx < |asp.c.hostIds|;
    requires 0 <= src_idx < |b[current_step].hosts|;
    requires 0 <= dst_idx < |b[current_step].hosts|;
    requires 0 <= current_step;
    requires m.SingleMessage?;
    requires m.dst == asp.c.hostIds[dst_idx];
    requires m.dst in b[current_step].hosts[src_idx].host.sd.sendState;
    requires m in b[current_step].hosts[src_idx].host.sd.sendState[m.dst].unAcked;
    requires TombstoneTableLookup(asp.c.hostIds[src_idx], b[current_step].hosts[dst_idx].host.sd.receiveState) < m.seqno;
    ensures  current_step <= next_step;
    ensures  0 <= dst_idx < |b[next_step].hosts|;
    ensures  TombstoneTableLookup(asp.c.hostIds[src_idx], b[next_step].hosts[dst_idx].host.sd.receiveState) >
             TombstoneTableLookup(asp.c.hostIds[src_idx], b[current_step].hosts[dst_idx].host.sd.receiveState);
{
    var src := asp.c.hostIds[src_idx];
    var dst := asp.c.hostIds[dst_idx];
    Lemma_GetHostIndexIsUnique(asp.c, src_idx);
    Lemma_GetHostIndexIsUnique(asp.c, dst_idx);

    Lemma_ConstantsAllConsistent(b, asp.c, current_step);
    var receiveState := b[current_step].hosts[dst_idx].host.sd.receiveState;
    var sendState := b[current_step].hosts[src_idx].host.sd.sendState;
    
    var recipientSeqno := TombstoneTableLookup(src, receiveState);
    var senderNumAcked := AckStateLookup(dst, sendState).numPacketsAcked;
    Lemma_NumPacketsAckedBeforeRecipientSequenceNumber(b, asp.c, current_step, src_idx, dst_idx);
    assert senderNumAcked <= recipientSeqno < m.seqno;
    var pos := Lemma_GetPositionOfMessageInUnackedList(b, asp.c, current_step, src_idx, dst, m);
    assert pos == m.seqno - senderNumAcked - 1 >= 0;

    var m_expected := sendState[dst].unAcked[recipientSeqno - senderNumAcked];
    Lemma_MessageInUnackedListHasParticularSeqno(b, asp.c, current_step, src_idx, dst, m_expected, recipientSeqno - senderNumAcked);
    assert m_expected.seqno == recipientSeqno + 1;
    Lemma_MessageInUnackedListHasParticularDestination(b, asp.c, current_step, src_idx, dst, m_expected);

    if sat(current_step, always(RecipientSequenceNumberBelowTemporal(b, src_idx, dst_idx, m_expected.seqno)))
    {
        var receive_step, ap := Lemma_IfRecipientSequenceNumberNeverBeyondThenPacketReceived(b, asp, current_step, src_idx, dst_idx, m_expected);
        Lemma_ConstantsAllConsistent(b, asp.c, receive_step);
        assert ap.pkt.msg == m_expected;
        var last_seqno := TombstoneTableLookup(ap.pkt.src, ap.host.sd.receiveState);
        Lemma_RecipientSequenceNumberMonotonic(b, asp.c, current_step, receive_step, src, dst_idx);
        assert last_seqno >= recipientSeqno;
        if m_expected.seqno == last_seqno + 1
        {
            assert NewSingleMessage(ap.host.sd, ap.pkt);
            next_step := receive_step + 1;
            assert TombstoneTableLookup(src, b[next_step].hosts[dst_idx].host.sd.receiveState) >= m_expected.seqno;
        }
        else
        {
            next_step := receive_step;
            assert TombstoneTableLookup(src, b[receive_step].hosts[dst_idx].host.sd.receiveState) >= m_expected.seqno;
        }
        return;
    }

    TemporalNot(current_step, RecipientSequenceNumberBelowTemporal(b, src_idx, dst_idx, m_expected.seqno));
    next_step := TemporalDeduceFromEventual(current_step, not(RecipientSequenceNumberBelowTemporal(b, src_idx, dst_idx, m_expected.seqno)));
    Lemma_ConstantsAllConsistent(b, asp.c, next_step);
}

lemma Lemma_IfTheresAnUnackedPacketThenRecipientSequenceNumberReachesItsSequenceNumber(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    current_step:int,
    src_idx:int,
    dst_idx:int,
    m:SingleMessage<Message>
    ) returns
    (next_step:int)
    requires LivenessAssumptions(b, asp);
    requires 0 <= src_idx < |asp.c.hostIds|;
    requires 0 <= dst_idx < |asp.c.hostIds|;
    requires 0 <= src_idx < |b[current_step].hosts|;
    requires 0 <= dst_idx < |b[current_step].hosts|;
    requires 0 <= current_step;
    requires m.SingleMessage?;
    requires m.dst == asp.c.hostIds[dst_idx];
    requires m.dst in b[current_step].hosts[src_idx].host.sd.sendState;
    requires m in b[current_step].hosts[src_idx].host.sd.sendState[m.dst].unAcked;
    ensures  current_step <= next_step;
    ensures  0 <= dst_idx < |b[next_step].hosts|;
    ensures  TombstoneTableLookup(asp.c.hostIds[src_idx], b[next_step].hosts[dst_idx].host.sd.receiveState) >= m.seqno;
    decreases m.seqno - TombstoneTableLookup(asp.c.hostIds[src_idx], b[current_step].hosts[dst_idx].host.sd.receiveState);
{
    var src := asp.c.hostIds[src_idx];
    var dst := asp.c.hostIds[dst_idx];
    Lemma_GetHostIndexIsUnique(asp.c, src_idx);
    Lemma_GetHostIndexIsUnique(asp.c, dst_idx);
    Lemma_ConstantsAllConsistent(b, asp.c, current_step);

    var x := RecipientSequenceNumberBelowTemporal(b, src_idx, dst_idx, m.seqno);
    if !sat(current_step, always(x))
    {
        TemporalNot(current_step, x);
        next_step := TemporalDeduceFromEventual(current_step, not(x));
        Lemma_ConstantsAllConsistent(b, asp.c, next_step);
        return;
    }

    TemporalDeduceFromAlways(current_step, current_step, x);
    assert TombstoneTableLookup(src, b[current_step].hosts[dst_idx].host.sd.receiveState) < m.seqno;

    var intermediate_step := Lemma_IfTheresAnUnackedPacketThenRecipientSequenceNumberIncreases(b, asp, current_step, src_idx, dst_idx, m);
    Lemma_ConstantsAllConsistent(b, asp.c, intermediate_step);

    TemporalDeduceFromAlways(current_step, intermediate_step, x);
    assert TombstoneTableLookup(src, b[intermediate_step].hosts[dst_idx].host.sd.receiveState) < m.seqno;

    Lemma_IfRecipientSequenceNumberNeverBeyondThenPacketStaysInSendState(b, asp, current_step, intermediate_step, src_idx, dst_idx, m);
    next_step := Lemma_IfTheresAnUnackedPacketThenRecipientSequenceNumberReachesItsSequenceNumber(b, asp, intermediate_step, src_idx, dst_idx, m);
    Lemma_ConstantsAllConsistent(b, asp.c, next_step);
}

lemma Lemma_GetReceiveStepForSequenceNumber(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    j:int,
    src_idx:int,
    dst_idx:int,
    seqno:int
    ) returns
    (receive_step:int,
     ap:SHTActionParams)
    requires IsValidBehaviorPrefix(b, c, j);
    requires 0 <= i <= j;
    requires |c.hostIds| == |b[i].hosts| == |b[j].hosts|;
    requires 0 <= src_idx < |c.hostIds|;
    requires 0 <= dst_idx < |c.hostIds|;
    requires TombstoneTableLookup(c.hostIds[src_idx], b[i].hosts[dst_idx].host.sd.receiveState) < seqno;
    requires TombstoneTableLookup(c.hostIds[src_idx], b[j].hosts[dst_idx].host.sd.receiveState) >= seqno;
    ensures  i <= receive_step < j;
    ensures  SHTActionOccurred(b[receive_step], b[receive_step+1], ap);
    ensures  ap.idx == dst_idx;
    ensures  ap.nextActionIndex == 0;
    ensures  b[receive_step].hosts[dst_idx].host.receivedPacket.None?;
    ensures  b[receive_step+1].hosts[dst_idx].host.receivedPacket.Some?;
    ensures  ap.pkt.msg.SingleMessage?;
    ensures  ap.pkt.msg.seqno == seqno;
    ensures  |ap.ios| > 0;
    ensures  ap.ios[0].LIoOpReceive?;
    ensures  ap.ios[0].r.msg == ap.pkt.msg;
    ensures  ap.ios[0].r.src == c.hostIds[src_idx];
{
    Lemma_ConstantsAllConsistent(b, c, i);
    Lemma_ConstantsAllConsistent(b, c, j);

    var x := RecipientSequenceNumberBelowTemporal(b, src_idx, dst_idx, seqno);
    receive_step := earliestStepBetween(i, j, not(x)) - 1;
    assert i <= receive_step < j;
    assert sat(receive_step, x);
    assert sat(receive_step + 1, not(x));
 
    Lemma_ConstantsAllConsistent(b, c, receive_step);
    Lemma_AssumptionsMakeValidTransition(b, c, receive_step);
    ap := Lemma_ActionThatChangesHostIsThatHostsAction(b, c, receive_step, dst_idx);
}

}
