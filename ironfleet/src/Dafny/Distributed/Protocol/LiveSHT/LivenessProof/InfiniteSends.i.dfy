include "PacketReceipt.i.dfy"
include "Acks.i.dfy"
include "RefinementInvariants.i.dfy"

module LivenessProof__InfiniteSends_i {

import opened LivenessProof__PacketReceipt_i
import opened LivenessProof__Acks_i
import opened LivenessProof__RefinementInvariants_i

predicate RecipientSequenceNumberBelow(
    ss:LSHT_State,
    src_idx:int,
    dst_idx:int,
    seqno:int
    )
{
       0 <= src_idx < |ss.config.hostIds|
    && 0 <= dst_idx < |ss.config.hostIds|
    && 0 <= dst_idx < |ss.hosts|
    && TombstoneTableLookup(ss.config.hostIds[src_idx], ss.hosts[dst_idx].host.sd.receiveState) < seqno
}

function RecipientSequenceNumberBelowTemporal(
    b:Behavior<LSHT_State>,
    src_idx:int,
    dst_idx:int,
    seqno:int
    ):temporal
    requires imaptotal(b);
    ensures  forall i{:trigger sat(i, RecipientSequenceNumberBelowTemporal(b, src_idx, dst_idx, seqno))} ::
             sat(i, RecipientSequenceNumberBelowTemporal(b, src_idx, dst_idx, seqno)) <==>
             RecipientSequenceNumberBelow(b[i], src_idx, dst_idx, seqno);
{
    stepmap(imap i :: RecipientSequenceNumberBelow(b[i], src_idx, dst_idx, seqno))
}

lemma Lemma_TruncateUnAckListDoesntRemoveHigherSeqno<MT>(
    unAcked:seq<SingleMessage<MT>>,
    seqnoAcked:nat,
    unAcked':seq<SingleMessage<MT>>,
    m:SingleMessage<MT>
    )
    requires unAcked' == TruncateUnAckList(unAcked, seqnoAcked);
    requires m in unAcked;
    requires m.SingleMessage?;
    requires m.seqno > seqnoAcked;
    ensures  m in unAcked';
{
    if |unAcked| > 0 && unAcked[0].SingleMessage? && unAcked[0].seqno <= seqnoAcked
    {
        assert m != unAcked[0];
        assert m in unAcked[1..];
        Lemma_TruncateUnAckListDoesntRemoveHigherSeqno(unAcked[1..], seqnoAcked, unAcked', m);
    }
}

lemma Lemma_IfRecipientSequenceNumberNeverBeyondThenPacketStaysInSendStateOneStep(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    i:int,
    src_idx:int,
    dst_idx:int,
    m:SingleMessage<Message>
    )
    requires LivenessAssumptions(b, asp);
    requires 0 <= src_idx < |asp.c.hostIds|;
    requires 0 <= dst_idx < |asp.c.hostIds|;
    requires 0 <= src_idx < |b[i].hosts|;
    requires 0 <= i;
    requires m.SingleMessage?;
    requires m.dst == asp.c.hostIds[dst_idx];
    requires sat(i, always(RecipientSequenceNumberBelowTemporal(b, src_idx, dst_idx, m.seqno)));
    requires m.dst in b[i].hosts[src_idx].host.sd.sendState;
    requires m in b[i].hosts[src_idx].host.sd.sendState[m.dst].unAcked;
    ensures  0 <= src_idx < |b[i+1].hosts|;
    ensures  m.dst in b[i+1].hosts[src_idx].host.sd.sendState;
    ensures  m in b[i+1].hosts[src_idx].host.sd.sendState[m.dst].unAcked;
{
    Lemma_AssumptionsMakeValidTransition(b, asp.c, i);
    Lemma_ConstantsAllConsistent(b, asp.c, i);

    var src := asp.c.hostIds[src_idx];
    var dst := asp.c.hostIds[dst_idx];
    Lemma_GetHostIndexIsUnique(asp.c, src_idx);
    Lemma_GetHostIndexIsUnique(asp.c, dst_idx);
    var host := b[i].hosts[src_idx].host;
    var host' := b[i+1].hosts[src_idx].host;
    
    TemporalDeduceFromAlways(i, i, RecipientSequenceNumberBelowTemporal(b, src_idx, dst_idx, m.seqno));
    Lemma_NumPacketsAckedBeforeRecipientSequenceNumber(b, asp.c, i, src_idx, dst_idx);
    assert AckStateLookup(dst, host.sd.sendState).numPacketsAcked < m.seqno;

    TemporalDeduceFromAlways(i, i+1, RecipientSequenceNumberBelowTemporal(b, src_idx, dst_idx, m.seqno));
    Lemma_NumPacketsAckedBeforeRecipientSequenceNumber(b, asp.c, i+1, src_idx, dst_idx);
    assert AckStateLookup(dst, host'.sd.sendState).numPacketsAcked < m.seqno;
    
    assert dst in host'.sd.sendState;
    if m in host'.sd.sendState[dst].unAcked
    {
        return;
    }

    var ap := Lemma_ActionThatChangesHostIsThatHostsAction(b, asp.c, i, src_idx);
    var pos :| 0 <= pos < |host.sd.sendState[dst].unAcked| && m == host.sd.sendState[dst].unAcked[pos];

    assert ap.nextActionIndex == 0;
    assert ap.ios[0].LIoOpReceive?;
    assert ap.ios[0].r.msg.Ack?;
    assert ReceiveAck(host.sd, host'.sd, ap.pkt, ap.out);
    assert host'.sd.sendState[dst].unAcked == TruncateUnAckList(host.sd.sendState[dst].unAcked, host'.sd.sendState[dst].numPacketsAcked);
    Lemma_TruncateUnAckListDoesntRemoveHigherSeqno(host.sd.sendState[dst].unAcked, host'.sd.sendState[dst].numPacketsAcked,
                                                   host'.sd.sendState[dst].unAcked, m);
}

lemma Lemma_IfRecipientSequenceNumberNeverBeyondThenPacketStaysInSendState(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    i:int,
    j:int,
    src_idx:int,
    dst_idx:int,
    m:SingleMessage<Message>
    )
    requires LivenessAssumptions(b, asp);
    requires 0 <= src_idx < |asp.c.hostIds|;
    requires 0 <= dst_idx < |asp.c.hostIds|;
    requires 0 <= src_idx < |b[i].hosts|;
    requires 0 <= i <= j;
    requires m.SingleMessage?;
    requires m.dst == asp.c.hostIds[dst_idx];
    requires sat(i, always(RecipientSequenceNumberBelowTemporal(b, src_idx, dst_idx, m.seqno)));
    requires m.dst in b[i].hosts[src_idx].host.sd.sendState;
    requires m in b[i].hosts[src_idx].host.sd.sendState[m.dst].unAcked;
    ensures  0 <= src_idx < |b[j].hosts|;
    ensures  m.dst in b[j].hosts[src_idx].host.sd.sendState;
    ensures  m in b[j].hosts[src_idx].host.sd.sendState[m.dst].unAcked;
{
    if i == j
    {
        return;
    }

    Lemma_IfRecipientSequenceNumberNeverBeyondThenPacketStaysInSendState(b, asp, i, j-1, src_idx, dst_idx, m);
    Lemma_AlwaysImpliesLaterAlways(i, j-1, RecipientSequenceNumberBelowTemporal(b, src_idx, dst_idx, m.seqno));
    Lemma_IfRecipientSequenceNumberNeverBeyondThenPacketStaysInSendStateOneStep(b, asp, j-1, src_idx, dst_idx, m);
}

lemma Lemma_ResendCountAlwaysWithinRange(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    idx:int
    )
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= idx < |c.hostIds|;
    ensures  0 <= idx < |b[i].hosts|;
    ensures  0 <= b[i].hosts[idx].resendCount < 100000000;
{
    if i == 0
    {
        return;
    }

    Lemma_AssumptionsMakeValidTransition(b, c, i-1);
    Lemma_ConstantsAllConsistent(b, c, i-1);
    Lemma_ConstantsAllConsistent(b, c, i);
    Lemma_ResendCountAlwaysWithinRange(b, c, i-1, idx);

    var s := b[i-1].hosts[idx];
    var s' := b[i].hosts[idx];

    if s'.resendCount == s.resendCount
    {
        return;
    }

    var ap := Lemma_ActionThatChangesHostIsThatHostsAction(b, c, i-1, idx);
    assert LScheduler_Next(b[i-1].hosts[idx], b[i].hosts[idx], ap.ios);
    assert s'.resendCount == (s.resendCount + 1) % 100000000;
    lemma_mod_auto(100000000);
}

lemma Lemma_HostPerformsMaybeResendPacketsEventually(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    current_step:int,
    idx:int,
    resendCount:int
    ) returns
    (resend_step:int,
     ap:SHTActionParams)
    requires LivenessAssumptions(b, asp);
    requires 0 <= current_step;
    requires 0 <= idx < |asp.c.hostIds|;
    requires 0 <= idx < |b[current_step].hosts|;
    requires b[current_step].hosts[idx].resendCount == resendCount;
    requires 0 <= resendCount < 100000000;
    ensures  current_step <= resend_step;
    ensures  SHTActionOccurred(b[resend_step], b[resend_step+1], ap);
    ensures  ap.idx == idx;
    ensures  ap.nextActionIndex == 2;
    ensures  ap.resendCount == (resendCount + 1) % 100000000;
{
    var id := asp.c.hostIds[idx];
    Lemma_GetHostIndexIsUnique(asp.c, idx);

    var action_step := Lemma_HostNextPerformsSubactionEventually(b, asp, idx, current_step, 2);
    var P := stepmap(imap i ::   0 <= idx < |b[i].hosts|
                             && b[i].hosts[idx].resendCount == resendCount);
    var Q := stepmap(imap i ::   0 <= idx < |b[i].hosts|
                             && b[i].environment.nextStep.LEnvStepHostIos?
                             && b[i].environment.nextStep.actor == id
                             && b[i].hosts[idx].nextActionIndex == 2
                             && b[i].hosts[idx].resendCount == resendCount);
    if sat(action_step, P)
    {
        var ap_local := Lemma_GetParametersOfAction(b, asp.c, action_step);
        Lemma_ConstantsAllConsistent(b, asp.c, action_step);
        assert sat(action_step, Q);
    }
    assert sat(action_step, imply(P, or(Q, next(Q))));

    forall j | current_step <= j
        ensures sat(j, TemporalWF1Req1(P, Q));
    {
        Lemma_ConstantsAllConsistent(b, asp.c, j);
        Lemma_ConstantsAllConsistent(b, asp.c, j+1);
        if sat(j, P) && !sat(j+1, P) && !sat(j, Q)
        {
            var ap_local := Lemma_ActionThatChangesHostIsThatHostsAction(b, asp.c, j, idx);
            assert false;
        }
    }

    resend_step := TemporalWF1Specific(current_step, action_step, P, Q);
    Lemma_ConstantsAllConsistent(b, asp.c, resend_step);
    ap := Lemma_GetParametersOfAction(b, asp.c, resend_step);
}

lemma Lemma_HostPerformsResendPacketsEventually(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    current_step:int,
    idx:int
    ) returns
    (resend_step:int,
     ap:SHTActionParams)
    requires LivenessAssumptions(b, asp);
    requires 0 <= current_step;
    requires 0 <= idx < |asp.c.hostIds|;
    ensures  current_step <= resend_step;
    ensures  SHTActionOccurred(b[resend_step], b[resend_step+1], ap);
    ensures  ap.idx == idx;
    ensures  ap.nextActionIndex == 2;
    ensures  ap.resendCount == 0;
    decreases 100000000 - (if 0 <= idx < |b[current_step].hosts| then b[current_step].hosts[idx].resendCount else 0);
{
    Lemma_ConstantsAllConsistent(b, asp.c, current_step);
    var resendCount := b[current_step].hosts[idx].resendCount;
    Lemma_ResendCountAlwaysWithinRange(b, asp.c, current_step, idx);

    if resendCount == 100000000-1
    {
        resend_step, ap := Lemma_HostPerformsMaybeResendPacketsEventually(b, asp, current_step, idx, resendCount);
    }
    else
    {
        var try_resend_step, try_ap := Lemma_HostPerformsMaybeResendPacketsEventually(b, asp, current_step, idx, resendCount);
        lemma_mod_auto(100000000);
        resend_step, ap := Lemma_HostPerformsResendPacketsEventually(b, asp, try_resend_step + 1, idx);
    }
}

lemma Lemma_IfRecipientSequenceNumberNeverBeyondThenPacketEventuallySent(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    current_step:int,
    src_idx:int,
    dst_idx:int,
    m:SingleMessage<Message>
    ) returns
    (resend_step:int,
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
    ensures  current_step <= resend_step;
    ensures  SHTActionOccurred(b[resend_step], b[resend_step+1], ap);
    ensures  LIoOpSend(LPacket(m.dst, asp.c.hostIds[src_idx], m)) in ap.ios;
{
    resend_step, ap := Lemma_HostPerformsResendPacketsEventually(b, asp, current_step, src_idx);
    Lemma_GetHostIndexIsUnique(asp.c, ap.idx);
    Lemma_GetHostIndexIsUnique(asp.c, src_idx);
    Lemma_IfRecipientSequenceNumberNeverBeyondThenPacketStaysInSendState(b, asp, current_step, resend_step, src_idx, dst_idx, m);
    assert SpontaneouslyRetransmit(ap.host, ap.host', ap.out);
    assert ap.out == UnAckedMessages(ap.host.sd, ap.host.me);
    var pos :| 0 <= pos < |ap.host.sd.sendState[m.dst].unAcked| && ap.host.sd.sendState[m.dst].unAcked[pos] == m;
    assert Packet(m.dst, ap.host.me, m) in ap.out;
    Lemma_HostConstantsMeHasAppropriateValue(b, asp.c, resend_step, src_idx);
}

lemma Lemma_IfRecipientSequenceNumberNeverBeyondThenPacketSentInfinitelyOften(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    current_step:int,
    src_idx:int,
    dst_idx:int,
    m:SingleMessage<Message>
    )
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
    ensures  sat(current_step, always(eventual(SHTPacketSentTemporal(b, LPacket(m.dst, asp.c.hostIds[src_idx], m)))));
{
    var p := LPacket(m.dst, asp.c.hostIds[src_idx], m);

    forall later_step | current_step <= later_step
        ensures sat(later_step, eventual(SHTPacketSentTemporal(b, p)));
    {
        Lemma_ConstantsAllConsistent(b, asp.c, later_step);
        Lemma_AlwaysImpliesLaterAlways(current_step, later_step, RecipientSequenceNumberBelowTemporal(b, src_idx, dst_idx, m.seqno));
        Lemma_IfRecipientSequenceNumberNeverBeyondThenPacketStaysInSendState(b, asp, current_step, later_step, src_idx, dst_idx, m);
        var resend_step, ap := Lemma_IfRecipientSequenceNumberNeverBeyondThenPacketEventuallySent(b, asp, later_step, src_idx, dst_idx, m);
        Lemma_ConstantsAllConsistent(b, asp.c, resend_step);
        assert SHTPacketSent(b[resend_step], p);
        TemporalEventually(later_step, resend_step, SHTPacketSentTemporal(b, p));
    }

    TemporalAlways(current_step, eventual(SHTPacketSentTemporal(b, p)));
}

}
