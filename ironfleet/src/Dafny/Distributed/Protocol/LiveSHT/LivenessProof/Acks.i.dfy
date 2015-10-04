include "Constants.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"

module LivenessProof__Acks_i {
import opened LivenessProof__Constants_i
import opened LivenessProof__Actions_i
import opened LivenessProof__PacketSending_i

lemma Lemma_RecipientSequenceNumberMonotonicOneStep(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    sender:NodeIdentity,
    recipient_idx:int
    )
    requires IsValidBehaviorPrefix(b, c, i+1);
    requires 0 <= i;
    requires 0 <= recipient_idx < |c.hostIds|;
    ensures  0 <= recipient_idx < |b[i].hosts|;
    ensures  0 <= recipient_idx < |b[i+1].hosts|;
    ensures  TombstoneTableLookup(sender, b[i+1].hosts[recipient_idx].host.sd.receiveState) >= TombstoneTableLookup(sender, b[i].hosts[recipient_idx].host.sd.receiveState);
{
    Lemma_ConstantsAllConsistent(b, c, i);
    Lemma_ConstantsAllConsistent(b, c, i+1);
    Lemma_AssumptionsMakeValidTransition(b, c, i);

    if b[i+1].hosts[recipient_idx] == b[i].hosts[recipient_idx]
    {
        return;
    }

    var ap := Lemma_ActionThatChangesHostIsThatHostsAction(b, c, i, recipient_idx);
}

lemma Lemma_RecipientSequenceNumberMonotonic(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    j:int,
    sender:NodeIdentity,
    recipient_idx:int
    )
    requires IsValidBehaviorPrefix(b, c, j);
    requires 0 <= i <= j;
    requires 0 <= recipient_idx < |c.hostIds|;
    ensures  0 <= recipient_idx < |b[i].hosts|;
    ensures  0 <= recipient_idx < |b[j].hosts|;
    ensures  TombstoneTableLookup(sender, b[j].hosts[recipient_idx].host.sd.receiveState) >= TombstoneTableLookup(sender, b[i].hosts[recipient_idx].host.sd.receiveState);
{
    if i == j
    {
        Lemma_ConstantsAllConsistent(b, c, i);
        return;
    }

    Lemma_RecipientSequenceNumberMonotonic(b, c, i, j-1, sender, recipient_idx);
    Lemma_RecipientSequenceNumberMonotonicOneStep(b, c, j-1, sender, recipient_idx);
}

lemma Lemma_SenderSequenceNumberMonotonicOneStep(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    recipient:NodeIdentity,
    sender_idx:int
    )
    requires IsValidBehaviorPrefix(b, c, i+1);
    requires 0 <= i;
    requires 0 <= sender_idx < |c.hostIds|;
    ensures  0 <= sender_idx < |b[i].hosts|;
    ensures  0 <= sender_idx < |b[i+1].hosts|;
    ensures  AckStateLookup(recipient, b[i+1].hosts[sender_idx].host.sd.sendState).numPacketsAcked >=
             AckStateLookup(recipient, b[i].hosts[sender_idx].host.sd.sendState).numPacketsAcked;
{
    Lemma_ConstantsAllConsistent(b, c, i);
    Lemma_ConstantsAllConsistent(b, c, i+1);
    Lemma_AssumptionsMakeValidTransition(b, c, i);

    if b[i+1].hosts[sender_idx] == b[i].hosts[sender_idx]
    {
        return;
    }

    var ap := Lemma_ActionThatChangesHostIsThatHostsAction(b, c, i, sender_idx);
}

lemma Lemma_SenderSequenceNumberMonotonic(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    j:int,
    recipient:NodeIdentity,
    sender_idx:int
    )
    requires IsValidBehaviorPrefix(b, c, j);
    requires 0 <= i <= j;
    requires 0 <= sender_idx < |c.hostIds|;
    ensures  0 <= sender_idx < |b[i].hosts|;
    ensures  0 <= sender_idx < |b[j].hosts|;
    ensures  AckStateLookup(recipient, b[j].hosts[sender_idx].host.sd.sendState).numPacketsAcked >=
             AckStateLookup(recipient, b[i].hosts[sender_idx].host.sd.sendState).numPacketsAcked;
{
    if i == j
    {
        Lemma_ConstantsAllConsistent(b, c, i);
        return;
    }

    Lemma_SenderSequenceNumberMonotonic(b, c, i, j-1, recipient, sender_idx);
    Lemma_SenderSequenceNumberMonotonicOneStep(b, c, j-1, recipient, sender_idx);
}

lemma Lemma_AckPacketBeforeSenderSequenceNumber(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    src_idx:int,
    dst_idx:int,
    p:LSHTPacket
    )
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires p in b[i].environment.sentPackets;
    requires p.msg.Ack?;
    requires 0 <= src_idx < |c.hostIds|;
    requires 0 <= dst_idx < |c.hostIds|;
    requires p.src == c.hostIds[dst_idx];
    requires p.dst == c.hostIds[src_idx];
    ensures  0 <= dst_idx < |b[i].hosts|;
    ensures  TombstoneTableLookup(c.hostIds[src_idx], b[i].hosts[dst_idx].host.sd.receiveState) >= p.msg.ack_seqno;
{
    if i == 0
    {
        return;
    }

    Lemma_AssumptionsMakeValidTransition(b, c, i-1);
    Lemma_ConstantsAllConsistent(b, c, i-1);

    if p in b[i-1].environment.sentPackets
    {
        Lemma_AckPacketBeforeSenderSequenceNumber(b, c, i-1, src_idx, dst_idx, p);
        Lemma_RecipientSequenceNumberMonotonicOneStep(b, c, i-1, c.hostIds[src_idx], dst_idx);
        return;
    }

    var ap := Lemma_ActionThatSendsPacketIsActionOfSource(b, c, i-1, p);
    Lemma_GetHostIndexIsUnique(c, src_idx);
    Lemma_GetHostIndexIsUnique(c, dst_idx);
}

lemma Lemma_NumPacketsAckedBeforeRecipientSequenceNumber(
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
    ensures  TombstoneTableLookup(c.hostIds[src_idx], b[i].hosts[dst_idx].host.sd.receiveState) >=
             AckStateLookup(c.hostIds[dst_idx], b[i].hosts[src_idx].host.sd.sendState).numPacketsAcked;
{
    if i == 0
    {
        return;
    }

    Lemma_AssumptionsMakeValidTransition(b, c, i-1);
    Lemma_ConstantsAllConsistent(b, c, i-1);
    var src := c.hostIds[src_idx];
    var dst := c.hostIds[dst_idx];
    var host := b[i-1].hosts[src_idx].host;
    var host' := b[i].hosts[src_idx].host;
    
    Lemma_NumPacketsAckedBeforeRecipientSequenceNumber(b, c, i-1, src_idx, dst_idx);
    Lemma_RecipientSequenceNumberMonotonicOneStep(b, c, i-1, c.hostIds[src_idx], dst_idx);
    Lemma_GetHostIndexIsUnique(c, src_idx);
    Lemma_GetHostIndexIsUnique(c, dst_idx);

    if AckStateLookup(dst, host.sd.sendState).numPacketsAcked == AckStateLookup(dst, host'.sd.sendState).numPacketsAcked
    {
        return;
    }

    var ap := Lemma_ActionThatChangesHostIsThatHostsAction(b, c, i-1, src_idx);
    assert ap.nextActionIndex == 0;
    assert ap.ios[0].LIoOpReceive?;
    assert IsValidLIoOp(ap.ios[0], src, b[i-1].environment);
    Lemma_AckPacketBeforeSenderSequenceNumber(b, c, i, src_idx, dst_idx, ap.ios[0].r);
}

}
