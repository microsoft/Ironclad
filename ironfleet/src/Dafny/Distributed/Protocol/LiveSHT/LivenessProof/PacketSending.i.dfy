include "../RefinementProof/SHT.i.dfy"
include "RefinementInvariants.i.dfy"

module LivenessProof__PacketSending_i {

import opened LiveSHT__SHT_i
import opened LivenessProof__RefinementInvariants_i

lemma Lemma_ActionThatSendsPacketIsActionOfSource(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    p:LSHTPacket
    )
    returns
    (ap:SHTActionParams)
    requires IsValidBehaviorPrefix(b, c, i+1);
    requires 0 <= i;
    requires p.src in c.hostIds;
    requires p in b[i+1].environment.sentPackets;
    requires p !in b[i].environment.sentPackets;
    ensures  SHTActionOccurred(b[i], b[i+1], ap);
    ensures  0 <= ap.idx < |c.hostIds|;
    ensures  p.src == c.hostIds[ap.idx];
    ensures  LSHT_Next(b[i], b[i+1]);
    ensures  LIoOpSend(p) in ap.ios;
{
    Lemma_AssumptionsMakeValidTransition(b, c, i);
    Lemma_ConstantsAllConsistent(b, c, i);
    assert b[i].environment.nextStep.LEnvStepHostIos?;
    assert LIoOpSend(p) in b[i].environment.nextStep.ios;
    ap := Lemma_GetParametersOfAction(b, c, i);
}

lemma Lemma_ActionThatSendsFreshPacketIsNotResend(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    ap:SHTActionParams,
    p:LSHTPacket
    )
    requires IsValidBehaviorPrefix(b, c, i+1);
    requires 0 < i;
    requires p in b[i+1].environment.sentPackets;
    requires p !in b[i].environment.sentPackets;
    requires SHTActionOccurred(b[i], b[i+1], ap);
    ensures  ap.nextActionIndex != 2;
{
    Lemma_AssumptionsMakeValidTransition(b, c, i);
    Lemma_ConstantsAllConsistent(b, c, i);

    assert LIoOpSend(p) in ap.ios;
    assert LSHTPacketToPacket(p) in ap.out;
    if ap.nextActionIndex == 2
    {
        Lemma_HostConstantsMeHasAppropriateValue(b, c, i, ap.idx);
        assert SpontaneouslyRetransmit(ap.host, ap.host', ap.out);
        assert ap.out == UnAckedMessages(ap.host.sd, ap.host.me);
        var s := ap.host.sd;
        var dst, j :|    dst in s.sendState
                      && 0 <= j < |s.sendState[dst].unAcked|
                      && s.sendState[dst].unAcked[j].SingleMessage?
                      && LSHTPacketToPacket(p) == Packet(s.sendState[dst].unAcked[j].dst, ap.host.me, s.sendState[dst].unAcked[j]);
        assert LSHTPacketToPacket(p).msg == s.sendState[dst].unAcked[j];
        assert p.msg == s.sendState[dst].unAcked[j];
        Lemma_MessageInUnackedListHasParticularDestination(b, c, i, ap.idx, dst, p.msg);
        Lemma_UnAckedPacketInNetwork(b, c, i, ap.idx, p);
    }
}
    
}
