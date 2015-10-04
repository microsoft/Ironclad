include "Constants.i.dfy"
include "../RefinementProof/SHTRefinement.i.dfy"

module LivenessProof__Actions_i {
import opened LivenessProof__Constants_i
import opened LiveSHT__SHTRefinement_i

predicate PacketProcessedViaIos(
    ps:LSHT_State,
    ps':LSHT_State,
    p:LSHTPacket,
    idx:int,
    ios:seq<LSHTIo>
    )
{
       |ios| > 0
    && LIoOpReceive(p) == ios[0]
    && 0 <= idx < |ps.config.hostIds|
    && p.dst == ps.config.hostIds[idx]
    && ps.environment.nextStep == LEnvStepHostIos(p.dst, ios)
    && LSHT_NextOneHost(ps, ps', idx, ios)
    && LHost_ReceivePacket_Next(ps.hosts[idx].host, ps'.hosts[idx].host, ios)
}

predicate PacketProcessedDuringAction(
    ps:LSHT_State,
    p:LSHTPacket
    )
{
    ps.environment.nextStep.LEnvStepHostIos? && LIoOpReceive(p) in ps.environment.nextStep.ios
}

function{:opaque} PacketProcessedTemporal(
    b:Behavior<LSHT_State>,
    p:LSHTPacket
    ):temporal
    requires imaptotal(b);
    ensures  forall i {:trigger sat(i, PacketProcessedTemporal(b, p))} ::
                 sat(i, PacketProcessedTemporal(b, p)) <==> PacketProcessedDuringAction(b[i], p);
{
    stepmap(imap i :: PacketProcessedDuringAction(b[i], p))
}

predicate PacketSentDuringAction(
    ps:LSHT_State,
    p:LSHTPacket
    )
{
    ps.environment.nextStep.LEnvStepHostIos? && LIoOpSend(p) in ps.environment.nextStep.ios
}

function{:opaque} PacketSentTemporal(
    b:Behavior<LSHT_State>,
    p:LSHTPacket
    ):temporal
    requires imaptotal(b);
    ensures  forall i {:trigger sat(i, PacketSentTemporal(b, p))} ::
             sat(i, PacketSentTemporal(b, p)) <==> PacketSentDuringAction(b[i], p);
{
    stepmap(imap i :: PacketSentDuringAction(b[i], p))
}

datatype SHTActionParams = SHTActionParams(idx:int, ios:seq<LSHTIo>, host:Host, host':Host, recv:set<Packet>, out:set<Packet>,
                                           nextActionIndex:int, resendCount:int, pkt:Packet, ack:Packet)

predicate SHTActionOccurred(ss:LSHT_State, ss':LSHT_State, ap:SHTActionParams)
{
       0 <= ap.idx < |ss.hosts|
    && 0 <= ap.idx < |ss.config.hostIds|
    && 0 <= ap.idx < |ss'.hosts|
    && ss.environment.nextStep.LEnvStepHostIos?
    && ss.environment.nextStep.actor == ss.config.hostIds[ap.idx]
    && ss.environment.nextStep.ios == ap.ios
    && ap.host == ss.hosts[ap.idx].host
    && ap.host' == ss'.hosts[ap.idx].host
    && ap.recv == PacketsTo(LSHTEnvironment_Refine(ss.environment), ap.host.me)
    && ap.out == ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ap.ios))
    && ap.nextActionIndex == ss.hosts[ap.idx].nextActionIndex
    && ap.resendCount == ss'.hosts[ap.idx].resendCount
    && LScheduler_Next(ss.hosts[ap.idx], ss'.hosts[ap.idx], ap.ios)
    && GetHostIndex(ss.config.hostIds[ap.idx], ss.config) == ap.idx
    && (   (   ap.nextActionIndex == 0
            && |ap.ios| == 1
            && ap.ios[0].LIoOpTimeoutReceive?
            && ap.host == ap.host')
        || (   ap.nextActionIndex == 0
            && |ap.ios| > 0
            &&  ap.ios[0].LIoOpReceive?
            && (forall i{:trigger ap.ios[i].LIoOpSend?} :: 1 <= i < |ap.ios| ==> ap.ios[i].LIoOpSend?)
            && ap.pkt == LSHTPacketToPacket(ap.ios[0].r)
            && LSHT_NextOneHost(ss, ss', ap.idx, ap.ios)
            && Host_Next(ap.host, ap.host', ap.recv, ap.out)
            && ReceivePacket(ap.host, ap.host', ap.pkt, ap.out, ap.ack))
       || (   ap.nextActionIndex == 1
           && (forall io{:trigger io in ap.ios} :: io in ap.ios ==> io.LIoOpSend?)
           && LSHT_NextOneHost(ss, ss', ap.idx, ap.ios)
           && Host_Next(ap.host, ap.host', ap.recv, ap.out)
           && ProcessReceivedPacket(ap.host, ap.host', ap.out))
       || (   ap.nextActionIndex == 2
           && (forall io{:trigger io in ap.ios} :: io in ap.ios ==> io.LIoOpSend?)
           && LSHT_NextOneHost(ss, ss', ap.idx, ap.ios)
           && (if ap.resendCount != 0 then
                   ap.host == ap.host'
               else
                      Host_Next(ap.host, ap.host', ap.recv, ap.out)
                   && SpontaneouslyRetransmit(ap.host, ap.host', ap.out))))
}

lemma Lemma_NextActionIndexAlwaysWithinRange(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    idx:int
    )
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= idx < |b[i].hosts|;
    ensures  0 <= b[i].hosts[idx].nextActionIndex < 3;
{
    if i == 0
    {
        return;
    }

    Lemma_AssumptionsMakeValidTransition(b, c, i-1);
    Lemma_ConstantsAllConsistent(b, c, i-1);
    Lemma_ConstantsAllConsistent(b, c, i);
    Lemma_NextActionIndexAlwaysWithinRange(b, c, i-1, idx);
}

///////////////////////////////
// ACTION REFINEMENT
///////////////////////////////

lemma Lemma_GetParametersOfAction0(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    idx:int
    ) returns
    (ap:SHTActionParams)
    requires IsValidBehaviorPrefix(b, c, i+1);
    requires 0 <= i;
    requires 0 <= idx < |b[i].hosts|;
    requires 0 <= idx < |c.hostIds|;
    requires b[i].environment.nextStep.LEnvStepHostIos?;
    requires b[i].environment.nextStep.actor == c.hostIds[idx];
    requires b[i].hosts[idx].nextActionIndex == 0;
    ensures  SHTActionOccurred(b[i], b[i+1], ap);
    ensures  ap.idx == idx;
    ensures  ap.nextActionIndex == 0;
{
    Lemma_AssumptionsMakeValidTransition(b, c, i);
    Lemma_ConstantsAllConsistent(b, c, i);
    Lemma_ConstantsAllConsistent(b, c, i+1);

    var scheduler := b[i].hosts[idx];
    var scheduler' := b[i+1].hosts[idx];

    var host := scheduler.host;
    var host' := scheduler'.host;
    var recv := PacketsTo(LSHTEnvironment_Refine(b[i].environment), host.me);
    var resendCount := scheduler'.resendCount;

    Lemma_GetHostIndexIsUnique(b[i].config, idx);

    assert LSHT_Next(b[i], b[i+1]);
    //assert !LSHT_NextEnvironment(b[i], b[i+1]);
    assert !(exists idx, ios :: LSHT_NextExternal(b[i], b[i+1], idx, ios));
    assert exists idx, ios :: LSHT_NextOneHost(b[i], b[i+1], idx, ios);

    var other_idx, ios :| LSHT_NextOneHost(b[i], b[i+1], other_idx, ios);
    assert HostsDistinct(c.hostIds, idx, other_idx);

    var out := ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ios));
    assert out == ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ios));

    var pkt:Packet, ack:Packet;
    if ios[0].LIoOpTimeoutReceive?
    {
    }
    else
    {
        assert IsValidLIoOp(ios[0], host.me, b[i].environment);
        assert LHost_ReceivePacketWithoutReadingClock(host, host', ios);
        pkt := LSHTPacketToPacket(ios[0].r);
        ack :| ReceivePacket(host, host', pkt, out, ack);
    }

    ap := SHTActionParams(idx, ios, host, host', recv, out, 0, resendCount, pkt, ack);
}

lemma Lemma_GetParametersOfAction1(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    idx:int
    ) returns
    (ap:SHTActionParams)
    requires IsValidBehaviorPrefix(b, c, i+1);
    requires 0 <= i;
    requires 0 <= idx < |b[i].hosts|;
    requires 0 <= idx < |c.hostIds|;
    requires b[i].environment.nextStep.LEnvStepHostIos?;
    requires b[i].environment.nextStep.actor == c.hostIds[idx];
    requires b[i].hosts[idx].nextActionIndex == 1;
    ensures  SHTActionOccurred(b[i], b[i+1], ap);
    ensures  ap.idx == idx;
    ensures  ap.nextActionIndex == 1;
{
    Lemma_AssumptionsMakeValidTransition(b, c, i);
    Lemma_ConstantsAllConsistent(b, c, i);
    Lemma_ConstantsAllConsistent(b, c, i+1);

    var scheduler := b[i].hosts[idx];
    var scheduler' := b[i+1].hosts[idx];
    var host := scheduler.host;
    var host' := scheduler'.host;
    var recv := PacketsTo(LSHTEnvironment_Refine(b[i].environment), host.me);
    var resendCount := scheduler'.resendCount;
    var pkt:Packet, ack:Packet;

    Lemma_GetHostIndexIsUnique(b[i].config, idx);

    var other_idx, ios :| LSHT_NextOneHost(b[i], b[i+1], other_idx, ios);
    assert HostsDistinct(c.hostIds, idx, other_idx);
    var out := LSHTIoSeq_RefineAsSends(ios);
    assert out == ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ios));

    ap := SHTActionParams(idx, ios, host, host', recv, out, 1, resendCount, pkt, ack);
}

lemma Lemma_GetParametersOfAction2(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    idx:int
    ) returns
    (ap:SHTActionParams)
    requires IsValidBehaviorPrefix(b, c, i+1);
    requires 0 <= i;
    requires 0 <= idx < |b[i].hosts|;
    requires 0 <= idx < |c.hostIds|;
    requires b[i].environment.nextStep.LEnvStepHostIos?;
    requires b[i].environment.nextStep.actor == c.hostIds[idx];
    requires b[i].hosts[idx].nextActionIndex == 2;
    ensures  SHTActionOccurred(b[i], b[i+1], ap);
    ensures  ap.idx == idx;
    ensures  ap.nextActionIndex == 2;
{
    Lemma_AssumptionsMakeValidTransition(b, c, i);
    Lemma_ConstantsAllConsistent(b, c, i);
    Lemma_ConstantsAllConsistent(b, c, i+1);

    var scheduler := b[i].hosts[idx];
    var scheduler' := b[i+1].hosts[idx];
    var host := scheduler.host;
    var host' := scheduler'.host;
    var recv := PacketsTo(LSHTEnvironment_Refine(b[i].environment), host.me);
    var resendCount := scheduler'.resendCount;
    var pkt:Packet, ack:Packet;

    Lemma_GetHostIndexIsUnique(b[i].config, idx);

    var other_idx, ios :| LSHT_NextOneHost(b[i], b[i+1], other_idx, ios);
    assert HostsDistinct(c.hostIds, idx, other_idx);
    var out := LSHTIoSeq_RefineAsSends(ios);
    assert out == ExtractPacketsFromLSHTPackets(ExtractSentPacketsFromIos(ios));

    ap := SHTActionParams(idx, ios, host, host', recv, out, 2, resendCount, pkt, ack);
    assert ap.nextActionIndex == 2;
    if ap.resendCount != 0
    {
        assert ap.host == ap.host';
    }
    else
    {
        assert SpontaneouslyRetransmit(ap.host, ap.host', ap.out);
    }
}

lemma Lemma_GetParametersOfAction(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int
    ) returns
    (ap:SHTActionParams)
    requires IsValidBehaviorPrefix(b, c, i+1);
    requires 0 <= i;
    requires b[i].environment.nextStep.LEnvStepHostIos?;
    requires b[i].environment.nextStep.actor in b[i].config.hostIds;
    ensures  SHTActionOccurred(b[i], b[i+1], ap);
{
    Lemma_AssumptionsMakeValidTransition(b, c, i);
    Lemma_ConstantsAllConsistent(b, c, i);
    Lemma_ConstantsAllConsistent(b, c, i+1);

    var idx, ios :| LSHT_NextOneHost(b[i], b[i+1], idx, ios);
    Lemma_GetHostIndexIsUnique(b[i].config, idx);
    var scheduler := b[i].hosts[idx];
    var nextActionIndex := scheduler.nextActionIndex;

    Lemma_NextActionIndexAlwaysWithinRange(b, c, i, idx);
    if nextActionIndex == 0
    {
        ap := Lemma_GetParametersOfAction0(b, c, i, idx);
    }
    else if nextActionIndex == 1
    {
        ap := Lemma_GetParametersOfAction1(b, c, i, idx);
    }
    else if nextActionIndex == 2
    {
        ap := Lemma_GetParametersOfAction2(b, c, i, idx);
    }
    else
    {
        assert false;
    }
}

lemma Lemma_ActionThatChangesHostIsThatHostsAction(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    host_index:int
    )
    returns (ap:SHTActionParams)
    requires IsValidBehaviorPrefix(b, c, i+1);
    requires 0 <= i;
    requires 0 <= host_index < |b[i].hosts|;
    requires 0 <= host_index < |b[i+1].hosts|;
    requires b[i+1].hosts[host_index] != b[i].hosts[host_index];
    ensures  SHTActionOccurred(b[i], b[i+1], ap);
    ensures  ap.idx == host_index;
    ensures  LSHT_Next(b[i], b[i+1]);
    ensures  LSHT_NextOneHost(b[i], b[i+1], host_index, ap.ios);
{
    Lemma_AssumptionsMakeValidTransition(b, c, i);
    Lemma_ConstantsAllConsistent(b, c, i);
    ap := Lemma_GetParametersOfAction(b, c, i);
    Lemma_GetHostIndexIsUnique(c, host_index);
}

lemma Lemma_PacketProcessedImpliesPacketSent(
    ps:LSHT_State,
    ps':LSHT_State,
    idx:int,
    ios:seq<LSHTIo>,
    inp:LSHTPacket
    )
    requires LSHT_NextOneHost(ps, ps', idx, ios);
    requires LIoOpReceive(inp) in ios;
    ensures  inp in ps.environment.sentPackets;
{
    var id := ps.config.hostIds[idx];
    var e := ps.environment;
    var e' := ps'.environment;

    assert IsValidLIoOp(LIoOpReceive(inp), id, ps.environment);
    assert inp in e.sentPackets;
}

lemma Lemma_PacketProcessedImpliesPacketSentAlt(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    idx:int,
    inp:LSHTPacket
    )
    requires IsValidBehaviorPrefix(b, c, i+1);
    requires 0 <= i;
    requires 0 <= idx < |c.hostIds|;
    requires b[i].environment.nextStep.LEnvStepHostIos?;
    requires b[i].environment.nextStep.actor == c.hostIds[idx];
    requires LIoOpReceive(inp) in b[i].environment.nextStep.ios;
    ensures  inp in b[i].environment.sentPackets;
{
    var ps := b[i];
    var ps' := b[i+1];

    Lemma_AssumptionsMakeValidTransition(b, c, i);
    Lemma_ConstantsAllConsistent(b, c, i);

    var id := ps.config.hostIds[idx];
    var e := ps.environment;
    var e' := ps'.environment;

    assert IsValidLIoOp(LIoOpReceive(inp), id, ps.environment);
    assert inp in e.sentPackets;
}

}
