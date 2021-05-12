include "../../../Common/Framework/Environment.s.dfy"
include "EnvironmentRefinement.i.dfy"

module LiveSHT__EnvironmentLemmas_i {
import opened Environment_s
import opened LiveSHT__Environment_i
import opened LiveSHT__EnvironmentRefinement_i

lemma Lemma_EffectOnLSHTEnvironmentRefinementOfAddingPackets(e:LSHTEnvironment, e':LSHTEnvironment, ios:seq<LSHTIo>)
    requires e'.sentPackets == e.sentPackets + (set io | io in ios && io.LIoOpSend? :: io.s);
    ensures  LSHTEnvironment_Refine(e') == LSHTEnvironment_Refine(e) + LSHTIoSeq_RefineAsSends(ios);
{
}

lemma Lemma_LSHTIoSeq_RefineAsSendsEmptyHelper<T>(x: T, s1: set<T>, s2: set<T>)
  requires x in s1
  requires x !in s2
  ensures  s1 != s2
{
}

lemma Lemma_LSHTIoSeq_RefineAsSendsEmpty(ios:seq<LSHTIo>)
    requires (set io | io in ios && io.LIoOpSend? :: io.s) == {};
    ensures LSHTIoSeq_RefineAsSends(ios) == {};
{
    var sends := LSHTIoSeq_RefineAsSends(ios);
    if (|sends| > 0)
    {
        var io' :| io' in ios && io'.LIoOpSend?;
        assert io'.s in (set io | io in ios && io.LIoOpSend? :: io.s);
        Lemma_LSHTIoSeq_RefineAsSendsEmptyHelper(io'.s, set io | io in ios && io.LIoOpSend? :: io.s, {});
        assert false;
    }
}

lemma Lemma_LSHTPacketSetRefineIsCommutative(l_ps1:set<LSHTPacket>, l_ps2:set<LSHTPacket>)
    ensures LSHTPacketSet_Refine(l_ps1 + l_ps2) == LSHTPacketSet_Refine(l_ps1) + LSHTPacketSet_Refine(l_ps2);
{
    var h_ps1 := LSHTPacketSet_Refine(l_ps1);
    var h_ps2 := LSHTPacketSet_Refine(l_ps2);
    var l_ps := l_ps1 + l_ps2;
    var h_ps := LSHTPacketSet_Refine(l_ps);

    forall h_p | h_p in h_ps1
        ensures h_p in h_ps;
    {
    }

    forall h_p | h_p in h_ps2
        ensures h_p in h_ps;
    {
    }

    forall h_p | h_p in h_ps
        ensures (h_p in h_ps1) || (h_p in h_ps2);
    {
    }
}

lemma Lemma_LSHTPacketSetRefineOfOnePacket(l_ps:LSHTPacket)
    ensures  LSHTPacketSet_Refine({l_ps}) == { LSHTPacket_Refine(l_ps) };
{
}

lemma Lemma_LSHTPacketSeqRefineIsCommutative(l_ps1:seq<LSHTPacket>, l_ps2:seq<LSHTPacket>)
    ensures LSHTPacketSeq_Refine(l_ps1 + l_ps2) == LSHTPacketSeq_Refine(l_ps1) + LSHTPacketSeq_Refine(l_ps2);
{
    var h_ps1 := LSHTPacketSeq_Refine(l_ps1);
    var h_ps2 := LSHTPacketSeq_Refine(l_ps2);
    var l_ps := l_ps1 + l_ps2;
    var h_ps := LSHTPacketSeq_Refine(l_ps);

    forall h_p | h_p in h_ps1
        ensures h_p in h_ps;
    {
    }

    forall h_p | h_p in h_ps2
        ensures h_p in h_ps;
    {
    }

    forall h_p | h_p in h_ps
        ensures (h_p in h_ps1) || (h_p in h_ps2);
    {
    }
}

lemma Lemma_LSHTPacketSeqRefineOfOnePacket(l_ps:LSHTPacket)
    ensures  LSHTPacketSeq_Refine([l_ps]) == { LSHTPacket_Refine(l_ps) };
{
}

} 
