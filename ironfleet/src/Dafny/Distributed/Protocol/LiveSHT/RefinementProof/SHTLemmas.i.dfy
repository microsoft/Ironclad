include "../../../Common/Collections/Maps2.i.dfy"
include "SHTRefinement.i.dfy"
include "SchedulerRefinement.i.dfy"
include "SchedulerLemmas.i.dfy"
include "EnvironmentLemmas.i.dfy"
include "SHT.i.dfy"

module RefinementProof__DistributedSystemLemmas_i {
import opened Native__Io_s
import opened Collections__Maps2_s
import opened Collections__Maps2_i
import opened Concrete_NodeIdentity_i`Spec
import opened Environment_s
import opened SHT__Host_i
import opened SHT__Network_i
import opened SHT__SHT_i
import opened SHT__Configuration_i
import opened LiveSHT__SHTRefinement_i
import opened LiveSHT__Scheduler_i
import opened LiveSHT__SchedulerRefinement_i
import opened LiveSHT__SchedulerLemmas_i
import opened LiveSHT__EnvironmentLemmas_i
import opened LiveSHT__SHT_i
import opened LiveSHT__EnvironmentRefinement_i
import opened LiveSHT__Environment_i


lemma Lemma_HostNextImpliesHostNextWithBiggerReceiveSet(s:Host, s':Host, recvs1:set<Packet>, recvs2:set<Packet>, out:set<Packet>)
    requires Host_Next(s, s', recvs1, out);
    requires recvs1 <= recvs2;
    ensures  Host_Next(s, s', recvs1, out);
{
}

lemma {:timeLimitMultiplier 2} Lemma_HostRefinementAllowsSHTStateRefinement(
    ps:SHT_State,
    ps':SHT_State,
    actor:NodeIdentity,
    environment:LSHTEnvironment,
    environment':LSHTEnvironment,
    ios:seq<LSHTIo>
    )
    requires environment.nextStep == LEnvStepHostIos(actor, ios);
    requires LEnvironment_Next(environment, environment');
    requires SHT_MapsComplete(ps);
    requires SHT_MapsComplete(ps');
    requires ps'.config == ps.config;
    requires actor in ps.hosts;
    requires actor in ps'.hosts;
    requires forall id :: id in ps.hosts <==> id in ps'.hosts;
    requires forall id :: id in ps.hosts <==> id in ps.config.hostIds;
    requires forall oid :: oid in ps.config.hostIds && oid != actor ==> ps'.hosts[oid] == ps.hosts[oid];
    requires actor in ps.config.hostIds;
    requires ps.network == LSHTEnvironment_Refine(environment);
    requires ps'.network == LSHTEnvironment_Refine(environment');
    requires HostNextOrStutter(ps.hosts[actor], ps'.hosts[actor],
                               PacketsTo(LSHTEnvironment_Refine(environment), actor), LSHTIoSeq_RefineAsSends(ios));
    ensures  SHTNextOrStutter(ps, ps');
{
    var receives := PacketsTo(LSHTEnvironment_Refine(environment), actor);
    var sends := LSHTIoSeq_RefineAsSends(ios);
    var host := ps.hosts[actor];
    var host' := ps'.hosts[actor];

    Lemma_EffectOnLSHTEnvironmentRefinementOfAddingPackets(environment, environment', ios);

    if host' == host && sends == {} {
        assert ps'.network == ps.network;
        assert ps'.hosts == ps.hosts;
        assert ps' == ps;
        return;
    }

    assert receives <= PacketsTo(ps.network, actor);
    assert Host_Next(host, host', receives, sends);
    Lemma_HostNextImpliesHostNextWithBiggerReceiveSet(host, host', receives, PacketsTo(ps.network, actor), sends);
    assert Host_Next(host, host', PacketsTo(ps.network, actor), sends);
    assert SHT_NextPred(ps, ps', actor, PacketsTo(ps.network, actor), sends);
    assert SHT_Next(ps, ps');
    assert SHTNextOrStutter(ps, ps');
}

lemma Lemma_LSHTInitImpliesSHTInit(l_config:SHTConfiguration, l_ps:LSHT_State)
    requires LSHT_Init(l_config, l_ps);
    ensures SHT_Init(LSHTConfiguration_Refine(l_config), LSHTState_Refine(l_ps));
    ensures LSHTState_RefinementInvariant(l_ps);
{
    var h_config := l_config;
    var h_ps := LSHTState_Refine(l_ps);

    forall nodeIndex | 0 <= nodeIndex < |h_config.hostIds|
        ensures Host_Init(h_ps.hosts[h_config.hostIds[nodeIndex]], h_config.hostIds[nodeIndex], h_config.rootIdentity, h_config.hostIds, h_config.params);
        ensures LScheduler_RefinementInvariant(l_ps.hosts[nodeIndex]);
    {
        Lemma_GetHostIndexIsUnique(l_config, nodeIndex);
    }
}

lemma Lemma_LSHTNextPreservesLocalInvariant(ps:LSHT_State, ps':LSHT_State)
    requires LSHTState_RefinementInvariant(ps);
    requires LSHT_Next(ps, ps');
    ensures  |ps.hosts| == |ps'.hosts|;
    ensures  |ps'.hosts| == |ps'.config.hostIds|;
{
}

lemma Lemma_SHTStateRefinementLeavesHostDomainUnchanged(l_ps:LSHT_State, h_ps:SHT_State)
    requires LSHTState_RefinementInvariant(l_ps);
    requires h_ps == LSHTState_Refine(l_ps);
    ensures  forall id :: id in l_ps.config.hostIds <==> id in mapdomain(h_ps.hosts);
{
    forall id | id in l_ps.config.hostIds
        ensures id in mapdomain(h_ps.hosts);
    {
        assert id in h_ps.hosts;
    }
}

lemma Lemma_LSHTNextOneHostMaintainsInvariant(l_s:LSHT_State, l_s':LSHT_State, idx:int, ios:seq<LSHTIo>)
    requires l_s.config == l_s'.config;
    requires LSHT_NextOneHost(l_s, l_s', idx, ios);
    requires LSHTState_RefinementInvariant(l_s);
    ensures  LSHTState_RefinementInvariant(l_s');
{
    Lemma_LSHTNextPreservesLocalInvariant(l_s, l_s');
    Lemma_LSchedulerNextImpliesHostNextOrStutter(l_s.hosts[idx], l_s'.hosts[idx], l_s.environment, l_s'.environment, ios);
}

lemma Lemma_LSHTNextOneHostImpliesSHTNext(l_ps:LSHT_State, l_ps':LSHT_State, idx:int, ios:seq<LSHTIo>)
    requires LSHT_NextOneHost(l_ps, l_ps', idx, ios);
    requires LSHTState_RefinementInvariant(l_ps);
    ensures  LSHTState_RefinementInvariant(l_ps');
    ensures  SHTNextOrStutter(LSHTState_Refine(l_ps), LSHTState_Refine(l_ps'));
{
    var h_ps := LSHTState_Refine(l_ps);

    Lemma_LSHTNextOneHostMaintainsInvariant(l_ps, l_ps', idx, ios);

    var h_ps' := LSHTState_Refine(l_ps');

    var id := l_ps.config.hostIds[idx];

    Lemma_SHTStateRefinementLeavesHostDomainUnchanged(l_ps, h_ps);
    Lemma_SHTStateRefinementLeavesHostDomainUnchanged(l_ps', h_ps');
    assert mapdomain(h_ps'.hosts) == mapdomain(h_ps.hosts);

    forall oid | oid != id && oid in h_ps.hosts
        ensures oid in h_ps'.hosts && h_ps'.hosts[oid] == h_ps.hosts[oid];
    {
        assert oid in mapdomain(h_ps.hosts);
        assert oid in mapdomain(h_ps'.hosts);
        var idx' := GetHostIndex(oid, l_ps.config);
        calc {
            h_ps.hosts[oid];
            (l_ps.hosts[idx'].host);
            (l_ps'.hosts[idx'].host);
            h_ps'.hosts[oid];
        }
    }
    
    Lemma_LSchedulerNextImpliesHostNextOrStutter(l_ps.hosts[idx], l_ps'.hosts[idx], l_ps.environment, l_ps'.environment, ios);

    Lemma_GetHostIndexIsUnique(l_ps.config, idx);
    Lemma_HostRefinementAllowsSHTStateRefinement(h_ps, h_ps', id, l_ps.environment, l_ps'.environment, ios);
}

lemma Lemma_LSHTNextExternalImpliesSHTNext(l_ps:LSHT_State, l_ps':LSHT_State, idx:EndPoint, ios:seq<LSHTIo>)
    requires LSHT_NextExternal(l_ps, l_ps', idx, ios);
    requires LSHTState_RefinementInvariant(l_ps);
    ensures  LSHTState_RefinementInvariant(l_ps');
    ensures  SHTNextOrStutter(LSHTState_Refine(l_ps), LSHTState_Refine(l_ps'));
{
    var h_ps := LSHTState_Refine(l_ps);
    //Lemma_LSHTNextOneHostMaintainsInvariant(l_ps, l_ps', idx, ios);
    var h_ps' := LSHTState_Refine(l_ps');

    Lemma_SHTStateRefinementLeavesHostDomainUnchanged(l_ps, h_ps);
    Lemma_SHTStateRefinementLeavesHostDomainUnchanged(l_ps', h_ps');
    assert mapdomain(h_ps'.hosts) == mapdomain(h_ps.hosts);
    
    var s := [h_ps, h_ps'];
    assert SHT_NextExternal(h_ps, h_ps', idx, LSHTIoSeq_RefineAsSends(ios), LSHTIoSeq_RefineAsSends(ios));  // OBSERVE: exists
    assert SHTNextOrStutter(h_ps, h_ps');
}

lemma Lemma_LSHTNextEnvironmentImpliesSHTNext(l_s:LSHT_State, l_s':LSHT_State)
    requires LSHT_NextEnvironment(l_s, l_s');
    requires LSHTState_RefinementInvariant(l_s);
    requires LSHTState_RefinementInvariant(l_s');
    ensures  SHTNextOrStutter(LSHTState_Refine(l_s), LSHTState_Refine(l_s'));
{
    var h_s := LSHTState_Refine(l_s);
    var h_s' := LSHTState_Refine(l_s');

    assert h_s'.hosts == h_s.hosts;

    var s := [h_s];
    assert s[0] == LSHTState_Refine(l_s);

    assert h_s'.network == h_s.network;
    
    assert SHTNextOrStutter(LSHTState_Refine(l_s), LSHTState_Refine(l_s'));
}

lemma Lemma_LSHTNextImpliesSHTNext(l_s:LSHT_State, l_s':LSHT_State)
    requires LSHT_Next(l_s, l_s');
    requires LSHTState_RefinementInvariant(l_s);
    ensures  LSHTState_RefinementInvariant(l_s');
    ensures  SHTNextOrStutter(LSHTState_Refine(l_s), LSHTState_Refine(l_s'));
{
    if (exists idx, ios :: LSHT_NextOneHost(l_s, l_s', idx, ios)) {
        var idx, ios :| LSHT_NextOneHost(l_s, l_s', idx, ios);
        Lemma_LSHTNextOneHostImpliesSHTNext(l_s, l_s', idx, ios);
    } else if (exists idx, ios :: LSHT_NextExternal(l_s, l_s', idx, ios)) {
        var idx, ios :| LSHT_NextExternal(l_s, l_s', idx, ios);
        Lemma_LSHTNextExternalImpliesSHTNext(l_s, l_s', idx, ios);
    } else if LSHT_NextEnvironment(l_s, l_s') {
        Lemma_LSHTNextEnvironmentImpliesSHTNext(l_s, l_s');
    }
}

} 
