include "../../../Common/Collections/Maps2.i.dfy"
include "SHTRefinement.i.dfy"
include "SchedulerRefinement.i.dfy"
include "SchedulerLemmas.i.dfy"
include "EnvironmentLemmas.i.dfy"
include "SHT.i.dfy"

module RefinementProof__DistributedSystemLemmas_i {
import opened Collections__Maps2_i
import opened LiveSHT__SHTRefinement_i
import opened LiveSHT__Scheduler_i
import opened LiveSHT__SchedulerRefinement_i
import opened LiveSHT__SchedulerLemmas_i
import opened LiveSHT__EnvironmentLemmas_i
import opened LiveSHT__SHT_i

function CreateSHTStateRefinementSequenceFrom(
    ps:SHT_State,
    actor:NodeIdentity,
    hosts:seq<Host>,
    sends_by_step:seq<set<Packet>>
    ):seq<SHT_State>
    requires |sends_by_step| == |hosts| - 1;
    ensures  var s := CreateSHTStateRefinementSequenceFrom(ps, actor, hosts, sends_by_step);
                |s| == |hosts|
             && (forall i :: 0 <= i < |s| ==> s[i].config == ps.config)
             && (forall i :: 0 <= i < |s| ==> s[i].hosts == ps.hosts[actor := hosts[i]])
             && (forall i :: 0 <= i < |sends_by_step| ==> s[i+1].network == s[i].network + sends_by_step[i])
             && (forall i :: 0 <= i < |sends_by_step| ==> ps.network <= s[i].network)
             && s[0].network == ps.network
             && s[|s|-1].network == s[0].network + AddPacketSets(sends_by_step);
    decreases |hosts|;
{
    if |hosts| == 0 then
        []
    else if |hosts| == 1 then
        assert |sends_by_step| == 0;
        [ps[hosts := ps.hosts[actor := hosts[0]]]]
    else
        [ps[hosts := ps.hosts[actor := hosts[0]]]] + CreateSHTStateRefinementSequenceFrom(ps[network := ps.network + sends_by_step[0]], actor, hosts[1..], sends_by_step[1..])
}

lemma Lemma_HostNextImpliesHostNextWithBiggerReceiveSet(s:Host, s':Host, recvs1:set<Packet>, recvs2:set<Packet>, out:set<Packet>)
    requires Host_Next(s, s', recvs1, out);
    requires recvs1 <= recvs2;
    ensures  Host_Next(s, s', recvs1, out);
{
}

lemma {:timeLimitMultiplier 4} Lemma_CreatingSHTStateRefinementSequenceWorks(
    ps:SHT_State,
    ps':SHT_State,
    actor:NodeIdentity,
    hosts:seq<Host>,
    sends_by_step:seq<set<Packet>>,
    s:seq<SHT_State>,
    receives:set<Packet>,
    sends:set<Packet>
    )
    requires |sends_by_step| == |hosts| - 1;
    requires s == CreateSHTStateRefinementSequenceFrom(ps, actor, hosts, sends_by_step);
    requires actor in ps.hosts;
    requires actor in ps'.hosts;
    requires forall id :: id in ps.hosts <==> id in ps'.hosts;
    requires forall id :: id in ps.hosts <==> id in ps.config.hostIds;
    requires forall oid :: oid in ps.config.hostIds && oid != actor ==> ps'.hosts[oid] == ps.hosts[oid];
    requires ps'.hosts == ps.hosts[actor := ps'.hosts[actor]];
    requires ps'.network == ps.network + sends;
    requires actor in ps.config.hostIds;
    requires SHT_MapsComplete(ps);
    requires SHT_MapsComplete(ps');
    requires ps.config == ps'.config;
    requires forall p :: p in sends ==> p.src == actor;
    requires receives <= PacketsTo(ps.network, actor);
    requires IsHostRefinementSequenceOf(hosts, sends_by_step, ps.hosts[actor], ps'.hosts[actor], receives, sends);
    requires sends == AddPacketSets(sends_by_step);
    ensures  IsSHTStateRefinementSequenceOf(s, ps, ps');
{
    assert s[0].hosts == ps.hosts;
    assert s[0] == ps;
    assert s[|s|-1].hosts == ps'.hosts;
    assert s[|s|-1] == ps';
    
    forall i | 0 <= i < |hosts|-1
         ensures SHT_MapsComplete(s[i+1]);
         ensures SHT_MapsComplete(s[i]);
         ensures SHT_Next(s[i], s[i+1]);
    {
         assert receives <= PacketsTo(ps.network, actor) <= PacketsTo(s[i].network, actor);
         assert Host_Next(hosts[i], hosts[i+1], receives, sends_by_step[i]);
         Lemma_HostNextImpliesHostNextWithBiggerReceiveSet(hosts[i], hosts[i+1], receives, PacketsTo(s[i].network, actor), sends_by_step[i]);
         assert Host_Next(hosts[i], hosts[i+1], PacketsTo(s[i].network, actor), sends_by_step[i]);
         assert SHT_NextPred(s[i], s[i+1], actor, PacketsTo(s[i].network, actor), sends_by_step[i]);
         assert SHT_Next(s[i], s[i+1]);
    }
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
    requires exists hosts, sends_by_step ::
                 IsHostRefinementSequenceOf(hosts, sends_by_step, ps.hosts[actor], ps'.hosts[actor],
                                               PacketsTo(LSHTEnvironment_Refine(environment), actor), LSHTIoSeq_RefineAsSends(ios));
    ensures  exists s:seq<SHT_State> :: IsSHTStateRefinementSequenceOf(s, ps, ps');
{
    var receives := PacketsTo(LSHTEnvironment_Refine(environment), actor);
    var sends := LSHTIoSeq_RefineAsSends(ios);
    var host := ps.hosts[actor];
    var host' := ps'.hosts[actor];
    var hosts, sends_by_step :| IsHostRefinementSequenceOf(hosts, sends_by_step, host, host', receives, sends);
    var s := CreateSHTStateRefinementSequenceFrom(ps, actor, hosts, sends_by_step);
    Lemma_EffectOnLSHTEnvironmentRefinementOfAddingPackets(environment, environment', ios);
    Lemma_CreatingSHTStateRefinementSequenceWorks(ps, ps', actor, hosts, sends_by_step, s, receives, sends);
    assert IsSHTStateRefinementSequenceOf(s, ps, ps');
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

function CombineIntoSHTState(baseline:SHT_State, host:NodeIdentity, hosts:seq<Host>, networks:seq<Network>) : seq<SHT_State>
    requires |hosts| == |networks|;
    ensures  var states := CombineIntoSHTState(baseline, host, hosts, networks);
                |states| == |hosts|
             && forall i :: 0 <= i < |hosts| ==> states[i] == SHT_State(baseline.config, networks[i], baseline.hosts[host := hosts[i]]);
{
    if |hosts| == 0 then
        []
    else
        [baseline[hosts := baseline.hosts[host := hosts[0]]][network := networks[0]]] + CombineIntoSHTState(baseline, host, hosts[1..], networks[1..])
}

lemma Lemma_ChangingOneHostToItselfIsNoChange(hosts:map<NodeIdentity, Host>, hosts':map<NodeIdentity, Host>, id:NodeIdentity)
    requires id in hosts;
    requires hosts' == hosts[id := hosts[id]];
    ensures  hosts' == hosts;
{
}

lemma Lemma_LeavingMostHostsUnchangedEquivalentToUpdate(hosts:map<NodeIdentity, Host>, hosts':map<NodeIdentity, Host>, id:NodeIdentity)
    requires id in hosts && id in hosts';
    requires forall id :: id in hosts <==> id in hosts';
    requires forall oid :: oid in hosts && oid != id ==> oid in hosts' && hosts'[oid]==hosts[oid];
    ensures  hosts' == hosts[id := hosts'[id]];
{
    var r := hosts[id := hosts'[id]];
    forall host
        ensures host in hosts' <==> host in r;
        ensures host in hosts' || host in r ==> r[host] == hosts'[host];
    {
        if host in hosts'
        {
            assert host in mapdomain(hosts');
            assert host in mapdomain(hosts);
            assert host in r;
        }
        if host in r
        {
            assert host in hosts';
        }
    }
    assert r == hosts';
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
    Lemma_LSchedulerNextImpliesExistsHostRefinementSequence(l_s.hosts[idx], l_s'.hosts[idx], l_s.environment, l_s'.environment, ios);
}

lemma Lemma_LSHTNextOneHostImpliesSHTNext(l_ps:LSHT_State, l_ps':LSHT_State, idx:int, ios:seq<LSHTIo>)
    requires LSHT_NextOneHost(l_ps, l_ps', idx, ios);
    requires LSHTState_RefinementInvariant(l_ps);
    ensures  LSHTState_RefinementInvariant(l_ps');
    ensures  exists s:seq<SHT_State> :: IsSHTStateRefinementSequenceOf(s, LSHTState_Refine(l_ps), LSHTState_Refine(l_ps'));
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
        var idx := GetHostIndex(oid, l_ps.config);
        calc {
            h_ps.hosts[oid];
            (l_ps.hosts[idx].host);
            (l_ps'.hosts[idx].host);
            h_ps'.hosts[oid];
        }
    }
    
    Lemma_LSchedulerNextImpliesExistsHostRefinementSequence(l_ps.hosts[idx], l_ps'.hosts[idx], l_ps.environment, l_ps'.environment, ios);


    Lemma_GetHostIndexIsUnique(l_ps.config, idx);
    assert exists hosts, sends_by_step :: IsHostRefinementSequenceOf(hosts, sends_by_step,
                                                                           h_ps.hosts[id], h_ps'.hosts[id],
                                                                           PacketsTo(LSHTEnvironment_Refine(l_ps.environment), id), LSHTIoSeq_RefineAsSends(ios));
    var hosts, sends_by_step :| IsHostRefinementSequenceOf(hosts, sends_by_step,
                                                                 h_ps.hosts[id], h_ps'.hosts[id],
                                                                 PacketsTo(LSHTEnvironment_Refine(l_ps.environment), id), LSHTIoSeq_RefineAsSends(ios));
    Lemma_HostRefinementAllowsSHTStateRefinement(h_ps, h_ps', id, l_ps.environment, l_ps'.environment, ios);
}


lemma Lemma_LSHTNextExternalImpliesSHTNext(l_ps:LSHT_State, l_ps':LSHT_State, idx:EndPoint, ios:seq<LSHTIo>)
    requires LSHT_NextExternal(l_ps, l_ps', idx, ios);
    requires LSHTState_RefinementInvariant(l_ps);
    ensures  LSHTState_RefinementInvariant(l_ps');
    ensures  exists s:seq<SHT_State> :: IsSHTStateRefinementSequenceOf(s, LSHTState_Refine(l_ps), LSHTState_Refine(l_ps'));
{
    var h_ps := LSHTState_Refine(l_ps);
    //Lemma_LSHTNextOneHostMaintainsInvariant(l_ps, l_ps', idx, ios);
    var h_ps' := LSHTState_Refine(l_ps');

    Lemma_SHTStateRefinementLeavesHostDomainUnchanged(l_ps, h_ps);
    Lemma_SHTStateRefinementLeavesHostDomainUnchanged(l_ps', h_ps');
    assert mapdomain(h_ps'.hosts) == mapdomain(h_ps.hosts);
    
    var s := [h_ps, h_ps'];
    assert SHT_NextExternal(h_ps, h_ps', idx, LSHTIoSeq_RefineAsSends(ios), LSHTIoSeq_RefineAsSends(ios));  // OBSERVE: exists
    assert IsSHTStateRefinementSequenceOf(s, h_ps, h_ps');
}

lemma Lemma_LSHTNextEnvironmentImpliesSHTNext(l_s:LSHT_State, l_s':LSHT_State)
    requires LSHT_NextEnvironment(l_s, l_s');
    requires LSHTState_RefinementInvariant(l_s);
    requires LSHTState_RefinementInvariant(l_s');
    ensures  exists s:seq<SHT_State> :: IsSHTStateRefinementSequenceOf(s, LSHTState_Refine(l_s), LSHTState_Refine(l_s'));
{
    var h_s := LSHTState_Refine(l_s);
    var h_s' := LSHTState_Refine(l_s');

    assert h_s'.hosts == h_s.hosts;

    var s := [h_s];
    assert s[0] == LSHTState_Refine(l_s);

    assert h_s'.network == h_s.network;
    
    assert IsSHTStateRefinementSequenceOf(s, LSHTState_Refine(l_s), LSHTState_Refine(l_s'));
}

lemma Lemma_LSHTNextImpliesSHTNext(l_s:LSHT_State, l_s':LSHT_State)
    requires LSHT_Next(l_s, l_s');
    requires LSHTState_RefinementInvariant(l_s);
    ensures  LSHTState_RefinementInvariant(l_s');
    ensures  exists s:seq<SHT_State> :: IsSHTStateRefinementSequenceOf(s, LSHTState_Refine(l_s), LSHTState_Refine(l_s'));
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
