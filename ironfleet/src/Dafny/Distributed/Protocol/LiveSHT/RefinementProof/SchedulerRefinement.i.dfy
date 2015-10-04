include "../Scheduler.i.dfy"
include "../../SHT/Host.i.dfy"
include "EnvironmentRefinement.i.dfy"

module LiveSHT__SchedulerRefinement_i {
import opened LiveSHT__Scheduler_i
import opened LiveSHT__EnvironmentRefinement_i
import opened SHT__Host_i

function AddPacketSets<Packet>(ps:seq<set<Packet>>) : set<Packet>
    ensures forall i :: 0 <= i < |ps| ==> ps[i] <= AddPacketSets(ps);
{
    if |ps| == 0 then {} else ps[0] + AddPacketSets(ps[1..])
}

predicate IsHostRefinementSequenceOf(hosts:seq<Host>, sends_by_step:seq<set<Packet>>, host:Host, host':Host,
                                        receives:set<Packet>, sends:set<Packet>)
{
       |hosts| > 0
    && |sends_by_step| == |hosts| - 1
    && host == hosts[0]
    && host' == hosts[|hosts|-1]
    && sends == AddPacketSets(sends_by_step)
    && (forall p :: p in receives ==> p.dst == host.me)
    && (forall p :: p in sends ==> p.src == host.me)
    && (forall i :: 0 <= i < |hosts|-1 ==> Host_Next(hosts[i], hosts[i+1], receives, sends_by_step[i]))
}


lemma Lemma_HostRefinementForPacketsAppliesToIos(
    host:Host,
    host':Host,
    receives:set<Packet>,
    sends:set<Packet>,
    environment:LSHTEnvironment,
    environment':LSHTEnvironment,
    ios:seq<LSHTIo>
    )
    requires LEnvironment_Next(environment, environment');
    requires environment.nextStep == LEnvStepHostIos(host.me, ios);
    requires receives <= PacketsTo(LSHTEnvironment_Refine(environment), host.me);
    requires sends == LSHTPacketSet_Refine(set io | io in ios && io.LIoOpSend? :: io.s);
    requires exists replicas, sends_at_step ::
                 IsHostRefinementSequenceOf(replicas, sends_at_step, host, host', receives, sends);
    ensures  exists replicas, sends_at_step ::
                 IsHostRefinementSequenceOf(replicas, sends_at_step, host, host',
                                               PacketsTo(LSHTEnvironment_Refine(environment), host.me), LSHTIoSeq_RefineAsSends(ios));
{
    var hosts, sends_at_step :| IsHostRefinementSequenceOf(hosts, sends_at_step, host, host', receives, sends);
    assert IsHostRefinementSequenceOf(hosts, sends_at_step, host, host',
                                         PacketsTo(LSHTEnvironment_Refine(environment), host.me), LSHTIoSeq_RefineAsSends(ios));
}

lemma Lemma_LHostUnchangedImpliesExistsRefinementSequence(
    l_host:Host,
    l_host':Host,
    receives:set<Packet>,
    sends:set<Packet>
    )
    requires l_host == l_host';
    requires forall p :: p in receives ==> p.dst == l_host.me;
    requires sends == {};
    ensures  exists h_replicas, h_sent_packets ::
                 IsHostRefinementSequenceOf(h_replicas, h_sent_packets, l_host, l_host', receives, sends);
{
    var h_host := l_host;
    var h_host' := l_host';

    var h_hosts := [ h_host ];
    var sends_by_step:seq<set<Packet>> := [];
    assert IsHostRefinementSequenceOf(h_hosts, sends_by_step, h_host, h_host', receives, sends);
}

predicate LScheduler_RefinementInvariant(s:LScheduler)
{
    0 <= s.nextActionIndex < LHost_NumActions()
}

function LScheduler_Refine(s:LScheduler) : Host
{
    s.host
}
} 
