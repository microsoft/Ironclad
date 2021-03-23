include "../Scheduler.i.dfy"
include "../../SHT/Host.i.dfy"
include "EnvironmentRefinement.i.dfy"

module LiveSHT__SchedulerRefinement_i {
import opened LiveSHT__Scheduler_i
import opened LiveSHT__EnvironmentRefinement_i
import opened Environment_s
import opened SHT__Host_i
import opened SHT__Network_i
import opened LiveSHT__Environment_i

function AddPacketSets<Packet>(ps:seq<set<Packet>>) : set<Packet>
    ensures forall i :: 0 <= i < |ps| ==> ps[i] <= AddPacketSets(ps);
{
    if |ps| == 0 then {} else ps[0] + AddPacketSets(ps[1..])
}

predicate HostNextOrStutter(host:Host, host':Host, receives:set<Packet>, sends:set<Packet>)
{
       (host == host' && sends == {})
    || (   (forall p :: p in receives ==> p.dst == host.me)
        && (forall p :: p in sends ==> p.src == host.me)
        && Host_Next(host, host', receives, sends))
}


lemma Lemma_HostRefinementForPacketsAppliesToIos(
    host:Host,
    host':Host,
    receives:set<Packet>,
    sent_packets:seq<LSHTPacket>,
    environment:LSHTEnvironment,
    environment':LSHTEnvironment,
    ios:seq<LSHTIo>
    )
    requires LEnvironment_Next(environment, environment');
    requires environment.nextStep == LEnvStepHostIos(host.me, ios);
    requires receives <= PacketsTo(LSHTEnvironment_Refine(environment), host.me);
    requires forall p :: p in sent_packets <==> p in (set io | io in ios && io.LIoOpSend? :: io.s);
    requires Host_Next(host, host', receives, ExtractPacketsFromLSHTPackets(sent_packets));
    ensures  Host_Next(host, host', PacketsTo(LSHTEnvironment_Refine(environment), host.me), LSHTIoSeq_RefineAsSends(ios));
{
    assert receives <= PacketsTo(LSHTEnvironment_Refine(environment), host.me);
    assert ExtractPacketsFromLSHTPackets(sent_packets) == LSHTIoSeq_RefineAsSends(ios);
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
