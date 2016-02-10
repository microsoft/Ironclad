include "SchedulerRefinement.i.dfy"
include "EnvironmentRefinement.i.dfy"
include "Environment.i.dfy"

module LiveSHT__SchedulerLemmas_i {
import opened LiveSHT__SchedulerRefinement_i
import opened LiveSHT__EnvironmentRefinement_i
import opened LiveSHT__Environment_i

lemma Lemma_LHostNextReceivePacketImpliesHostNextOrStutter(
    l_host:Host,
    l_host':Host,
    l_environment:LSHTEnvironment,
    l_environment':LSHTEnvironment,
    ios:seq<LSHTIo>
    )
    requires l_host.constants == l_host'.constants;
    requires LEnvironment_Next(l_environment, l_environment');
    requires l_environment.nextStep == LEnvStepHostIos(l_host.me, ios);
    requires LHost_ReceivePacket_Next(l_host, l_host', ios);
    ensures  HostNextOrStutter(l_host, l_host', PacketsTo(LSHTEnvironment_Refine(l_environment), l_host.me), LSHTIoSeq_RefineAsSends(ios));
{
    if (ios[0].LIoOpTimeoutReceive?) {
        assert l_host == l_host';
        return;
    }

    assert ios[0].r in l_environment.sentPackets;
    assert IsValidLEnvStep(l_environment, l_environment.nextStep);
    assert IsValidLIoOp(ios[0], l_host.me, l_environment);
    assert ios[0].r.dst == l_host.me;
    
    var sent_packets := ExtractSentPacketsFromIos(ios);
    Lemma_HostRefinementForPacketsAppliesToIos(l_host, l_host', PacketsTo(LSHTEnvironment_Refine(l_environment), l_host.me),
                                               ExtractPacketsFromLSHTPackets(sent_packets), l_environment, l_environment', ios);
}

lemma Lemma_LHostNextProcessReceivedPacketImpliesHostNextOrStutter(
    l_host:Host,
    l_host':Host,
    l_environment:LSHTEnvironment,
    l_environment':LSHTEnvironment,
    ios:seq<LSHTIo>
    )
    requires l_host.constants == l_host'.constants;
    requires l_host.me == l_host'.me;
    requires LHost_ProcessReceivedPacket_Next(l_host, l_host', ios);
    requires LEnvironment_Next(l_environment, l_environment');
    requires l_environment.nextStep == LEnvStepHostIos(l_host.me, ios);
    ensures  HostNextOrStutter(l_host, l_host', PacketsTo(LSHTEnvironment_Refine(l_environment), l_host.me), LSHTIoSeq_RefineAsSends(ios));
{
    var sent_packets := ExtractSentPacketsFromIos(ios);
    Lemma_HostRefinementForPacketsAppliesToIos(l_host, l_host', PacketsTo(LSHTEnvironment_Refine(l_environment), l_host.me),
                                               ExtractPacketsFromLSHTPackets(sent_packets), l_environment, l_environment', ios);
}

lemma Lemma_LHostNextSpontaneousImpliesHostNextOrStutter(
    l_scheduler:LScheduler, 
    l_scheduler':LScheduler,
    l_environment:LSHTEnvironment,
    l_environment':LSHTEnvironment,
    ios:seq<LSHTIo>
    )
    requires LHost_NoReceive_Next_Wrapper(l_scheduler, l_scheduler', ios);
    requires LEnvironment_Next(l_environment, l_environment');
    requires l_environment.nextStep == LEnvStepHostIos(l_scheduler.host.me, ios);
    ensures  HostNextOrStutter(l_scheduler.host, l_scheduler'.host,
                               PacketsTo(LSHTEnvironment_Refine(l_environment), l_scheduler.host.me), LSHTIoSeq_RefineAsSends(ios));
{
    if (l_scheduler'.resendCount == 0) {
        var sent_packets := ExtractSentPacketsFromIos(ios);
        Lemma_HostRefinementForPacketsAppliesToIos(l_scheduler.host, l_scheduler'.host,
                                                   PacketsTo(LSHTEnvironment_Refine(l_environment), l_scheduler.host.me),
                                                   ExtractPacketsFromLSHTPackets(sent_packets), l_environment, l_environment', ios);
    } else {
        assert l_scheduler'.host == l_scheduler.host;
        assert ios == [];
    }
}

lemma Lemma_LSchedulerNextImpliesHostNextOrStutter(l_scheduler:LScheduler, l_scheduler':LScheduler, l_environment:LSHTEnvironment,
                                                   l_environment':LSHTEnvironment, ios:seq<LSHTIo>)
    requires l_scheduler.host.constants == l_scheduler'.host.constants;
    requires l_scheduler.host.me == l_scheduler'.host.me;
    requires LScheduler_Next(l_scheduler, l_scheduler', ios);
    requires LEnvironment_Next(l_environment, l_environment');
    requires l_environment.nextStep == LEnvStepHostIos(l_scheduler.host.me, ios);
    requires LScheduler_RefinementInvariant(l_scheduler);
    ensures  LScheduler_RefinementInvariant(l_scheduler');
    ensures  HostNextOrStutter(l_scheduler.host, l_scheduler'.host,
                               PacketsTo(LSHTEnvironment_Refine(l_environment), l_scheduler.host.me), LSHTIoSeq_RefineAsSends(ios));
{
    assert 0 <= l_scheduler'.nextActionIndex < LHost_NumActions();
    var l_host  := l_scheduler.host;
    var l_host' := l_scheduler'.host;
    
    if l_scheduler.nextActionIndex == 0 {
        Lemma_LHostNextReceivePacketImpliesHostNextOrStutter(l_host, l_host', l_environment, l_environment', ios);
    } else if l_scheduler.nextActionIndex == 1 {
        Lemma_LHostNextProcessReceivedPacketImpliesHostNextOrStutter(l_host, l_host', l_environment, l_environment', ios);
    } else if l_scheduler.nextActionIndex == 2 {
        Lemma_LHostNextSpontaneousImpliesHostNextOrStutter(l_scheduler, l_scheduler', l_environment, l_environment', ios);
    }
}

}
