include "Assumptions.i.dfy"
include "../../../Common/Framework/HostQueueLemmas.i.dfy"
include "Constants.i.dfy"
include "RefinementInvariants.i.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module LivenessProof__Invariants_i {
import opened LivenessProof__Assumptions_i
import opened Liveness__HostQueueLemmas_i
import opened LivenessProof__Constants_i
import opened LivenessProof__RefinementInvariants_i
import opened Collections__Seqs_s

lemma Lemma_HostQueuesNext(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    i:int
    )
    requires LivenessAssumptions(b, asp);
    requires 0 <= i;
    ensures  HostQueues_Next(b[i].environment, b[i+1].environment);
{
    TemporalDeduceFromAlways(0, i, HostQueuesNextTemporal(RestrictBehaviorToEnvironment(b)));
}

lemma Lemma_LEnvironmentInvariantHolds(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    i:int
    )
    requires LivenessAssumptions(b, asp);
    requires 0 <= i;
    ensures  LEnvironmentInvariant(b[i].environment);
{
    if i == 0
    {
        Lemma_LEnvironmentInitEstablishesInvariant(b[i].environment);
    }
    else
    {
        Lemma_LEnvironmentInvariantHolds(b, asp, i-1);
        Lemma_AssumptionsMakeValidTransition(b, asp.c, i-1);
        Lemma_HostQueuesNext(b, asp, i-1);

        Lemma_LEnvironmentNextPreservesInvariant(b[i-1].environment, b[i].environment);
    }
}

lemma Lemma_EffectOfNextOnHostQueue(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    i:int,
    host_idx:int
    )
    requires LivenessAssumptions(b, asp);
    requires 0 <= i;
    requires 0 <= host_idx < |asp.c.hostIds|;
    ensures  var host := asp.c.hostIds[host_idx];
             var hostQueue := if host in b[i].environment.hostInfo then b[i].environment.hostInfo[host].queue else [];
             var hostQueue' := if host in b[i+1].environment.hostInfo then b[i+1].environment.hostInfo[host].queue else [];
                (hostQueue' == hostQueue)
             || (|hostQueue'| > 0 && all_but_last(hostQueue') == hostQueue)
             || (|hostQueue| > 0 && hostQueue' == hostQueue[1..]);
{
    Lemma_AssumptionsMakeValidTransition(b, asp.c, i);
    Lemma_HostQueuesNext(b, asp, i);
    Lemma_ConstantsAllConsistent(b, asp.c, i);
    Lemma_ConstantsAllConsistent(b, asp.c, i+1);

    var host := asp.c.hostIds[host_idx];
    var hostQueue := if host in b[i].environment.hostInfo then b[i].environment.hostInfo[host].queue else [];
    var hostQueue' := if host in b[i+1].environment.hostInfo then b[i+1].environment.hostInfo[host].queue else [];

    if b[i].environment.nextStep.LEnvStepHostIos? 
    {
        if b[i].environment.nextStep.actor in b[i].config.hostIds {
            var ap := Lemma_GetParametersOfAction(b, asp.c, i);
            var id := asp.c.hostIds[ap.idx];
            if ap.idx != host_idx
            {
                assert HostsDistinct(asp.c.hostIds, ap.idx, host_idx);
            }
            else
            {
                assert HostQueue_PerformIos(hostQueue, hostQueue', ap.ios);
                if ap.nextActionIndex == 0
                {
                    if ap.ios[0].LIoOpTimeoutReceive?
                    {
                        assert hostQueue' == hostQueue;
                    }
                    else
                    {
                        assert ap.ios[0].LIoOpReceive?;
                        assert |ap.ios| == 1 || (ap.ios[1] in ap.ios /* trigger */ && !ap.ios[1].LIoOpReceive?);
                        assert HostQueue_PerformIos(hostQueue[1..], hostQueue', ap.ios[1..]);
                        assert hostQueue[1..] == hostQueue';
                    }
                }
                else if ap.nextActionIndex == 1
                {
                    assert |ap.ios| == 0 || (ap.ios[0] in ap.ios /* trigger */ && ap.ios[0].LIoOpSend?);
                    assert hostQueue' == hostQueue;
                }
                else
                {
                    assert |ap.ios| == 0 || (ap.ios[0] in ap.ios /* trigger */ && ap.ios[0].LIoOpSend?);
                    assert hostQueue' == hostQueue;
                }
            }
        } else {
            // NextExternal
        }
    }
    else
    {
        assert LSHT_NextEnvironment(b[i], b[i+1]);
    }
}

} 
