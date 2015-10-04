include "Invariants.i.dfy"
include "RoundRobin.i.dfy"
include "Constants.i.dfy"
include "RefinementInvariants.i.dfy"
include "../../../Common/Logic/Temporal/WF1.i.dfy"

module LivenessProof__Environment_i {
import opened LivenessProof__Invariants_i
import opened LivenessProof__RoundRobin_i
import opened LivenessProof__Constants_i
import opened LivenessProof__RefinementInvariants_i
import opened Temporal__WF1_i

lemma Lemma_AssumptionsMakeValidEnvironmentBehavior(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration
    )
    requires IsValidBehavior(b, c);
    ensures  LEnvironment_BehaviorSatisfiesSpec(RestrictBehaviorToEnvironment(b));
{
    var eb := RestrictBehaviorToEnvironment(b);
    var x := EnvironmentNextTemporal(eb);

    forall i | i >= 0
        ensures sat(i, x);
    {
        Lemma_AssumptionsMakeValidTransition(b, c, i);
        assert LEnvironment_Next(eb[i], eb[i+1]);
    }

    TemporalAlways(0, x);
    assert LEnvironment_Init(eb[0]);
    assert LEnvironment_BehaviorSatisfiesSpec(eb);
}

lemma Lemma_PacketStaysInSentPackets(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    j:int,
    p:LSHTPacket
    )
    requires IsValidBehaviorPrefix(b, c, j);
    requires 0 <= i <= j;
    requires p in b[i].environment.sentPackets;
    ensures  p in b[j].environment.sentPackets;
{
    if j == i
    {
    }
    else
    {
        Lemma_PacketStaysInSentPackets(b, c, i, j-1, p);
        Lemma_AssumptionsMakeValidTransition(b, c, j-1);
    }
}

lemma Lemma_PositionOfPacketInHostQueueEventuallyDecreasesByOne(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    current_step:int,
    host_idx:int,
    p:LSHTPacket,
    pos:int
    )
    returns
    (next_step:int)
    requires LivenessAssumptions(b, asp);
    requires 0 <= current_step;
    requires 0 <= host_idx < |asp.c.hostIds|;
    requires asp.c.hostIds[host_idx] in b[current_step].environment.hostInfo;
    requires 1 <= pos < |b[current_step].environment.hostInfo[asp.c.hostIds[host_idx]].queue|;
    requires p == b[current_step].environment.hostInfo[asp.c.hostIds[host_idx]].queue[pos];
    ensures  current_step <= next_step;
    ensures  asp.c.hostIds[host_idx] in b[next_step].environment.hostInfo;
    ensures  pos-1 < |b[next_step].environment.hostInfo[asp.c.hostIds[host_idx]].queue|;
    ensures  p == b[next_step].environment.hostInfo[asp.c.hostIds[host_idx]].queue[pos-1];
{
    var host := asp.c.hostIds[host_idx];
    var P := stepmap(imap i ::    host in b[i].environment.hostInfo
                             && |b[i].environment.hostInfo[host].queue| > pos
                             && p == b[i].environment.hostInfo[host].queue[pos]);
    var Q := stepmap(imap i ::    host in b[i].environment.hostInfo
                             && |b[i].environment.hostInfo[host].queue| > pos-1
                             && p == b[i].environment.hostInfo[host].queue[pos-1]);

    var action_step := Lemma_HostNextPerformsSubactionEventually(b, asp, host_idx, current_step, 0);

    forall j | current_step <= j
        ensures sat(j, TemporalWF1Req1(P, Q));
    {
        Lemma_EffectOfNextOnHostQueue(b, asp, j, host_idx);
    }

    forall ensures sat(action_step, imply(P, or(Q, next(Q))))
    {
        if sat(action_step, P)
        {
            Lemma_ConstantsAllConsistent(b, asp.c, action_step);
            var ios := b[action_step].environment.nextStep.ios;
            var hostQueue := if host in b[action_step].environment.hostInfo then b[action_step].environment.hostInfo[host].queue else [];
            var hostQueue' := if host in b[action_step+1].environment.hostInfo then b[action_step+1].environment.hostInfo[host].queue else [];
            Lemma_HostQueuesNext(b, asp, action_step);
            assert HostQueue_PerformIos(hostQueue, hostQueue', ios);
            assert |ios| > 0;
            if ios[0].LIoOpTimeoutReceive?
            {
                assert false;
            }
            else
            {
                assert ios[0].LIoOpReceive?;
                assert |ios| == 1 || (ios[1] in ios /* trigger */ && !ios[1].LIoOpReceive?);
                assert HostQueue_PerformIos(hostQueue[1..], hostQueue', ios[1..]);
                assert hostQueue[1..] == hostQueue';
            }
            assert sat(action_step+1, Q);
        }
    }

    next_step := TemporalWF1Specific(current_step, action_step, P, Q);
}

lemma Lemma_PositionOfPacketInHostQueueEventuallyDecreasesToZero(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    current_step:int,
    host_idx:int,
    p:LSHTPacket,
    pos:int
    )
    returns
    (next_step:int)
    requires LivenessAssumptions(b, asp);
    requires 0 <= current_step;
    requires 0 <= host_idx < |asp.c.hostIds|;
    requires asp.c.hostIds[host_idx] in b[current_step].environment.hostInfo;
    requires 0 <= pos < |b[current_step].environment.hostInfo[asp.c.hostIds[host_idx]].queue|;
    requires p == b[current_step].environment.hostInfo[asp.c.hostIds[host_idx]].queue[pos];
    ensures  current_step <= next_step;
    ensures  asp.c.hostIds[host_idx] in b[next_step].environment.hostInfo;
    ensures  0 < |b[next_step].environment.hostInfo[asp.c.hostIds[host_idx]].queue|;
    ensures  p == b[next_step].environment.hostInfo[asp.c.hostIds[host_idx]].queue[0];
    decreases pos;
{
    if pos == 0
    {
        next_step := current_step;
    }
    else
    {
        var intermediate_step := Lemma_PositionOfPacketInHostQueueEventuallyDecreasesByOne(b, asp, current_step, host_idx, p, pos);
        next_step := Lemma_PositionOfPacketInHostQueueEventuallyDecreasesToZero(b, asp, intermediate_step, host_idx, p, pos-1);
    }
}

lemma Lemma_PacketInHostQueueEventuallyAtFrontOfHostQueue(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    current_step:int,
    host_idx:int,
    p:LSHTPacket
    )
    returns
    (next_step:int)
    requires LivenessAssumptions(b, asp);
    requires 0 <= current_step;
    requires 0 <= host_idx < |asp.c.hostIds|;
    requires asp.c.hostIds[host_idx] in b[current_step].environment.hostInfo;
    requires p in b[current_step].environment.hostInfo[asp.c.hostIds[host_idx]].queue;
    ensures  current_step <= next_step;
    ensures  asp.c.hostIds[host_idx] in b[next_step].environment.hostInfo;
    ensures  0 < |b[next_step].environment.hostInfo[asp.c.hostIds[host_idx]].queue|;
    ensures  p == b[next_step].environment.hostInfo[asp.c.hostIds[host_idx]].queue[0];
{
    var host := asp.c.hostIds[host_idx];
    var queue := b[current_step].environment.hostInfo[host].queue;
    var pos :| 0 <= pos < |queue| && queue[pos] == p;
    next_step := Lemma_PositionOfPacketInHostQueueEventuallyDecreasesToZero(b, asp, current_step, host_idx, p, pos);
}

} 
