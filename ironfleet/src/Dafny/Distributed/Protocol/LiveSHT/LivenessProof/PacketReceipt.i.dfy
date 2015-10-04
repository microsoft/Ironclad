include "Assumptions.i.dfy"
include "Environment.i.dfy"
include "Acks.i.dfy"
include "PacketSending.i.dfy"

module LivenessProof__PacketReceipt_i {

import opened LivenessProof__Assumptions_i
import opened LivenessProof__Environment_i
import opened LivenessProof__Acks_i
import opened LivenessProof__PacketSending_i

predicate SHTPacketSent(ss:LSHT_State, p:LSHTPacket)
{
       ss.environment.nextStep.LEnvStepHostIos?
    && LIoOpSend(p) in ss.environment.nextStep.ios
}

function{:opaque} SHTPacketSentTemporal(b:Behavior<LSHT_State>, p:LSHTPacket):temporal
    requires imaptotal(b);
    ensures  forall i{:trigger sat(i, SHTPacketSentTemporal(b, p))} ::
             sat(i, SHTPacketSentTemporal(b, p)) <==> SHTPacketSent(b[i], p);
{
    stepmap(imap i :: SHTPacketSent(b[i], p))
}

predicate IsDelegateStep(
    ps:LSHT_State,
    ps':LSHT_State,
    idx:int
    )
{
       0 <= idx < |ps.hosts|
    && 0 <= idx < |ps.config.hostIds|
    && 0 <= idx < |ps'.hosts|
    && ps.environment.nextStep.LEnvStepHostIos?
    && ps.environment.nextStep.actor == ps.config.hostIds[idx]
    && ps.hosts[idx].nextActionIndex == 1
    && ps.hosts[idx].host.receivedPacket.Some?
    && ps.hosts[idx].host.receivedPacket.v.src in ps.config.hostIds
    && ps.hosts[idx].host.receivedPacket.v.dst == ps.config.hostIds[idx]
    && ps.hosts[idx].host.receivedPacket.v.msg.SingleMessage?
    && ps.hosts[idx].host.receivedPacket.v.msg.m.Delegate?
    && ps'.hosts[idx].host.receivedPacket.None?
}

predicate IsShardStepOfHost(
    ps:LSHT_State,
    ps':LSHT_State,
    idx:int
    )
{
       0 <= idx < |ps.hosts|
    && 0 <= idx < |ps.config.hostIds|
    && 0 <= idx < |ps'.hosts|
    && ps.environment.nextStep.LEnvStepHostIos?
    && ps.environment.nextStep.actor == ps.config.hostIds[idx]
    && ps.hosts[idx].nextActionIndex == 1
    && ps.hosts[idx].host.receivedPacket.Some?
    && ps.hosts[idx].host.receivedPacket.v.dst == ps.config.hostIds[idx]
    && ps.hosts[idx].host.receivedPacket.v.msg.SingleMessage?
    && ps.hosts[idx].host.receivedPacket.v.msg.m.Shard?
    && ps'.hosts[idx].host.receivedPacket.None?
}

predicate IsShardStepOfOtherHost(
    ps:LSHT_State,
    ps':LSHT_State,
    idx:int
    )
{
    exists other_idx :: other_idx != idx && IsShardStepOfHost(ps, ps', other_idx)
}

function AllDelegatePacketsToHost(b:Behavior<LSHT_State>, i:int, dst:NodeIdentity):set<LSHTPacket>
    requires imaptotal(b);
{
    set p | p in b[i].environment.sentPackets && p.src in b[i].config.hostIds && p.msg.SingleMessage? && p.msg.m.Delegate? && p.dst == dst
}

lemma Lemma_ReceivedPacketAlwaysSingleMessageToProperDestination(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    idx:int
    )
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= idx < |c.hostIds|;
    ensures  0 <= idx < |b[i].hosts|;
    ensures  var p := b[i].hosts[idx].host.receivedPacket;
             p.Some? ==> p.v.msg.SingleMessage? && p.v.dst == c.hostIds[idx];
{
    if i == 0
    {
        return;
    }
    
    Lemma_AssumptionsMakeValidTransition(b, c, i-1);
    Lemma_ConstantsAllConsistent(b, c, i-1);
    Lemma_ReceivedPacketAlwaysSingleMessageToProperDestination(b, c, i-1, idx);

    if b[i].hosts[idx].host.receivedPacket == b[i-1].hosts[idx].host.receivedPacket
    {
        return;
    }

    var ap := Lemma_ActionThatChangesHostIsThatHostsAction(b, c, i-1, idx);
}

lemma Lemma_ReceivedPacketInTombstoneTable(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    idx:int
    )
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= idx < |b[i].hosts|;
    requires b[i].hosts[idx].host.receivedPacket.Some?;
    requires b[i].hosts[idx].host.receivedPacket.v.msg.SingleMessage?;
    ensures  var host := b[i].hosts[idx].host;
             TombstoneTableLookup(host.receivedPacket.v.src, host.sd.receiveState) >= host.receivedPacket.v.msg.seqno;
{
    if i == 0
    {
        return;
    }

    Lemma_AssumptionsMakeValidTransition(b, c, i-1);
    Lemma_ConstantsAllConsistent(b, c, i-1);
    Lemma_ConstantsAllConsistent(b, c, i);

    var host := b[i-1].hosts[idx].host;
    var host' := b[i].hosts[idx].host;
    var src := host'.receivedPacket.v.src;

    if host'.receivedPacket == host.receivedPacket
    {
        Lemma_ReceivedPacketInTombstoneTable(b, c, i-1, idx);
        Lemma_RecipientSequenceNumberMonotonicOneStep(b, c, i-1, src, idx);
        return;
    }

    var ap := Lemma_ActionThatChangesHostIsThatHostsAction(b, c, i-1, idx);
}

lemma Lemma_PacketsProcessedInDifferentStepsHaveDifferentSourcesOrSequenceNumbers(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    j:int,
    idx:int
    )
    requires IsValidBehaviorPrefix(b, c, j);
    requires 0 <= i < j;
    requires 0 <= idx < |b[i].hosts| == |b[i+1].hosts| == |b[j].hosts| == |c.hostIds|;
    requires b[i].environment.nextStep.LEnvStepHostIos?;
    requires b[i].environment.nextStep.actor == c.hostIds[idx];
    requires b[i].hosts[idx].host.receivedPacket.Some?;
    requires b[i+1].hosts[idx].host.receivedPacket.None?;
    requires b[j].environment.nextStep.LEnvStepHostIos?;
    requires b[j].environment.nextStep.actor == c.hostIds[idx];
    requires b[j].hosts[idx].host.receivedPacket.Some?;
    ensures  b[i].hosts[idx].host.receivedPacket.v.msg.SingleMessage?;
    ensures  b[j].hosts[idx].host.receivedPacket.v.msg.SingleMessage?;
    ensures  var p1 := b[i].hosts[idx].host.receivedPacket.v;
             var p2 := b[j].hosts[idx].host.receivedPacket.v;
             p1.src != p2.src || p1.msg.seqno < p2.msg.seqno;
{
    Lemma_ReceivedPacketAlwaysSingleMessageToProperDestination(b, c, i, idx);
    Lemma_ReceivedPacketAlwaysSingleMessageToProperDestination(b, c, j, idx);

    var p1 := b[i].hosts[idx].host.receivedPacket.v;
    var p2 := b[j].hosts[idx].host.receivedPacket.v;
    if p1.src != p2.src
    {
        return;
    }

    Lemma_ReceivedPacketInTombstoneTable(b, c, i, idx);

    var x := stepmap(imap k ::    0 <= idx < |b[k].hosts|
                              && b[k].hosts[idx].host.receivedPacket.Some?
                              && b[k].hosts[idx].host.receivedPacket.v == p2);
    assert !sat(i+1, x);
    assert sat(j, x);
    var transition_step := earliestStepBetween(i+1, j, x) - 1;
    assert i+1 <= transition_step < j;
    assert !sat(transition_step, x);
    Lemma_ConstantsAllConsistent(b, c, transition_step);

    var ap := Lemma_ActionThatChangesHostIsThatHostsAction(b, c, transition_step, idx);
    Lemma_RecipientSequenceNumberMonotonic(b, c, i, transition_step, p2.src, idx);
}

lemma Lemma_GetPacketsFromShardStepsOfHost(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    host_idx:int,
    shard_steps:set<int>
    )
    returns
    (shard_packets:set<LSHTPacket>)
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= host_idx < |c.hostIds|;
    requires forall step :: step in shard_steps ==> 0 <= step < i && IsShardStepOfHost(b[step], b[step+1], host_idx);
    ensures  forall shard_packet :: shard_packet in shard_packets ==> shard_packet.dst == c.hostIds[host_idx];
    ensures  shard_packets <= AllShardPacketsSent(b[i].environment.sentPackets);
    ensures  |shard_steps| == |shard_packets|;
{
    Lemma_ConstantsAllConsistent(b, c, i);

    var f := ((step:int) requires step in shard_steps => PacketToLSHTPacket(b[step].hosts[host_idx].host.receivedPacket.v));
    shard_packets := set step | step in shard_steps :: f(step);

    assert forall step :: step in shard_steps ==> f(step) in shard_packets;

    forall shard_packet | shard_packet in shard_packets
        ensures shard_packet.dst == c.hostIds[host_idx];
    {
        var step :| step in shard_steps && shard_packet == f(step);
        Lemma_ConstantsAllConsistent(b, c, step);
    }
    
    forall step1, step2 |    step1 in shard_steps
                          && step2 in shard_steps
                          && f(step1) in shard_packets
                          && f(step2) in shard_packets
                          && f(step1) == f(step2)
                          && step1 != step2
        ensures false;
    {
        Lemma_ConstantsAllConsistent(b, c, step1);
        Lemma_ConstantsAllConsistent(b, c, step2);
        var p1 := b[step1].hosts[host_idx].host.receivedPacket.v;
        var p2 := b[step2].hosts[host_idx].host.receivedPacket.v;
        Lemma_ReceivedPacketWasSent(b, c, step1, host_idx);
        Lemma_ReceivedPacketWasSent(b, c, step2, host_idx);
        assert p1.src == p2.src;
        if step1 < step2
        {
            Lemma_ConstantsAllConsistent(b, c, step1+1);
            Lemma_PacketsProcessedInDifferentStepsHaveDifferentSourcesOrSequenceNumbers(b, c, step1, step2, host_idx);
        }
        else
        {
            Lemma_ConstantsAllConsistent(b, c, step2+1);
            Lemma_PacketsProcessedInDifferentStepsHaveDifferentSourcesOrSequenceNumbers(b, c, step2, step1, host_idx);
        }
        assert p1.msg.seqno != p2.msg.seqno;
        assert false;
    }

    lemma_MapSetCardinalityOver(shard_steps, shard_packets, f);

    var all_shard_packets := AllShardPacketsSent(b[i].environment.sentPackets);
    forall shard_packet | shard_packet in shard_packets
        ensures shard_packet in all_shard_packets;
    {
        var step :| step in shard_steps && shard_packet == f(step);
        Lemma_ReceivedPacketWasSent(b, c, step, host_idx);
        Lemma_PacketStaysInSentPackets(b, c, step, i, shard_packet);
    }
    assert shard_packets <= all_shard_packets;
}

lemma Lemma_GetPacketsFromShardStepsOfOtherHost(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    host_idx:int,
    shard_steps:set<int>
    )
    returns
    (shard_packets:set<LSHTPacket>)
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= host_idx < |c.hostIds|;
    requires forall step :: step in shard_steps ==> 0 <= step < i && IsShardStepOfOtherHost(b[step], b[step+1], host_idx);
    ensures  forall shard_packet :: shard_packet in shard_packets ==> shard_packet.dst != c.hostIds[host_idx];
    ensures  shard_packets <= AllShardPacketsSent(b[i].environment.sentPackets);
    ensures  |shard_steps| == |shard_packets|;
{
    Lemma_ConstantsAllConsistent(b, c, i);

    var f := ((step:int) requires step in shard_steps =>
              assert IsShardStepOfOtherHost(b[step], b[step+1], host_idx);
              var other_idx :| other_idx != host_idx && IsShardStepOfHost(b[step], b[step+1], other_idx);
              PacketToLSHTPacket(b[step].hosts[other_idx].host.receivedPacket.v));
    shard_packets := set step | step in shard_steps :: f(step);

    assert forall step :: step in shard_steps ==> f(step) in shard_packets;

    forall shard_packet | shard_packet in shard_packets
        ensures shard_packet.dst != c.hostIds[host_idx];
    {
        var step :| step in shard_steps && shard_packet == f(step);
        var other_idx :| other_idx != host_idx && IsShardStepOfHost(b[step], b[step+1], other_idx);
        Lemma_ConstantsAllConsistent(b, c, step);
        assert HostsDistinct(c.hostIds, host_idx, other_idx);
    }
    
    forall step1, step2 |    step1 in shard_steps
                          && step2 in shard_steps
                          && f(step1) in shard_packets
                          && f(step2) in shard_packets
                          && f(step1) == f(step2)
                          && step1 != step2
        ensures false;
    {
        Lemma_ConstantsAllConsistent(b, c, step1);
        Lemma_ConstantsAllConsistent(b, c, step2);
        var other_idx1 :|    other_idx1 != host_idx
                          && IsShardStepOfHost(b[step1], b[step1+1], other_idx1)
                          && f(step1) == PacketToLSHTPacket(b[step1].hosts[other_idx1].host.receivedPacket.v);
        var other_idx2 :|    other_idx2 != host_idx
                          && IsShardStepOfHost(b[step2], b[step2+1], other_idx2)
                          && f(step2) == PacketToLSHTPacket(b[step2].hosts[other_idx2].host.receivedPacket.v);
        var p1 := b[step1].hosts[other_idx1].host.receivedPacket.v;
        var p2 := b[step2].hosts[other_idx2].host.receivedPacket.v;
        Lemma_ReceivedPacketWasSent(b, c, step1, other_idx1);
        Lemma_ReceivedPacketWasSent(b, c, step2, other_idx2);
        assert HostsDistinct(c.hostIds, other_idx1, other_idx2);
        if step1 < step2
        {
            Lemma_ConstantsAllConsistent(b, c, step1+1);
            Lemma_PacketsProcessedInDifferentStepsHaveDifferentSourcesOrSequenceNumbers(b, c, step1, step2, other_idx1);
        }
        else
        {
            Lemma_ConstantsAllConsistent(b, c, step2+1);
            Lemma_PacketsProcessedInDifferentStepsHaveDifferentSourcesOrSequenceNumbers(b, c, step2, step1, other_idx2);
        }
        assert p1.msg.seqno != p2.msg.seqno;
        assert false;
    }

    lemma_MapSetCardinalityOver(shard_steps, shard_packets, f);

    var all_shard_packets := AllShardPacketsSent(b[i].environment.sentPackets);
    forall shard_packet | shard_packet in shard_packets
        ensures shard_packet in all_shard_packets;
    {
        var step :| step in shard_steps && shard_packet == f(step);
        var other_idx :|    other_idx != host_idx
                         && IsShardStepOfHost(b[step], b[step+1], other_idx)
                         && shard_packet == PacketToLSHTPacket(b[step].hosts[other_idx].host.receivedPacket.v);
        Lemma_ReceivedPacketWasSent(b, c, step, other_idx);
        Lemma_PacketStaysInSentPackets(b, c, step, i, shard_packet);
    }
    assert shard_packets <= all_shard_packets;
}

lemma {:timeLimitMultiplier 3} Lemma_GetShardStepsLeadingToDelegateMessages(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    host_idx:int
    ) returns
    (shard_steps:set<int>)
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= host_idx < |c.hostIds|;
    ensures  0 <= host_idx < |b[i].hosts|;
    ensures  |shard_steps| == |AllDelegatePacketsToHost(b, i, c.hostIds[host_idx])|;
    ensures  forall step :: step in shard_steps ==> 0 <= step < i && IsShardStepOfOtherHost(b[step], b[step+1], host_idx);
{
    if i == 0 {
        shard_steps := {};
        return;
    }

    Lemma_AssumptionsMakeValidTransition(b, c, i-1);
    Lemma_ConstantsAllConsistent(b, c, i-1);
    Lemma_ConstantsAllConsistent(b, c, i);

    shard_steps := Lemma_GetShardStepsLeadingToDelegateMessages(b, c, i-1, host_idx);

    var dst := c.hostIds[host_idx];
    var s := b[i-1].hosts[host_idx].host;
    var s' := b[i].hosts[host_idx].host;

    if AllDelegatePacketsToHost(b, i, dst) == AllDelegatePacketsToHost(b, i-1, dst)
    {
        return;
    }

    var p :|    p in b[i].environment.sentPackets
             && p !in b[i-1].environment.sentPackets
             && p.src in b[i].config.hostIds
             && p.msg.SingleMessage?
             && p.msg.m.Delegate?
             && p.dst == dst;
    var ap := Lemma_ActionThatSendsPacketIsActionOfSource(b, c, i-1, p);
    Lemma_ActionThatSendsFreshPacketIsNotResend(b, c, i-1, ap, p);
    
    assert ap.nextActionIndex == 1;
    assert ap.idx != host_idx;

    Lemma_ReceivedPacketAlwaysSingleMessageToProperDestination(b, c, i-1, ap.idx);
    assert IsShardStepOfHost(b[i-1], b[i], ap.idx);
    shard_steps := shard_steps + {i-1};

    assert AllDelegatePacketsToHost(b, i, dst) == AllDelegatePacketsToHost(b, i-1, dst) + {p};
}

lemma Lemma_GetPacketsFromDelegateSteps(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    host_idx:int,
    delegate_steps:set<int>
    )
    returns
    (delegate_packets:set<LSHTPacket>)
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= host_idx < |c.hostIds|;
    requires forall step :: step in delegate_steps ==> 0 <= step < i && IsDelegateStep(b[step], b[step+1], host_idx);
    ensures  delegate_packets <= AllDelegatePacketsToHost(b, i, c.hostIds[host_idx]);
    ensures  |delegate_steps| == |delegate_packets|;
{
    Lemma_ConstantsAllConsistent(b, c, i);

    var dst := c.hostIds[host_idx];
    var f := ((step:int) requires step in delegate_steps => PacketToLSHTPacket(b[step].hosts[host_idx].host.receivedPacket.v));
    delegate_packets := set step | step in delegate_steps :: f(step);

    assert forall step :: step in delegate_steps ==> f(step) in delegate_packets;

    forall step1, step2 |    step1 in delegate_steps
                          && step2 in delegate_steps
                          && f(step1) in delegate_packets
                          && f(step2) in delegate_packets
                          && f(step1) == f(step2)
                          && step1 != step2
        ensures false;
    {
        Lemma_ConstantsAllConsistent(b, c, step1);
        Lemma_ConstantsAllConsistent(b, c, step2);
        var p1 := b[step1].hosts[host_idx].host.receivedPacket.v;
        var p2 := b[step2].hosts[host_idx].host.receivedPacket.v;
        Lemma_ReceivedPacketWasSent(b, c, step1, host_idx);
        Lemma_ReceivedPacketWasSent(b, c, step2, host_idx);
        assert p1.src == p2.src;
        if step1 < step2
        {
            Lemma_ConstantsAllConsistent(b, c, step1+1);
            Lemma_PacketsProcessedInDifferentStepsHaveDifferentSourcesOrSequenceNumbers(b, c, step1, step2, host_idx);
        }
        else
        {
            Lemma_ConstantsAllConsistent(b, c, step2+1);
            Lemma_PacketsProcessedInDifferentStepsHaveDifferentSourcesOrSequenceNumbers(b, c, step2, step1, host_idx);
        }
        assert p1.msg.seqno != p2.msg.seqno;
        assert false;
    }

    lemma_MapSetCardinalityOver(delegate_steps, delegate_packets, f);

    var all_delegate_packets := AllDelegatePacketsToHost(b, i, dst);
    forall delegate_packet | delegate_packet in delegate_packets
        ensures delegate_packet in all_delegate_packets;
    {
        var step :| step in delegate_steps && delegate_packet == f(step);
        Lemma_ConstantsAllConsistent(b, c, step);
        Lemma_ReceivedPacketWasSent(b, c, step, host_idx);
        Lemma_PacketStaysInSentPackets(b, c, step, i, delegate_packet);
        assert delegate_packet.dst == dst;
    }
    assert delegate_packets <= all_delegate_packets;
}


lemma Lemma_GetDelegateAndShardStepsLeadingToNumDelegations(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    host_idx:int
    ) returns
    (delegate_steps:set<int>,
     shard_steps:set<int>)
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= host_idx < |c.hostIds|;
    ensures  0 <= host_idx < |b[i].hosts|;
    ensures  |delegate_steps| + |shard_steps| + 1 == b[i].hosts[host_idx].host.numDelegations;
    ensures  forall step :: step in delegate_steps ==> 0 <= step < i && IsDelegateStep(b[step], b[step+1], host_idx);
    ensures  forall step :: step in shard_steps ==> 0 <= step < i && IsShardStepOfHost(b[step], b[step+1], host_idx);
{
    if i == 0 {
        delegate_steps := {};
        shard_steps := {};
        return;
    }

    Lemma_AssumptionsMakeValidTransition(b, c, i-1);
    Lemma_ConstantsAllConsistent(b, c, i-1);
    Lemma_ConstantsAllConsistent(b, c, i);

    delegate_steps, shard_steps := Lemma_GetDelegateAndShardStepsLeadingToNumDelegations(b, c, i-1, host_idx);

    var s := b[i-1].hosts[host_idx].host;
    var s' := b[i].hosts[host_idx].host;

    if s'.numDelegations == s.numDelegations
    {
        return;
    }

    var ap := Lemma_ActionThatChangesHostIsThatHostsAction(b, c, i-1, host_idx);
    assert ap.nextActionIndex == 1;
    assert s'.numDelegations == s.numDelegations + 1;

    Lemma_ReceivedPacketAlwaysSingleMessageToProperDestination(b, c, i-1, host_idx);

    if IsShardStepOfHost(b[i-1], b[i], host_idx)
    {
        shard_steps := shard_steps + {i-1};
    }
    else
    {
        assert IsDelegateStep(b[i-1], b[i], host_idx);
        delegate_steps := delegate_steps + {i-1};
    }
}

lemma Lemma_DelegationBound(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    i:int,
    host_idx:int
    )
    requires LivenessAssumptions(b, asp);
    requires 0 <= i;
    requires 0 <= host_idx < |asp.c.hostIds|;
    ensures  0 <= host_idx < |b[i].hosts|;
    ensures  b[i].hosts[host_idx].host.numDelegations < asp.c.params.max_delegations - 2;
{
    Lemma_ConstantsAllConsistent(b, asp.c, i);

    var host := asp.c.hostIds[host_idx];
    var delegate_steps, shard_steps_direct := Lemma_GetDelegateAndShardStepsLeadingToNumDelegations(b, asp.c, i, host_idx);
    var shard_packets_direct := Lemma_GetPacketsFromShardStepsOfHost(b, asp.c, i, host_idx, shard_steps_direct);
    var delegate_packets := Lemma_GetPacketsFromDelegateSteps(b, asp.c, i, host_idx, delegate_steps);
    var all_delegate_packets := AllDelegatePacketsToHost(b, i, asp.c.hostIds[host_idx]);
    SubsetCardinality(delegate_packets, all_delegate_packets);
    
    var shard_steps_indirect := Lemma_GetShardStepsLeadingToDelegateMessages(b, asp.c, i, host_idx);
    assert |shard_steps_indirect| == |all_delegate_packets|;
    var shard_packets_indirect := Lemma_GetPacketsFromShardStepsOfOtherHost(b, asp.c, i, host_idx, shard_steps_indirect);

    forall p1, p2 | p1 in shard_packets_direct && p2 in shard_packets_indirect
        ensures p1 != p2;
    {
        assert p1.dst == host;
        assert p2.dst != host;
    }
    var shard_packets := shard_packets_direct + shard_packets_indirect;
    assert |shard_packets| == |shard_packets_direct| + |shard_packets_indirect|;

    var all_shard_packets := AllShardPacketsSent(b[i].environment.sentPackets);
    SubsetCardinality(shard_packets, all_shard_packets);

    calc {
        b[i].hosts[host_idx].host.numDelegations;
        |delegate_steps| + |shard_steps_direct| + 1;
        |delegate_packets| + |shard_packets_direct| + 1;
        <= |all_delegate_packets| + |shard_packets_direct| + 1;
        |shard_steps_indirect| + |shard_packets_direct| + 1;
        |shard_packets_indirect| + |shard_packets_direct| + 1;
        |shard_packets| + 1;
        <= |all_shard_packets| + 1;
        <= asp.c.params.max_delegations - 4 + 1;
    }
}

lemma Lemma_ReceivedPacketSlotEmptyUnlessNextActionIndexOne(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    i:int,
    idx:int
    )
    requires LivenessAssumptions(b, asp);
    requires 0 <= i;
    requires 0 <= idx < |asp.c.hostIds|;
    ensures  0 <= idx < |b[i].hosts|;
    ensures  var s := b[i].hosts[idx];
             s.host.receivedPacket.Some? ==> s.nextActionIndex == 1;
{
    if i == 0
    {
        return;
    }

    Lemma_AssumptionsMakeValidTransition(b, asp.c, i-1);
    Lemma_ConstantsAllConsistent(b, asp.c, i-1);
    Lemma_ReceivedPacketSlotEmptyUnlessNextActionIndexOne(b, asp, i-1, idx);

    if b[i-1].hosts[idx] == b[i].hosts[idx]
    {
        return;
    }

    var ap := Lemma_ActionThatChangesHostIsThatHostsAction(b, asp.c, i-1, idx);
    Lemma_ReceivedPacketAlwaysSingleMessageToProperDestination(b, asp.c, i-1, idx);
    assert 0 <= idx < |asp.c.hostIds| && 0 <= i-1 && 0 <= idx < |b[i-1].hosts|;
    Lemma_DelegationBound(b, asp, i-1, idx);
    assert b[i-1].hosts[idx].host.numDelegations < asp.c.params.max_delegations - 2;
}


lemma Lemma_PacketInHostQueueStaysThereUnlessActionZeroOccurs(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    i:int,
    host_idx:int,
    host:NodeIdentity,
    p:LSHTPacket
    )
    requires LivenessAssumptions(b, asp);
    requires 0 <= i;
    requires 0 <= host_idx < |asp.c.hostIds|;
    requires host == asp.c.hostIds[host_idx];
    requires host in b[i].environment.hostInfo;
    requires |b[i].environment.hostInfo[host].queue| > 0;
    requires p == b[i].environment.hostInfo[host].queue[0];
    requires !(   b[i].environment.nextStep.LEnvStepHostIos?
               && b[i].environment.nextStep.actor == host
               && 0 <= host_idx < |b[i].hosts|
               && b[i].hosts[host_idx].nextActionIndex == 0);
    ensures  host in b[i+1].environment.hostInfo;
    ensures  |b[i+1].environment.hostInfo[host].queue| > 0;
    ensures  p == b[i+1].environment.hostInfo[host].queue[0];
{
    Lemma_AssumptionsMakeValidTransition(b, asp.c, i);
    Lemma_ConstantsAllConsistent(b, asp.c, i);
    Lemma_HostQueuesNext(b, asp, i);

    var hostQueue := if host in b[i].environment.hostInfo then b[i].environment.hostInfo[host].queue else [];
    var hostQueue' := if host in b[i+1].environment.hostInfo then b[i+1].environment.hostInfo[host].queue else [];

    if    b[i].environment.nextStep.LEnvStepHostIos? 
       && b[i].environment.nextStep.actor in b[i].config.hostIds
    {
        var ap := Lemma_GetParametersOfAction(b, asp.c, i);
        var id := asp.c.hostIds[ap.idx];
        if ap.idx != host_idx
        {
            assert HostsDistinct(asp.c.hostIds, ap.idx, host_idx);
            assert hostQueue' == hostQueue;
        }
        else
        {
            assert HostQueue_PerformIos(hostQueue, hostQueue', ap.ios);
            assert ap.nextActionIndex != 0;
            assert |ap.ios| == 0 || (ap.ios[0] in ap.ios /* trigger */ && ap.ios[0].LIoOpSend?);
            assert hostQueue' == hostQueue;
        }
    }
}


lemma Lemma_PacketInHostQueueEventuallyReceived(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    current_step:int,
    host_idx:int,
    p:LSHTPacket
    )
    returns
    (next_step:int,
     ap:SHTActionParams)
    requires LivenessAssumptions(b, asp);
    requires 0 <= current_step;
    requires 0 <= host_idx < |asp.c.hostIds|;
    requires asp.c.hostIds[host_idx] in b[current_step].environment.hostInfo;
    requires p in b[current_step].environment.hostInfo[asp.c.hostIds[host_idx]].queue;
    ensures  current_step <= next_step;
    ensures  SHTActionOccurred(b[next_step], b[next_step+1], ap);
    ensures  ap.idx == host_idx;
    ensures  ap.nextActionIndex == 0;
    ensures  b[next_step].hosts[host_idx].host.receivedPacket.None?;
    ensures  |ap.ios| > 0;
    ensures  ap.ios[0] == LIoOpReceive(p);
{
    var host := asp.c.hostIds[host_idx];
    var intermediate_step := Lemma_PacketInHostQueueEventuallyAtFrontOfHostQueue(b, asp, current_step, host_idx, p);

    var P := stepmap(imap i ::   host in b[i].environment.hostInfo
                             && |b[i].environment.hostInfo[host].queue| > 0
                             && p == b[i].environment.hostInfo[host].queue[0]);
    var Q := stepmap(imap i ::    host in b[i].environment.hostInfo
                             && |b[i].environment.hostInfo[host].queue| > 0
                             && p == b[i].environment.hostInfo[host].queue[0]
                             && b[i].environment.nextStep.LEnvStepHostIos?
                             && b[i].environment.nextStep.actor == host
                             && 0 <= host_idx < |b[i].hosts|
                             && b[i].hosts[host_idx].nextActionIndex == 0);

    var action_step := Lemma_HostNextPerformsSubactionEventually(b, asp, host_idx, intermediate_step, 0);

    forall j | intermediate_step <= j
        ensures sat(j, TemporalWF1Req1(P, Q));
    {
        if sat(j, P) && !sat(j, Q)
        {
            Lemma_PacketInHostQueueStaysThereUnlessActionZeroOccurs(b, asp, j, host_idx, host, p);
            assert sat(j+1, P);
        }
    }

    forall ensures sat(action_step, imply(P, or(Q, next(Q))))
    {
        if sat(action_step, P)
        {
            Lemma_ConstantsAllConsistent(b, asp.c, action_step);
            var ap_intermediate := Lemma_GetParametersOfAction(b, asp.c, action_step);
            Lemma_GetHostIndexIsUnique(asp.c, host_idx);
            assert host_idx == ap_intermediate.idx;
            assert sat(action_step, Q);
        }
    }

    next_step := TemporalWF1Specific(intermediate_step, action_step, P, Q);
    Lemma_ConstantsAllConsistent(b, asp.c, next_step);
    ap := Lemma_GetParametersOfAction(b, asp.c, next_step);
    Lemma_GetHostIndexIsUnique(asp.c, host_idx);
    Lemma_ReceivedPacketSlotEmptyUnlessNextActionIndexOne(b, asp, next_step, host_idx);
    Lemma_HostQueuesNext(b, asp, next_step);
}


lemma Lemma_DeliveredPacketEventuallyReceived(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    deliver_step:int,
    host_idx:int,
    p:LSHTPacket
    )
    returns
    (next_step:int,
     ap:SHTActionParams)
    requires LivenessAssumptions(b, asp);
    requires 0 <= deliver_step;
    requires 0 <= host_idx < |asp.c.hostIds|;
    requires p.dst == asp.c.hostIds[host_idx];
    requires b[deliver_step].environment.nextStep == LEnvStepDeliverPacket(p);
    ensures  deliver_step + 1 <= next_step;
    ensures  SHTActionOccurred(b[next_step], b[next_step+1], ap);
    ensures  ap.idx == host_idx;
    ensures  ap.nextActionIndex == 0;
    ensures  b[next_step].hosts[host_idx].host.receivedPacket.None?;
    ensures  |ap.ios| > 0;
    ensures  ap.ios[0] == LIoOpReceive(p);
{
    Lemma_AssumptionsMakeValidTransition(b, asp.c, deliver_step);
    Lemma_HostQueuesNext(b, asp, deliver_step);
    next_step, ap := Lemma_PacketInHostQueueEventuallyReceived(b, asp, deliver_step + 1, host_idx, p);
}


lemma Lemma_PacketSentInfinitelyOftenEventuallyReceived(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    current_step:int,
    src_idx:int,
    dst_idx:int,
    p:LSHTPacket
    )
    returns
    (receive_step:int,
     ap:SHTActionParams)
    requires LivenessAssumptions(b, asp);
    requires 0 <= src_idx < |asp.c.hostIds|;
    requires 0 <= dst_idx < |asp.c.hostIds|;
    requires sat(current_step, always(eventual(SHTPacketSentTemporal(b, p))));
    requires 0 <= current_step;
    requires p.src == asp.c.hostIds[src_idx];
    requires p.dst == asp.c.hostIds[dst_idx];
    ensures  current_step <= receive_step;
    ensures  SHTActionOccurred(b[receive_step], b[receive_step+1], ap);
    ensures  ap.idx == dst_idx;
    ensures  ap.nextActionIndex == 0;
    ensures  b[receive_step].hosts[dst_idx].host.receivedPacket.None?;
    ensures  |ap.ios| > 0;
    ensures  ap.ios[0] == LIoOpReceive(p);
{
    var eb := RestrictBehaviorToEnvironment(b);
    var host_set := SeqToSet(asp.c.hostIds);
    assert NetworkWeaklyFair(eb, asp.c.hostIds);

    forall i | current_step <= i
        ensures sat(i, eventual(PacketSentBetweenHostsTemporal(eb, p, host_set, host_set)));
    {
        TemporalDeduceFromAlways(current_step, i, eventual(SHTPacketSentTemporal(b, p)));
        var j := TemporalDeduceFromEventual(i, SHTPacketSentTemporal(b, p));
        Lemma_HostQueuesNext(b, asp, j);
        Lemma_ConstantsAllConsistent(b, asp.c, j);
        Lemma_GetHostIndexIsUnique(asp.c, src_idx);
        Lemma_GetHostIndexIsUnique(asp.c, dst_idx);
        assert PacketSentBetweenHosts(eb[j], p, host_set, host_set);
        TemporalEventually(i, j, PacketSentBetweenHostsTemporal(eb, p, host_set, host_set));
    }
    TemporalAlways(current_step, eventual(PacketSentBetweenHostsTemporal(eb, p, host_set, host_set)));
    
    TemporalDeduceFromAlways(0, current_step, imply(always(eventual(PacketSentBetweenHostsTemporal(eb, p, host_set, host_set))),
                                                    eventual(PacketDeliveredTemporal(eb, p))));
    var deliver_step := TemporalDeduceFromEventual(current_step, PacketDeliveredTemporal(eb, p));
    receive_step, ap := Lemma_DeliveredPacketEventuallyReceived(b, asp, deliver_step, dst_idx, p);
}

}
