include "../Replica.i.dfy"
include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Environment.i.dfy"
include "Invariants.i.dfy"
include "RealTime.i.dfy"
include "../CommonProof/Constants.i.dfy"
include "../../../Common/Framework/EnvironmentSynchronyLemmas.i.dfy"
include "../../Common/Liveness/RTSchedule.i.dfy"
include "../../../../Libraries/Math/mul.i.dfy"

module LivenessProof__RoundRobin_i {
import opened LiveRSL__Replica_i
import opened LiveRSL__DistributedSystem_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Environment_i
import opened LivenessProof__Invariants_i
import opened CommonProof__Constants_i
import opened Liveness__EnvironmentSynchronyLemmas_i
import opened Liveness__RTSchedule_i
import opened LivenessProof__RealTime_i
import opened Math__mul_i

function{:opaque} MakeRslActionTemporalFromReplicaFunction(
    b:Behavior<RslState>,
    action_fun:(LReplica, LReplica, seq<RslIo>)->bool,
    replica_index:int
    ):temporal
    reads action_fun.reads;
    requires forall r, r', ios :: action_fun.requires(r, r', ios);
    requires imaptotal(b);
    ensures  forall i {:trigger sat(i, MakeRslActionTemporalFromReplicaFunction(b, action_fun, replica_index))} ::
                 sat(i, MakeRslActionTemporalFromReplicaFunction(b, action_fun, replica_index)) <==>
                 exists ios ::    RslNextOneReplica(b[i], b[i+1], replica_index, ios)
                               && action_fun(b[i].replicas[replica_index].replica, b[i+1].replicas[replica_index].replica, ios);
{
    stepmap(imap i :: exists ios ::    RslNextOneReplica(b[i], b[i+1], replica_index, ios)
                                    && action_fun(b[i].replicas[replica_index].replica, b[i+1].replicas[replica_index].replica, ios))
}

function{:opaque} MakeRslActionTemporalFromSpontaneousReplicaFunction(
    b:Behavior<RslState>,
    action_fun:(LReplica, LReplica, seq<RslPacket>)->bool,
    replica_index:int
    ):temporal
    reads action_fun.reads;
    requires forall r, r', ios :: action_fun.requires(r, r', ios);
    requires imaptotal(b);
    ensures  forall i {:trigger sat(i, MakeRslActionTemporalFromSpontaneousReplicaFunction(b, action_fun, replica_index))} ::
                 sat(i, MakeRslActionTemporalFromSpontaneousReplicaFunction(b, action_fun, replica_index)) <==>
                 exists ios ::    RslNextOneReplica(b[i], b[i+1], replica_index, ios)
                               && SpontaneousIos(ios, 0)
                               && action_fun(b[i].replicas[replica_index].replica, b[i+1].replicas[replica_index].replica, ExtractSentPacketsFromIos(ios));
{
    stepmap(imap i :: exists ios ::    RslNextOneReplica(b[i], b[i+1], replica_index, ios)
                                    && SpontaneousIos(ios, 0)
                                    && action_fun(b[i].replicas[replica_index].replica, b[i+1].replicas[replica_index].replica, ExtractSentPacketsFromIos(ios)))
}

function{:opaque} MakeRslActionTemporalFromReadClockReplicaFunction(
    b:Behavior<RslState>,
    action_fun:(LReplica, LReplica, ClockReading, seq<RslPacket>)->bool,
    replica_index:int
    ):temporal
    reads action_fun.reads;
    requires forall r, r', ios :: action_fun.requires(r, r', SpontaneousClock(ios), ExtractSentPacketsFromIos(ios));
    requires imaptotal(b);
    ensures  forall i {:trigger sat(i, MakeRslActionTemporalFromReadClockReplicaFunction(b, action_fun, replica_index))} ::
                 sat(i, MakeRslActionTemporalFromReadClockReplicaFunction(b, action_fun, replica_index)) <==>
                 exists ios ::    RslNextOneReplica(b[i], b[i+1], replica_index, ios)
                               && SpontaneousIos(ios, 1)
                               && action_fun(b[i].replicas[replica_index].replica, b[i+1].replicas[replica_index].replica, SpontaneousClock(ios), ExtractSentPacketsFromIos(ios));
{
    stepmap(imap i :: exists ios ::    RslNextOneReplica(b[i], b[i+1], replica_index, ios)
                                    && SpontaneousIos(ios, 1)
                                    && action_fun(b[i].replicas[replica_index].replica, b[i+1].replicas[replica_index].replica, SpontaneousClock(ios), ExtractSentPacketsFromIos(ios)))
}

function ReplicaSchedule(b:Behavior<RslState>, replica_index:int):seq<temporal>
    requires imaptotal(b);
{
    [ MakeRslActionTemporalFromReplicaFunction(b, LReplicaNextProcessPacket, replica_index),
      MakeRslActionTemporalFromSpontaneousReplicaFunction(b, LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a, replica_index),
      MakeRslActionTemporalFromSpontaneousReplicaFunction(b, LReplicaNextSpontaneousMaybeEnterPhase2, replica_index),
      MakeRslActionTemporalFromReadClockReplicaFunction(b, LReplicaNextReadClockMaybeNominateValueAndSend2a, replica_index),
      MakeRslActionTemporalFromSpontaneousReplicaFunction(b, LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints, replica_index),
      MakeRslActionTemporalFromSpontaneousReplicaFunction(b, LReplicaNextSpontaneousMaybeMakeDecision, replica_index),
      MakeRslActionTemporalFromSpontaneousReplicaFunction(b, LReplicaNextSpontaneousMaybeExecute, replica_index),
      MakeRslActionTemporalFromReadClockReplicaFunction(b, LReplicaNextReadClockCheckForViewTimeout, replica_index),
      MakeRslActionTemporalFromReadClockReplicaFunction(b, LReplicaNextReadClockCheckForQuorumOfViewSuspicions, replica_index),
      MakeRslActionTemporalFromReadClockReplicaFunction(b, LReplicaNextReadClockMaybeSendHeartbeat, replica_index)
    ]
}

function TimeToPerformGenericAction(asp:AssumptionParameters):int
    requires asp.host_period > 0;
    ensures  TimeToPerformGenericAction(asp) >= 0;
{
    lemma_mul_nonnegative(asp.host_period, LReplicaNumActions());
    asp.host_period * LReplicaNumActions()
}

lemma lemma_PaxosNextTakesSchedulerActionOrLeavesNextActionIndexUnchanged(
    b:Behavior<RslState>,
    asp:AssumptionParameters,
    replica_index:int,
    next_action_type_fun:imap<int, int>,
    scheduler_action:temporal
    )
    requires LivenessAssumptions(b, asp);
    requires 0 <= replica_index < |asp.c.config.replica_ids|;
    requires imaptotal(next_action_type_fun);
    requires forall i {:trigger next_action_type_fun[i]} ::
                 next_action_type_fun[i] == if 0 <= replica_index < |b[i].replicas| then b[i].replicas[replica_index].nextActionIndex else 0;
    requires forall i ::
                 sat(i, scheduler_action) <==>
                 exists ios :: RslNextOneReplica(b[i], b[i+1], replica_index, ios) && LSchedulerNext(b[i].replicas[replica_index], b[i+1].replicas[replica_index], ios);
    ensures sat(0, always(SchedulerActsOrNextActionTypeUnchangedTemporal(b, next_action_type_fun, scheduler_action)));
{
    var m := SchedulerActsOrNextActionTypeUnchangedTemporal(b, next_action_type_fun, scheduler_action);

    forall i | TLe(0, i)
        ensures sat(i, m);
    {
        assert RslNext(b[i], b[i+1]);

        lemma_ConstantsAllConsistent(b, asp.c, i);

        if (exists idx, ios :: RslNextOneReplica(b[i], b[i+1], idx, ios))
        {
            var idx, ios :| RslNextOneReplica(b[i], b[i+1], idx, ios);
            if (idx == replica_index)
            {
                assert sat(i, scheduler_action);
            }
            else
            {
                assert next_action_type_fun[i] == next_action_type_fun[i+1];
            }
        }
        else
        {
            assert next_action_type_fun[i] == next_action_type_fun[i+1];
        }

        assert sat(i, m);
    }
    TemporalAlways(0, m);
}

lemma lemma_ReplicaNextPerformsSubactionPeriodically(
    b:Behavior<RslState>,
    asp:AssumptionParameters,
    replica_index:int,
    action_index:int
    )
    requires LivenessAssumptions(b, asp);
    requires replica_index in asp.live_quorum;
    requires 0 <= action_index < LReplicaNumActions();
    ensures  var real_time_fun := PaxosTimeMap(b);
             var longer_interval := TimeToPerformGenericAction(asp);
             sat(asp.synchrony_start, always(eventuallynextwithin(ReplicaSchedule(b, replica_index)[action_index], longer_interval, real_time_fun)));
{
    var next_action_type_fun := imap i :: if 0 <= replica_index < |b[i].replicas| then b[i].replicas[replica_index].nextActionIndex else 0;
    var real_time_fun := PaxosTimeMap(b);
    var scheduler_action := MakeRslActionTemporalFromSchedulerFunction(b, replica_index);
    var schedule := ReplicaSchedule(b, replica_index);

    var t := stepmap(imap j :: real_time_fun[j] <= real_time_fun[j+1]);
    forall j | 0 <= j
        ensures sat(j, t);
    {
        lemma_AssumptionsMakeValidTransition(b, asp.c, j);
    }
    TemporalAlways(0, t);
    Lemma_MonotonicStepsLeadToMonotonicBehavior(0, real_time_fun);

    lemma_PaxosNextTakesSchedulerActionOrLeavesNextActionIndexUnchanged(b, asp, replica_index, next_action_type_fun, scheduler_action);
    assert HostExecutesPeriodically(b, asp, replica_index);
    Lemma_RoundRobinSchedulerTimelyForAllActionsTemporal(b, next_action_type_fun, real_time_fun, scheduler_action, schedule, asp.synchrony_start, asp.host_period);

    assert sat(asp.synchrony_start, always(eventuallynextwithin(schedule[action_index], asp.host_period * |schedule|, real_time_fun)));
    assert sat(asp.synchrony_start, always(eventuallynextwithin(ReplicaSchedule(b, replica_index)[action_index], TimeToPerformGenericAction(asp), real_time_fun)));
}

lemma lemma_ReplicaNextPerformsSubactionSoon(
    b:Behavior<RslState>,
    asp:AssumptionParameters,
    start_step:int,
    replica_index:int,
    action_index:int
    ) returns
    (action_step:int)
    requires LivenessAssumptions(b, asp);
    requires replica_index in asp.live_quorum;
    requires 0 <= action_index < LReplicaNumActions();
    requires asp.synchrony_start <= start_step;
    ensures  start_step <= action_step;
    ensures  b[action_step+1].environment.time <= b[start_step].environment.time + TimeToPerformGenericAction(asp);
    ensures  sat(action_step, ReplicaSchedule(b, replica_index)[action_index]);
{
    var x := ReplicaSchedule(b, replica_index)[action_index];
    var t := TimeToPerformGenericAction(asp);
    var f := PaxosTimeMap(b);
    
    lemma_ReplicaNextPerformsSubactionPeriodically(b, asp, replica_index, action_index);
    TemporalDeduceFromAlways(asp.synchrony_start, start_step, eventuallynextwithin(x, t, f));
    action_step := TemporalDeduceFromEventuallyNextWithin(start_step, x, t, f);
}

lemma lemma_ReplicaNextPerformsSubactionSoonAfter(
    b:Behavior<RslState>,
    asp:AssumptionParameters,
    start_step:int,
    replica_index:int,
    action_index:int,
    earliest:int
    ) returns
    (action_step:int)
    requires LivenessAssumptions(b, asp);
    requires replica_index in asp.live_quorum;
    requires 0 <= action_index < LReplicaNumActions();
    requires asp.synchrony_start <= start_step;
    ensures  start_step <= action_step;
    ensures  b[action_step+1].environment.time >= earliest;
    ensures  b[action_step+1].environment.time <= TimeToPerformGenericAction(asp) + (if earliest >= b[start_step].environment.time then earliest else b[start_step].environment.time);
    ensures  sat(action_step, ReplicaSchedule(b, replica_index)[action_index]);
{
    var x := ReplicaSchedule(b, replica_index)[action_index];
    var t := TimeToPerformGenericAction(asp);
    var f := PaxosTimeMap(b);
    
    lemma_ReplicaNextPerformsSubactionPeriodically(b, asp, replica_index, action_index);
    TemporalDeduceFromAlways(asp.synchrony_start, start_step, eventuallynextwithin(x, t, f));

    if earliest < b[start_step].environment.time
    {
        action_step := TemporalDeduceFromEventuallyNextWithin(start_step, x, t, f);
        assert b[action_step+1].environment.time <= b[start_step].environment.time + t;
        lemma_TimeAdvancesBetween(b, asp, start_step, action_step+1);
    }
    else
    {
        Lemma_AlwaysImpliesLaterAlways(asp.synchrony_start, start_step, eventuallynextwithin(x, t, f));
        lemma_TimeMonotonicFromInvariantHolds(b, asp, 0);
        lemma_AfterForm(b, asp);
        action_step := Lemma_AlwaysEventuallyWithinMeansAlwaysEventuallyWithinAfter(start_step, x, earliest - b[start_step].environment.time, t, f);
        assert b[action_step+1].environment.time <= b[start_step].environment.time + (earliest - b[start_step].environment.time) + t;
    }
}

lemma lemma_ProcessingPacketCausesReceiveAttempt(
    b:Behavior<RslState>,
    asp:AssumptionParameters,
    replica_index:int,
    i:int
    )
    requires LivenessAssumptions(b, asp);
    requires 0 <= i;
    requires 0 <= replica_index < |asp.c.config.replica_ids|;
    requires sat(i, MakeRslActionTemporalFromReplicaFunction(b, LReplicaNextProcessPacket, replica_index));
    ensures  sat(i, ReceiveAttemptedTemporal(RestrictBehaviorToEnvironment(b), asp.c.config.replica_ids[replica_index]));
{
    var eb := RestrictBehaviorToEnvironment(b);
    var host := asp.c.config.replica_ids[replica_index];
    lemma_ReplicasSize(b, asp.c, i);
    var action := MakeRslActionTemporalFromReplicaFunction(b, LReplicaNextProcessPacket, replica_index);
    assert sat(i, action);
    var ios :| RslNextOneReplica(b[i], b[i+1], replica_index, ios) && LReplicaNextProcessPacket(b[i].replicas[replica_index].replica, b[i+1].replicas[replica_index].replica, ios);
    assert |ios| >= 1 && (ios[0].LIoOpTimeoutReceive? || ios[0].LIoOpReceive?);
    lemma_ConstantsAllConsistent(b, asp.c, i);
    assert ReceiveAttemptedInStep(b[i].environment, host);
    assert sat(i, ReceiveAttemptedTemporal(eb, host));
}

lemma lemma_ReplicaNextPerformsProcessPacketPeriodically(
    b:Behavior<RslState>,
    asp:AssumptionParameters,
    replica_index:int
    )
    requires LivenessAssumptions(b, asp);
    requires replica_index in asp.live_quorum;
    ensures  var real_time_fun := PaxosTimeMap(b);
             var longer_interval := TimeToPerformGenericAction(asp);
             sat(asp.synchrony_start, always(eventuallynextwithin(MakeRslActionTemporalFromReplicaFunction(b, LReplicaNextProcessPacket, replica_index), longer_interval, real_time_fun)));
    ensures  var real_time_fun := PaxosTimeMap(b);
             var longer_interval := TimeToPerformGenericAction(asp);
             var host := asp.c.config.replica_ids[replica_index];
             sat(asp.synchrony_start, always(eventuallynextwithin(ReceiveAttemptedTemporal(RestrictBehaviorToEnvironment(b), host), longer_interval, real_time_fun)));
{
    var real_time_fun := PaxosTimeMap(b);
    var longer_interval := TimeToPerformGenericAction(asp);
    lemma_ReplicaNextPerformsSubactionPeriodically(b, asp, replica_index, 0);
    assert sat(asp.synchrony_start, always(eventuallynextwithin(MakeRslActionTemporalFromReplicaFunction(b, LReplicaNextProcessPacket, replica_index), longer_interval, real_time_fun)));

    var host := asp.c.config.replica_ids[replica_index];

    var eb := RestrictBehaviorToEnvironment(b);
    forall i | TLe(asp.synchrony_start, i)
        ensures sat(i, eventuallynextwithin(ReceiveAttemptedTemporal(eb, host), longer_interval, real_time_fun));
    {
        lemma_ReplicasSize(b, asp.c, i);
        TemporalDeduceFromAlways(asp.synchrony_start, i, eventuallynextwithin(MakeRslActionTemporalFromReplicaFunction(b, LReplicaNextProcessPacket, replica_index), longer_interval, real_time_fun));
        var j := TemporalDeduceFromEventuallyNextWithin(i, MakeRslActionTemporalFromReplicaFunction(b, LReplicaNextProcessPacket, replica_index), longer_interval, real_time_fun);
        lemma_ProcessingPacketCausesReceiveAttempt(b, asp, replica_index, j);
        TemporalEventuallyNextWithin(i, j, ReceiveAttemptedTemporal(eb, host), longer_interval, real_time_fun);
    }
    TemporalAlways(asp.synchrony_start, eventuallynextwithin(ReceiveAttemptedTemporal(RestrictBehaviorToEnvironment(b), host), longer_interval, real_time_fun));
}

} 
