include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "../../../Common/Framework/EnvironmentSynchronyLemmas.i.dfy"
include "../../Common/Liveness/RTSchedule.i.dfy"

module LivenessProof__RoundRobin_i {
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Constants_i
import opened Liveness__EnvironmentSynchronyLemmas_i
import opened Liveness__RTSchedule_i

function{:opaque} MakeLSHTAction_ReceivePacket_Temporal(
    b:Behavior<LSHT_State>,
    host_index:int
    ):temporal
    requires imaptotal(b);
    ensures  forall i {:trigger sat(i, MakeLSHTAction_ReceivePacket_Temporal(b, host_index))} ::
                 sat(i, MakeLSHTAction_ReceivePacket_Temporal(b, host_index)) <==>
                 b[i].environment.nextStep.LEnvStepHostIos? 
              && 0 <= host_index < |b[i].config.hostIds|
              && b[i].environment.nextStep.actor == b[i].config.hostIds[host_index] 
              && 0 <= host_index < |b[i].hosts|
              && b[i].hosts[host_index].nextActionIndex == 0
              && var ios := b[i].environment.nextStep.ios;
                 LSHT_NextOneHost(b[i], b[i+1], host_index, ios)
              && LHost_ReceivePacket_Next(b[i].hosts[host_index].host, b[i+1].hosts[host_index].host, ios);
{
    stepmap(imap i ::    b[i].environment.nextStep.LEnvStepHostIos? 
                      && 0 <= host_index < |b[i].config.hostIds|
                      && b[i].environment.nextStep.actor == b[i].config.hostIds[host_index] 
                      && 0 <= host_index < |b[i].hosts|
                      && b[i].hosts[host_index].nextActionIndex == 0
                      && var ios := b[i].environment.nextStep.ios;
                         LSHT_NextOneHost(b[i], b[i+1], host_index, ios)
                      && LHost_ReceivePacket_Next(b[i].hosts[host_index].host, b[i+1].hosts[host_index].host, ios))
}


function{:opaque} MakeLSHTAction_ProcessReceivedPacket_Temporal(
    b:Behavior<LSHT_State>,
    host_index:int
    ):temporal
    requires imaptotal(b);
    ensures  forall i {:trigger sat(i, MakeLSHTAction_ProcessReceivedPacket_Temporal(b, host_index))} ::
                 sat(i, MakeLSHTAction_ProcessReceivedPacket_Temporal(b, host_index)) <==>
                 b[i].environment.nextStep.LEnvStepHostIos? 
              && 0 <= host_index < |b[i].config.hostIds|
              && b[i].environment.nextStep.actor == b[i].config.hostIds[host_index] 
              && 0 <= host_index < |b[i].hosts|
              && b[i].hosts[host_index].nextActionIndex == 1
              && var ios := b[i].environment.nextStep.ios;
                 LSHT_NextOneHost(b[i], b[i+1], host_index, ios)
              && LHost_ProcessReceivedPacket_Next(b[i].hosts[host_index].host, b[i+1].hosts[host_index].host, ios);
{
    stepmap(imap i ::    b[i].environment.nextStep.LEnvStepHostIos? 
                      && 0 <= host_index < |b[i].config.hostIds|
                      && b[i].environment.nextStep.actor == b[i].config.hostIds[host_index] 
                      && 0 <= host_index < |b[i].hosts|
                      && b[i].hosts[host_index].nextActionIndex == 1
                      && var ios := b[i].environment.nextStep.ios;
                         LSHT_NextOneHost(b[i], b[i+1], host_index, ios)
                      && LHost_ProcessReceivedPacket_Next(b[i].hosts[host_index].host, b[i+1].hosts[host_index].host, ios))
}

function{:opaque} MakeLSHTAction_NoReceive_Next_Wrapper_Temporal(
    b:Behavior<LSHT_State>,
    host_index:int
    ):temporal
    requires imaptotal(b);
    ensures  forall i {:trigger sat(i, MakeLSHTAction_NoReceive_Next_Wrapper_Temporal(b, host_index))} ::
                 sat(i, MakeLSHTAction_NoReceive_Next_Wrapper_Temporal(b, host_index)) <==>
                 b[i].environment.nextStep.LEnvStepHostIos? 
              && 0 <= host_index < |b[i].config.hostIds|
              && b[i].environment.nextStep.actor == b[i].config.hostIds[host_index] 
              && 0 <= host_index < |b[i].hosts|
              && b[i].hosts[host_index].nextActionIndex == 2
              && var ios := b[i].environment.nextStep.ios;
                 LSHT_NextOneHost(b[i], b[i+1], host_index, ios)
              && LHost_NoReceive_Next_Wrapper(b[i].hosts[host_index], b[i+1].hosts[host_index], ios);
{
    stepmap(imap i ::    b[i].environment.nextStep.LEnvStepHostIos? 
                      && 0 <= host_index < |b[i].config.hostIds|
                      && b[i].environment.nextStep.actor == b[i].config.hostIds[host_index] 
                      && 0 <= host_index < |b[i].hosts|
                      && b[i].hosts[host_index].nextActionIndex == 2
                      && var ios := b[i].environment.nextStep.ios;
                         LSHT_NextOneHost(b[i], b[i+1], host_index, ios)
                      && LHost_NoReceive_Next_Wrapper(b[i].hosts[host_index], b[i+1].hosts[host_index], ios))
}

function HostSchedule(b:Behavior<LSHT_State>, host_index:int):seq<temporal>
    requires imaptotal(b);
{
    [ MakeLSHTAction_ReceivePacket_Temporal(b, host_index),
      MakeLSHTAction_ProcessReceivedPacket_Temporal(b, host_index),
      MakeLSHTAction_NoReceive_Next_Wrapper_Temporal(b, host_index)
    ]
}

lemma Lemma_SHTNextTakesSchedulerActionOrLeavesNextActionIndexUnchanged(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    host_index:int,
    next_action_type_fun:imap<int, int>,
    scheduler_action:temporal
    )
    requires LivenessAssumptions(b, asp);
    requires 0 <= host_index < |asp.c.hostIds|;
    requires imaptotal(next_action_type_fun);
    requires forall i {:trigger next_action_type_fun[i]} ::
                 next_action_type_fun[i] == if 0 <= host_index < |b[i].hosts| then b[i].hosts[host_index].nextActionIndex else 0;
    requires forall i :: sat(i, scheduler_action) <==> LSHTHostTakesAction(b[i], b[i+1], host_index);
    ensures sat(0, always(SchedulerActsOrNextActionTypeUnchangedTemporal(b, next_action_type_fun, scheduler_action)));
{
    var m := SchedulerActsOrNextActionTypeUnchangedTemporal(b, next_action_type_fun, scheduler_action);

    forall i | 0 <= i
        ensures sat(i, m);
    {
        assert LSHT_Next(b[i], b[i+1]);

        Lemma_ConstantsAllConsistent(b, asp.c, i);

        if (exists idx, ios :: LSHT_NextOneHost(b[i], b[i+1], idx, ios))
        {
            var idx, ios :| LSHT_NextOneHost(b[i], b[i+1], idx, ios);
            if (idx == host_index)
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

lemma Lemma_HostNextPerformsSubactionEventually(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    host_index:int,
    earliest_step:int,
    action_index:int
    ) returns
    (action_step:int)
    requires LivenessAssumptions(b, asp);
    requires 0 <= host_index < |asp.c.hostIds|;
    requires 0 <= action_index < LHost_NumActions();
    requires 0 <= earliest_step;
    ensures  earliest_step <= action_step;
    ensures  sat(action_step, HostSchedule(b, host_index)[action_index]);
{
    var next_action_type_fun := imap i :: if 0 <= host_index < |b[i].hosts| then b[i].hosts[host_index].nextActionIndex else 0;
    var scheduler_action := LSHTHostTakesActionTemporal(b, host_index);
    var schedule := HostSchedule(b, host_index);

    Lemma_SHTNextTakesSchedulerActionOrLeavesNextActionIndexUnchanged(b, asp, host_index, next_action_type_fun, scheduler_action);
    forall i | 0 <= i && sat(i, scheduler_action)
        ensures var action_type_index := next_action_type_fun[i];
                (0 <= action_type_index < |schedule| ==> sat(i, schedule[action_type_index]))
                && next_action_type_fun[i+1] == (action_type_index + 1) % |schedule|;
    {
    }

    action_step := Lemma_RoundRobinSchedulerEventuallyPerformsSpecificAction(b, next_action_type_fun, scheduler_action, schedule, 0, earliest_step, action_index);
}

lemma Lemma_HostNextPerformsProcessPacketEventually(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    host_index:int,
    earliest_step:int
    ) returns
    (action_step:int)
    requires LivenessAssumptions(b, asp);
    requires 0 <= host_index < |asp.c.hostIds|;
    requires 0 <= earliest_step;
    ensures  earliest_step <= action_step;
    ensures  sat(action_step, ReceiveAttemptedTemporal(RestrictBehaviorToEnvironment(b), asp.c.hostIds[host_index]));
{
    action_step := Lemma_HostNextPerformsSubactionEventually(b, asp, host_index, earliest_step, 0);
    var host := asp.c.hostIds[host_index];
    Lemma_ConstantsAllConsistent(b, asp.c, action_step);
    var ios := b[action_step].environment.nextStep.ios;
    assert |ios| >= 1 && (ios[0].LIoOpTimeoutReceive? || ios[0].LIoOpReceive?);
    assert ReceiveAttemptedInStep(b[action_step].environment, host);
}

} 
