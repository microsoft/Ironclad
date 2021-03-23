include "../../SHT/Host.i.dfy"
include "../../SHT/Configuration.i.dfy"
include "../../../Common/Framework/Environment.s.dfy"
include "../Scheduler.i.dfy"

module LiveSHT__SHT_i {
import opened SHT__Host_i
import opened SHT__Configuration_i
import opened Environment_s
import opened Concrete_NodeIdentity_i`Spec
import opened LiveSHT__Scheduler_i
import opened LiveSHT__Environment_i

datatype LSHT_State = LSHT_State(
    config:SHTConfiguration,
    environment:LSHTEnvironment,
    hosts:seq<LScheduler>
)

predicate LSHT_MapsComplete(s:LSHT_State)
{
        |s.config.hostIds| == |s.hosts|
     && WFSHTConfiguration(s.config) 
     && (forall i :: 0 <= i < |s.config.hostIds| ==> s.hosts[i].host.me == s.config.hostIds[i])
}

predicate LSHT_Init(config:SHTConfiguration, s:LSHT_State) 
{
        LSHT_MapsComplete(s)
    && s.config == config
    && LEnvironment_Init(s.environment)
    && (forall i :: 0 <= i < |s.config.hostIds| ==> LScheduler_Init(s.hosts[i], s.config.hostIds[i], s.config.rootIdentity, s.config.hostIds, s.config.params))
}

predicate LSHT_NextOneHost(s:LSHT_State, s':LSHT_State, idx:int, ios:seq<LSHTIo>)
{
       LSHT_MapsComplete(s)
    && LSHT_MapsComplete(s')
    && s'.config == s.config
    && 0 <= idx < |s.config.hostIds|
    && LScheduler_Next(s.hosts[idx], s'.hosts[idx], ios)
    && LEnvironment_Next(s.environment, s'.environment)
    && s.environment.nextStep == LEnvStepHostIos(s.config.hostIds[idx], ios)
    && s'.hosts == s.hosts[idx := s'.hosts[idx]]
}

predicate LSHT_NextEnvironment(s:LSHT_State, s':LSHT_State)
{
       !s.environment.nextStep.LEnvStepHostIos?
    && LEnvironment_Next(s.environment, s'.environment)
    && s'.config == s.config
    && s'.hosts == s.hosts
}

predicate LSHT_NextExternal(s:LSHT_State, s':LSHT_State, eid:NodeIdentity, ios:seq<LSHTIo>)
{
       LSHT_MapsComplete(s)
    && LSHT_MapsComplete(s')
    && eid !in s.config.hostIds
    && LEnvironment_Next(s.environment, s'.environment)
    && s.environment.nextStep == LEnvStepHostIos(eid, ios)
    && s'.config == s.config
    && s'.hosts == s.hosts
}

predicate LSHT_Next(s:LSHT_State, s':LSHT_State)
{
       (exists idx, ios :: LSHT_NextOneHost(s, s', idx, ios))
    || (exists idx, ios :: LSHT_NextExternal(s, s', idx, ios))
    || LSHT_NextEnvironment(s, s')
}

}
