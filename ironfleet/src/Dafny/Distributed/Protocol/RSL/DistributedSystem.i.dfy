include "../../Common/Collections/Maps2.i.dfy"
include "Constants.i.dfy"
include "Environment.i.dfy"
include "Replica.i.dfy"

module LiveRSL__DistributedSystem_i {
import opened Collections__Maps2_i
import opened LiveRSL__Constants_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Message_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__Parameters_i
import opened Concrete_NodeIdentity_i
import opened Environment_s

datatype RslState = RslState(
  constants:LConstants,
  environment:LEnvironment<NodeIdentity, RslMessage>,
  replicas:seq<LScheduler>,
  clients:set<NodeIdentity>
  )

predicate RslMapsComplete(ps:RslState)
{
  |ps.replicas| == |ps.constants.config.replica_ids|
}

predicate RslConstantsUnchanged(ps:RslState, ps':RslState)
{
  && |ps'.replicas| == |ps.replicas|
  && ps'.clients == ps.clients
  && ps'.constants == ps.constants
}

predicate RslInit(con:LConstants, ps:RslState)
{
  && WellFormedLConfiguration(con.config)
  && WFLParameters(con.params)
  && ps.constants == con
  && LEnvironment_Init(ps.environment)
  && RslMapsComplete(ps)
  && (forall i :: 0 <= i < |con.config.replica_ids| ==> LSchedulerInit(ps.replicas[i], LReplicaConstants(i, con)))
}

predicate RslNextCommon(ps:RslState, ps':RslState)
{
  && RslMapsComplete(ps)
  && RslConstantsUnchanged(ps, ps')
  && LEnvironment_Next(ps.environment, ps'.environment)
}

predicate RslNextOneReplica(ps:RslState, ps':RslState, idx:int, ios:seq<RslIo>)
{
  && RslNextCommon(ps, ps')
  && 0 <= idx < |ps.constants.config.replica_ids|
  && LSchedulerNext(ps.replicas[idx], ps'.replicas[idx], ios)
  && ps.environment.nextStep == LEnvStepHostIos(ps.constants.config.replica_ids[idx], ios)
  && ps'.replicas == ps.replicas[idx := ps'.replicas[idx]]
}

predicate RslNextEnvironment(ps:RslState, ps':RslState)
{
  && RslNextCommon(ps, ps')
  && !ps.environment.nextStep.LEnvStepHostIos?
  && ps'.replicas == ps.replicas
}

predicate RslNextOneExternal(ps:RslState, ps':RslState, eid:NodeIdentity, ios:seq<RslIo>)
{
  && RslNextCommon(ps, ps')
  && eid !in ps.constants.config.replica_ids
  && ps.environment.nextStep == LEnvStepHostIos(eid, ios)
  && ps'.replicas == ps.replicas
}

predicate RslNext(ps:RslState, ps':RslState)
{
  || (exists idx, ios :: RslNextOneReplica(ps, ps', idx, ios))
  || (exists eid, ios :: RslNextOneExternal(ps, ps', eid, ios))
  || RslNextEnvironment(ps, ps')
}

} 
