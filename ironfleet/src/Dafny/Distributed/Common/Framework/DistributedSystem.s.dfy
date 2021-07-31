include "Host.s.dfy"
include "../Collections/Maps2.s.dfy"

abstract module DistributedSystem_s {

import H_s : Host_s
import opened Collections__Maps2_s
import opened Native__Io_s
import opened Environment_s
import opened Native__NativeTypes_s

/////////////////////////////////////////
// PHYSICAL ENVIRONMENT
//
// TODO - Move this stuff to Io.s
//
/////////////////////////////////////////

predicate ValidPhysicalAddress(endPoint:EndPoint)
{
  |endPoint.public_key| < 0x10_0000 // < 1 MB
}
    
predicate ValidPhysicalPacket(p:LPacket<EndPoint, seq<byte>>)
{
  && ValidPhysicalAddress(p.src)
  && ValidPhysicalAddress(p.dst)
  && |p.msg| < 0x1_0000_0000_0000_0000
}
  
predicate ValidPhysicalIo(io:LIoOp<EndPoint, seq<byte>>)
{
  && (io.LIoOpReceive? ==> ValidPhysicalPacket(io.r))
  && (io.LIoOpSend? ==> ValidPhysicalPacket(io.s))
}

predicate ValidPhysicalEnvironmentStep(step:LEnvStep<EndPoint, seq<byte>>)
{
  step.LEnvStepHostIos? ==> forall io{:trigger io in step.ios}{:trigger ValidPhysicalIo(io)} :: io in step.ios ==> ValidPhysicalIo(io)
}

/////////////////////////////////////////
// DS_State
/////////////////////////////////////////

datatype DS_State = DS_State(
  config:H_s.ConcreteConfiguration,
  environment:LEnvironment<EndPoint,seq<byte>>,
  servers:map<EndPoint,H_s.HostState>,
  clients:set<EndPoint>
  )

predicate DS_Init(s:DS_State, config:H_s.ConcreteConfiguration)
  reads *
{
  && s.config == config
  && H_s.ConcreteConfigInit(s.config, mapdomain(s.servers), s.clients)
  && LEnvironment_Init(s.environment)
  && (forall id :: id in s.servers ==> H_s.HostInit(s.servers[id], config, id))
}
  
predicate DS_NextOneServer(s:DS_State, s':DS_State, id:EndPoint, ios:seq<LIoOp<EndPoint,seq<byte>>>)
  requires id in s.servers
  reads *
{
  && id in s'.servers
  && H_s.HostNext(s.servers[id], s'.servers[id], ios)
  && s'.servers == s.servers[id := s'.servers[id]]
}

predicate DS_Next(s:DS_State, s':DS_State)
  reads *
{
  && s'.config == s.config
  && s'.clients == s.clients
  && LEnvironment_Next(s.environment, s'.environment)
  && ValidPhysicalEnvironmentStep(s.environment.nextStep)
  && if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers then
      DS_NextOneServer(s, s', s.environment.nextStep.actor, s.environment.nextStep.ios)
    else
      s'.servers == s.servers
}

//    /////////////////////////////////////////////////////////////////////
//    // Relationship with the abstract service's state machine
//    function DS_AbstractState(s:DS_State) : SpecState
//    function DS_AbstractConfig(s:ConcreteConfiguration) : SpecConfiguration
//
//    predicate IsAbstractStateAbstractionSequenceOf(s:seq<SpecState>, start:SpecState, end:SpecState)
//    {
//      && |s| > 0
//      && s[0] == start
//      && s[|s|-1] == end
//      && (forall i :: 0 <= i < |s|-1 ==> Spec_Next(s[i], s[i+1]))
//    }

}

