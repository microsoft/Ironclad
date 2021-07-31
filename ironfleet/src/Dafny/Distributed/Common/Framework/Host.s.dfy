include "../Native/Io.s.dfy"
include "Environment.s.dfy"

abstract module Host_s {

import opened Native__Io_s
import opened Environment_s 
import opened Native__NativeTypes_s
    
type HostState
type ConcreteConfiguration

predicate HostInit(host_state:HostState, config:ConcreteConfiguration, id:EndPoint)
  reads *
predicate HostNext(host_state:HostState, host_state':HostState, ios:seq<LIoOp<EndPoint, seq<byte>>>)
  reads *
predicate ConcreteConfigInit(config:ConcreteConfiguration, servers:set<EndPoint>, clients:set<EndPoint>)

predicate HostStateInvariants(host_state:HostState, env:HostEnvironment)
  reads *
predicate ConcreteConfigurationInvariants(config:ConcreteConfiguration)

function ParseCommandLineConfiguration(args:seq<seq<byte>>) : (ConcreteConfiguration, set<EndPoint>, set<EndPoint>)

predicate ArbitraryObject(o:object) { true }

// TODO: Prohibit HostInitImpl from sending (and receiving?) packets
method HostInitImpl(ghost env:HostEnvironment) returns (
  ok:bool,
  host_state:HostState,
  config:ConcreteConfiguration,
  ghost servers:set<EndPoint>,
  ghost clients:set<EndPoint>,
  id:EndPoint
  )
  requires env.Valid()
  requires env.ok.ok()
  requires |env.constants.CommandLineArgs()| >= 2
  modifies set x:object | ArbitraryObject(x)     // Everything!
  ensures  ok ==> env.Valid() && env.ok.ok()
  ensures  ok ==> |env.constants.CommandLineArgs()| >= 2
  ensures  ok ==> HostStateInvariants(host_state, env)
  ensures  ok ==> ConcreteConfigurationInvariants(config)
  ensures  ok ==> var args := env.constants.CommandLineArgs();
                  var (parsed_config, parsed_servers, parsed_clients) := ParseCommandLineConfiguration(args[0..|args|-1]);
                  && config == parsed_config
                  && servers == parsed_servers
                  && clients == parsed_clients
                  && ConcreteConfigInit(parsed_config, parsed_servers, parsed_clients)
                  && id == EndPoint(args[|args|-1])
                  && HostInit(host_state, config, id)

method HostNextImpl(ghost env:HostEnvironment, host_state:HostState) 
  returns (
  ok:bool,
  host_state':HostState,
  ghost recvs:seq<NetEvent>,
  ghost clocks:seq<NetEvent>,
  ghost sends:seq<NetEvent>,
  ghost ios:seq<LIoOp<EndPoint, seq<byte>>>
  )
  requires env.Valid() && env.ok.ok()
  requires HostStateInvariants(host_state, env)
  modifies set x:object | ArbitraryObject(x)     // Everything!
  ensures  ok <==> env.Valid() && env.ok.ok()
  // TODO: Even when !ok, if sent is non-empty, we need to return valid set of sent packets too
  ensures  ok ==> HostStateInvariants(host_state', env)
  ensures  ok ==> HostNext(host_state, host_state', ios)
  // Connect the low-level IO events to the spec-level IO events
  ensures  ok ==> recvs + clocks + sends == ios
  // These obligations enable us to apply reduction
  ensures  ok ==> env.net.history() == old(env.net.history()) + (recvs + clocks + sends)
  ensures  forall e :: && (e in recvs ==> e.LIoOpReceive?) 
                 && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) 
                 && (e in sends ==> e.LIoOpSend?)
  ensures  |clocks| <= 1

}

