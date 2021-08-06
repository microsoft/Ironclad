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

predicate ConcreteConfigInit(config:ConcreteConfiguration)
function ConcreteConfigToServers(config:ConcreteConfiguration) : set<EndPoint>

predicate HostStateInvariants(host_state:HostState, env:HostEnvironment)
  reads *

function ParseCommandLineConfiguration(args:seq<seq<byte>>) : ConcreteConfiguration

predicate ArbitraryObject(o:object) { true }

method HostInitImpl(ghost env:HostEnvironment, netc:NetClient, args:seq<seq<byte>>) returns (
  ok:bool,
  host_state:HostState
  )
  requires env.Valid()
  requires env.ok.ok()
  requires netc.IsOpen()
  requires netc.env == env
  requires ValidPhysicalAddress(EndPoint(netc.MyPublicKey()))
  modifies set x:object | ArbitraryObject(x)     // Everything!
  ensures  ok ==> env.Valid() && env.ok.ok()
  ensures  ok ==> HostStateInvariants(host_state, env)
  ensures  ok ==> var id := EndPoint(netc.MyPublicKey());
                 var config := ParseCommandLineConfiguration(args);
                 && id in ConcreteConfigToServers(config)
                 && ConcreteConfigInit(config)
                 && HostInit(host_state, config, id)
  ensures  env.net.history() == old(env.net.history()) // Prohibit HostInitImpl from sending (and receiving) packets


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
  ensures  ok ==> HostStateInvariants(host_state', env)
  ensures  ok ==> HostNext(host_state, host_state', ios)
  // Connect the low-level IO events to the spec-level IO events
  ensures  ok ==> recvs + clocks + sends == ios
  // These obligations enable us to apply reduction
  // Even when !ok, if sent is non-empty, we need to return valid set of sent packets too
  ensures  (ok || |sends| > 0) ==> env.net.history() == old(env.net.history()) + (recvs + clocks + sends)
  ensures  forall e :: && (e in recvs ==> e.LIoOpReceive?) 
                 && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) 
                 && (e in sends ==> e.LIoOpSend?)
  ensures  |clocks| <= 1

}
