include "../../Common/Native/Io.s.dfy"
include "DistributedSystem.s.dfy"
include "AbstractService.s.dfy"
include "../Collections/Seqs.s.dfy"

abstract module Main_s
{
import opened Native__Io_s
import opened DS_s : DistributedSystem_s
import opened AS_s : AbstractService_s
import opened Collections__Seqs_s

method {:main} Main(ghost env:HostEnvironment)
  requires env.Valid() && env.ok.ok()
  requires env.udp.history() == []
  requires |env.constants.CommandLineArgs()| >= 2
  modifies set x:object | DS_s.H_s.ArbitraryObject(x)     // Everything!
  decreases *
{
  var ok, host_state, config, servers, clients, id := DS_s.H_s.HostInitImpl(env);
  assert ok ==> DS_s.H_s.HostInit(host_state, config, id);

  while (ok) 
    invariant ok ==> DS_s.H_s.HostStateInvariants(host_state, env)
    invariant ok ==> env.Valid() && env.ok.ok()
    decreases *
  {
    ghost var old_udp_history := env.udp.history();
    ghost var old_state := host_state;

    ghost var recvs, clocks, sends, ios;
    ok, host_state, recvs, clocks, sends, ios := DS_s.H_s.HostNextImpl(env, host_state);

    if ok {
      // Correctly executed one action
      assert DS_s.H_s.HostNext(old_state, host_state, ios);

      // Connect the low-level IO events to the spec-level IO events
      assert recvs + clocks + sends == ios;

      // These obligations enable us to apply reduction
      assert env.udp.history() == old_udp_history + recvs + clocks + sends;
      assert forall e :: && (e in recvs ==> e.LIoOpReceive?) 
                   && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) 
                   && (e in sends ==> e.LIoOpSend?);
      assert |clocks| <= 1;
    }
  }
}

lemma RefinementProof(config:DS_s.H_s.ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<ServiceState>)
  requires |db| > 0
  requires DS_Init(db[0], config)
  requires forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1])
  ensures  |db| == |sb|
  ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].servers))
  ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1])
  ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i])

}
