include "../../Common/Framework/Host.s.dfy"
include "ReplicaImplMain.i.dfy"
include "CmdLineParser.i.dfy"
include "Unsendable.i.dfy"

module Host_i refines Host_s {

import opened LiveRSL__Configuration_i
import opened LiveRSL__ConstantsState_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__Environment_i
import opened LiveRSL__ParametersState_i
import opened LiveRSL__QRelations_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ReplicaConstantsState_i
import opened LiveRSL__ReplicaImplClass_i
import opened LiveRSL__ReplicaImplMain_i
import opened LiveRSL__NetRSL_i
import opened LiveRSL__Unsendable_i
import opened CmdLineParser_i
import opened PaxosCmdLineParser_i 
import opened Collections__Sets_i
import opened Common__NodeIdentity_i
import opened Common__SeqIsUnique_i
import opened Common__SeqIsUniqueDef_i

datatype CScheduler = CScheduler(ghost sched:LScheduler, replica_impl:ReplicaImpl)

type HostState = CScheduler
type ConcreteConfiguration = ConstantsState

predicate ConcreteConfigInit(config:ConcreteConfiguration) 
{
  ConstantsStateIsValid(config)
}

function ConcreteConfigToServers(config:ConcreteConfiguration) : set<EndPoint>
{
  MapSeqToSet(config.config.replica_ids, x=>x)
}

predicate HostStateInvariants(host_state:HostState, env:HostEnvironment)
{
  && host_state.replica_impl.Valid() 
  && host_state.replica_impl.Env() == env
  && host_state.sched == host_state.replica_impl.AbstractifyToLScheduler()
}

predicate HostInit(host_state:HostState, config:ConcreteConfiguration, id:EndPoint)
{
  && host_state.replica_impl.Valid()
  && host_state.replica_impl.replica.constants.all == config
  && config.config.replica_ids[host_state.replica_impl.replica.constants.my_index] == id
  && LSchedulerInit(host_state.sched, 
                   AbstractifyReplicaConstantsStateToLReplicaConstants(host_state.replica_impl.replica.constants))
}

predicate HostNext(host_state:HostState, host_state':HostState, ios:seq<LIoOp<EndPoint, seq<byte>>>)
{
  && NetEventLogIsAbstractable(ios)
  && OnlySentMarshallableData(ios)
  && (|| LSchedulerNext(host_state.sched, host_state'.sched, AbstractifyRawLogToIos(ios))
     || HostNextIgnoreUnsendable(host_state.sched, host_state'.sched, ios))
}

function ParseCommandLineConfiguration(args:seq<seq<byte>>) : ConcreteConfiguration
{
  var paxos_config := paxos_config_parsing(args);
  var params := StaticParams();
  ConstantsState(paxos_config, params)
}

method {:timeLimitMultiplier 4} HostInitImpl(
  ghost env:HostEnvironment,
  netc:NetClient,
  args:seq<seq<byte>>
  ) returns (
  ok:bool,
  host_state:HostState
  )
{
  var pconfig:CPaxosConfiguration, my_index;
  var id := EndPoint(netc.MyPublicKey());
  ok, pconfig, my_index := parse_cmd_line(id, args);

  var lschedule:LScheduler;
  var repImpl:ReplicaImpl := new ReplicaImpl(); 
  host_state := CScheduler(lschedule,repImpl);

  if !ok { return; }
  assert id == pconfig.replica_ids[my_index];

  var scheduler := new ReplicaImpl();
  var constants := InitReplicaConstantsState(id, pconfig); //SystemConfiguration(me_ep);
  assert constants.all.config == pconfig;
  assert constants.all.config.replica_ids[constants.my_index] == id;
  calc {
    constants.my_index as int;
      { reveal SeqIsUnique(); }
    my_index as int;
  }

  assert env.Valid() && env.ok.ok();
  assert ReplicaConstantsState_IsValid(constants);
  assert WellFormedLConfiguration(AbstractifyReplicaConstantsStateToLReplicaConstants(constants).all.config);

  ok := scheduler.Replica_Init(constants, netc, env);
  if !ok { return; }
  host_state := CScheduler(scheduler.AbstractifyToLScheduler(), scheduler);
}

predicate EventsConsistent(recvs:seq<NetEvent>, clocks:seq<NetEvent>, sends:seq<NetEvent>) 
{
  forall e :: && (e in recvs  ==> e.LIoOpReceive?) 
        && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) 
        && (e in sends  ==> e.LIoOpSend?)
}

ghost method RemoveRecvs(events:seq<NetEvent>) returns (recvs:seq<NetEvent>, rest:seq<NetEvent>) 
  ensures forall e :: e in recvs ==> e.LIoOpReceive?
  ensures events == recvs + rest
  ensures rest != [] ==> !rest[0].LIoOpReceive?
  ensures NetEventsReductionCompatible(events) ==> NetEventsReductionCompatible(rest);
{
  recvs := [];
  rest := [];

  var i := 0;
  while i < |events| 
    invariant 0 <= i <= |events|
    invariant forall e :: e in recvs ==> e.LIoOpReceive?
    //invariant events == recvs + events[i..]
    invariant recvs == events[0..i]
  {
    if !events[i].LIoOpReceive? {
      rest := events[i..];
      return;
    }
    recvs := recvs + [events[i]];
    i := i + 1;
  }
}

predicate NetEventsReductionCompatible(events:seq<NetEvent>)
{
  forall i :: 0 <= i < |events| - 1 ==> events[i].LIoOpReceive? || events[i+1].LIoOpSend?
}


lemma lemma_RemainingEventsAreSends(events:seq<NetEvent>)
  requires NetEventsReductionCompatible(events)
  requires |events| > 0
  requires !events[0].LIoOpReceive?
  ensures  forall e :: e in events[1..] ==> e.LIoOpSend?
{
  if |events| == 1 {
  } else {
    assert events[1].LIoOpSend?;
    lemma_RemainingEventsAreSends(events[1..]);
  }
}

ghost method PartitionEvents(events:seq<NetEvent>) returns (recvs:seq<NetEvent>, clocks:seq<NetEvent>, sends:seq<NetEvent>)
  requires NetEventsReductionCompatible(events)
  ensures  events == recvs + clocks + sends
  ensures  EventsConsistent(recvs, clocks, sends)
  ensures  |clocks| <= 1
{
  var rest;
  recvs, rest := RemoveRecvs(events);
  assert NetEventsReductionCompatible(rest);
  if |rest| > 0 && (rest[0].LIoOpReadClock? || rest[0].LIoOpTimeoutReceive?) {
    clocks := [rest[0]];
    sends := rest[1..];
    lemma_RemainingEventsAreSends(rest);
  } else {
    clocks := [];
    sends := rest;
    if |rest| > 0 {
      lemma_RemainingEventsAreSends(rest);
    }
  }
}

lemma lemma_ProtocolIosRespectReduction(s:LScheduler, s':LScheduler, ios:seq<RslIo>)
  requires Q_LScheduler_Next(s, s', ios)
  ensures  LIoOpSeqCompatibleWithReduction(ios)
{
  reveal Q_LScheduler_Next();
}

lemma lemma_NetEventsRespectReduction(s:LScheduler, s':LScheduler, ios:seq<RslIo>, events:seq<NetEvent>)
  requires LIoOpSeqCompatibleWithReduction(ios)
  requires RawIoConsistentWithSpecIO(events, ios)
  ensures NetEventsReductionCompatible(events)
{
  forall i | 0 <= i < |events| - 1
    ensures events[i].LIoOpReceive? || events[i+1].LIoOpSend?
  {
    assert LIoOpOrderingOKForAction(ios[i], ios[i+1]);
    reveal AbstractifyRawLogToIos();
    assert AbstractifyRawLogToIos(events)[i] == AbstractifyNetEventToRslIo(events[i]) == ios[i];
  }
}

method {:timeLimitMultiplier 3} HostNextImpl(ghost env:HostEnvironment, host_state:HostState) 
  returns (ok:bool, host_state':HostState, 
           ghost recvs:seq<NetEvent>, ghost clocks:seq<NetEvent>, ghost sends:seq<NetEvent>, 
           ghost ios:seq<LIoOp<EndPoint, seq<byte>>>)
{
  var lschedule:LScheduler;
  var repImpl:ReplicaImpl := new ReplicaImpl(); 
  host_state' := CScheduler(lschedule,repImpl);

  var okay, netEventLog, abstract_ios := Replica_Next_main(host_state.replica_impl);
  if okay {
    calc { 
      Q_LScheduler_Next(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios);
        { reveal Q_LScheduler_Next(); }
      LSchedulerNext(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios);
    }

    assert AbstractifyRawLogToIos(netEventLog) == abstract_ios;
    if LSchedulerNext(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios)
    {
      lemma_ProtocolIosRespectReduction(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios);
    }
    lemma_NetEventsRespectReduction(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios, netEventLog);
    recvs, clocks, sends := PartitionEvents(netEventLog);
    ios := recvs + clocks + sends; //abstract_ios;
    assert ios == netEventLog;
    host_state' := CScheduler(host_state.replica_impl.AbstractifyToLScheduler(), host_state.replica_impl);
  } else {
    recvs := [];
    clocks := [];
    sends := [];
  }
  ok := okay;
  reveal Q_LScheduler_Next();
  assert host_state.replica_impl.Env() == env;
}

}
