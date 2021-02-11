include "RealTime.i.dfy"
include "RoundRobin.i.dfy"
include "../CommonProof/Environment.i.dfy"
include "../CommonProof/Actions.i.dfy"
include "../../../Common/Logic/Temporal/Heuristics.i.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"
include "../../../Common/Logic/Temporal/Time.i.dfy"
include "../../../Common/Logic/Temporal/LeadsTo.i.dfy"
include "../../../Common/Framework/EnvironmentSynchronyLemmas.i.dfy"
include "../../../../Libraries/Math/mul.i.dfy"
include "../../../../Libraries/Math/mul_auto.i.dfy"

module LivenessProof__PacketHandling_i {
import opened LiveRSL__Configuration_i
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Replica_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Environment_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__RoundRobin_i
import opened LivenessProof__RealTime_i
import opened CommonProof__Actions_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Environment_i
import opened Temporal__Heuristics_i
import opened Temporal__Rules_i
import opened Temporal__Time_i
import opened Temporal__LeadsTo_i
import opened Liveness__EnvironmentSynchronyLemmas_i
import opened Liveness__HostQueueLemmas_i
import opened Math__mul_i
import opened Math__mul_auto_i
import opened Math__mul_nonlinear_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Collections__Maps2_s
import opened Collections__Maps2_i
import opened Environment_s
import opened EnvironmentSynchrony_s
import opened Concrete_NodeIdentity_i

predicate AllPacketsProcessedWithin(
  b:Behavior<RslState>,
  i:int,
  processing_period:int,
  sources:set<NodeIdentity>,
  destinations:set<NodeIdentity>
  )
  requires imaptotal(b)
{
  forall p {:trigger PacketSentBetweenHosts(b[i].environment, p, sources, destinations)} ::
      PacketSentBetweenHosts(b[i].environment, p, sources, destinations) ==>
      sat(i, eventuallynextwithin(PacketProcessedTemporal(b, p), processing_period, PaxosTimeMap(b)))
}

function{:opaque} AllPacketsProcessedWithinTemporal(
  b:Behavior<RslState>,
  processing_period:int,
  sources:set<NodeIdentity>,
  destinations:set<NodeIdentity>
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, AllPacketsProcessedWithinTemporal(b, processing_period, sources, destinations))} ::
             sat(i, AllPacketsProcessedWithinTemporal(b, processing_period, sources, destinations)) <==>
             AllPacketsProcessedWithin(b, i, processing_period, sources, destinations)
{
  stepmap(imap i :: AllPacketsProcessedWithin(b, i, processing_period, sources, destinations))
}


lemma lemma_LReplicaNextProcessPacketOnlyReceivesOnePacket(
  s:LReplica,
  s':LReplica,
  p:RslPacket,
  ios:seq<RslIo>
  )
  requires LReplicaNextProcessPacket(s, s', ios)
  requires LIoOpReceive(p) in ios
  ensures  ios[0] == LIoOpReceive(p)
{
  Lemma_IfOpSeqIsCompatibleWithReductionAndFirstIsntReceiveThenNoneAreReceives(ios);
  assert ios[0].LIoOpReceive?;

  forall i | 0 < i < |ios|
    ensures !ios[i].LIoOpReceive?
  {
    if ios[0].r.msg.RslMessage_Heartbeat?
    {
      if i == 1
      {
        assert ios[i].LIoOpReadClock?;
      }
      else
      {
        assert ios[i] in ios[2..];
        assert ios[i].LIoOpSend?;
      }
    }
    else
    {
      assert ios[i] in ios[1..];
      assert ios[i].LIoOpSend?;
    }
  }
  assert ios[0] == LIoOpReceive(p);
}


lemma lemma_PacketReceiveCausesPacketProcessing(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  p:RslPacket,
  i:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires p.dst in asp.c.config.replica_ids
  requires sat(i, PacketReceivedTemporal(RestrictBehaviorToEnvironment(b), p))
  ensures  PacketProcessedDuringAction(b[i], p)
{
  var eb := RestrictBehaviorToEnvironment(b);
  var ps := b[i];
  var ps' := b[i+1];

  lemma_AssumptionsMakeValidTransition(b, asp.c, i);
  lemma_HostQueuesNext(b, asp, i);
  lemma_ConstantsAllConsistent(b, asp.c, i);

  assert sat(i, PacketReceivedTemporal(eb, p));
  assert PacketReceivedDuringAction(ps.environment, p);
  var ios := ps.environment.nextStep.ios;
  var io := LIoOpReceive(p);
  assert io in ios;
  assert IsValidLIoOp(io, p.dst, ps.environment);

  Lemma_ReceiveMakesHostQueueSmaller(ps.environment.hostInfo[p.dst].queue, ps'.environment.hostInfo[p.dst].queue, ios, p);
  assert ps'.environment.hostInfo[p.dst].queue != ps.environment.hostInfo[p.dst].queue;

  if (exists idx, ios' :: RslNextOneReplica(ps, ps', idx, ios'))
  {
    var idx, ios' :| RslNextOneReplica(ps, ps', idx, ios');
    Lemma_ReceiveRemovesPacketFromHostQueue(ps.environment.hostInfo[p.dst].queue, ps'.environment.hostInfo[p.dst].queue, ios, p);
    Lemma_RemovePacketFromHostQueueImpliesReceive(ps.environment.hostInfo[p.dst].queue, ps'.environment.hostInfo[p.dst].queue, ios', p);
    assert io in ios';
    lemma_LReplicaNextProcessPacketOnlyReceivesOnePacket(ps.replicas[idx].replica, ps'.replicas[idx].replica, p, ios');
    assert PacketProcessedViaIos(b[i], b[i+1], p, idx, ios');
  }
  else if (exists eid, ios' :: RslNextOneExternal(ps, ps', eid, ios'))
  {
    var eid, ios' :| RslNextOneExternal(ps, ps', eid, ios');
    assert eid !in ps.constants.config.replica_ids;
    assert p.dst != eid;
    assert HostQueue_PerformIos(ps.environment.hostInfo[p.dst].queue, ps'.environment.hostInfo[p.dst].queue, []);
    assert ps'.environment.hostInfo[p.dst] == ps.environment.hostInfo[p.dst];
    assert false;
  }
  else
  {
    assert false;
  }
}


lemma lemma_IfPacketsSynchronousForHostsThenSynchronousForFewerHosts<IdType, MessageType>(
  b:Behavior<LEnvironment<IdType, MessageType>>,
  sync_start:int,
  latency_bound:int,
  sources:set<IdType>,
  destinations:set<IdType>,
  sources':set<IdType>,
  destinations':set<IdType>
  )
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires NetworkSynchronousForHosts(b, sync_start, latency_bound, sources, destinations)
  requires 0 <= sync_start
  requires sources' <= sources
  requires destinations' <= destinations
  ensures  NetworkSynchronousForHosts(b, sync_start, latency_bound, sources', destinations')
{
  forall i | sync_start <= i
    ensures sat(i, PacketsSynchronousForHostsTemporal(b, latency_bound, sources', destinations'))
  {
    forall p | PacketSentBetweenHosts(b[i], p, sources', destinations')
      ensures sat(i, next(eventuallynextwithin(PacketDeliveredTemporal(b, p), latency_bound, BehaviorToTimeMap(b))))
    {
      assert PacketSentBetweenHosts(b[i], p, sources, destinations);
      TemporalDeduceFromAlways(sync_start, i, PacketsSynchronousForHostsTemporal(b, latency_bound, sources, destinations));
      lemma_PacketSentAppearsInSentPacketsEnvironment(b, i, p);
    }
  }
  TemporalAlways(sync_start, PacketsSynchronousForHostsTemporal(b, latency_bound, sources', destinations'));
}

lemma lemma_AllPacketsReceivedInTime(
  b:Behavior<RslState>,
  asp:AssumptionParameters
  ) returns (
  processing_sync_start:int,
  processing_bound:int
  )
  requires LivenessAssumptions(b, asp)
  ensures  asp.synchrony_start <= processing_sync_start
  ensures  processing_bound == asp.latency_bound + asp.burst_size * TimeToPerformGenericAction(asp)
  ensures  var eb := RestrictBehaviorToEnvironment(b);
           var sources := SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids) + {asp.persistent_request.client};
           var destinations := SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids);
           sat(processing_sync_start, always(AllPacketsReceivedWithinTemporal(eb, processing_bound, sources, destinations)))
{
  var eb := RestrictBehaviorToEnvironment(b);
  var sources := SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids) + {asp.persistent_request.client};
  var destinations := SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids);
  var receive_period := TimeToPerformGenericAction(asp);
  var burst_period := asp.burst_size * TimeToPerformGenericAction(asp) + 1;
  var real_time_fun := PaxosTimeMap(b);

  lemma_mul_is_associative(asp.burst_size, asp.host_period, LReplicaNumActions());
    
  forall i {:trigger real_time_fun[i]} {:trigger BehaviorToTimeMap(eb)[i]}
    ensures real_time_fun[i] == BehaviorToTimeMap(eb)[i]
  {
  }
  assert real_time_fun == BehaviorToTimeMap(eb);

  lemma_AssumptionsMakeValidEnvironmentBehavior(b, asp.c);
  assert LEnvironment_BehaviorSatisfiesSpec(eb);

  assert NetworkSynchronousForHosts(eb, asp.synchrony_start, asp.latency_bound, sources, sources);
  lemma_IfPacketsSynchronousForHostsThenSynchronousForFewerHosts(eb, asp.synchrony_start, asp.latency_bound, sources,
                                                                 sources, sources, destinations);
  assert NetworkSynchronousForHosts(eb, asp.synchrony_start, asp.latency_bound, sources, destinations);
  assert sat(asp.synchrony_start, always(PacketsSynchronousForHostsTemporal(eb, asp.latency_bound, sources, destinations)));
  TemporalEventually(0, asp.synchrony_start, always(PacketsSynchronousForHostsTemporal(eb, asp.latency_bound, sources, destinations)));

  forall host | host in destinations
    ensures sat(0, eventual(always(NetworkDeliveryRateForHostBoundedTemporal(eb, asp.burst_size, burst_period, host))))
  {
    var replica_index :| replica_index in asp.live_quorum && host == asp.c.config.replica_ids[replica_index];
    assert sat(asp.synchrony_start, always(NetworkDeliveryRateForHostBoundedTemporal(eb, asp.burst_size, burst_period, host)));
    TemporalEventually(0, asp.synchrony_start, always(NetworkDeliveryRateForHostBoundedTemporal(eb, asp.burst_size, burst_period, host)));
  }
    
  lemma_mul_is_associative(asp.burst_size, asp.host_period, LReplicaNumActions());
  assert forall host :: host in destinations ==> sat(0, eventual(always(NetworkDeliveryRateForHostBoundedTemporal(eb, asp.burst_size, asp.burst_size * receive_period + 1, host))));

  forall host | host in destinations
    ensures sat(asp.synchrony_start, always(eventuallynextwithin(ReceiveAttemptedTemporal(eb, host), receive_period, real_time_fun)))
  {
    var replica_index :| replica_index in asp.live_quorum && host == asp.c.config.replica_ids[replica_index];
    lemma_ReplicaNextPerformsProcessPacketPeriodically(b, asp, replica_index);
  }

  forall ensures 1 <= receive_period { lemma_mul_inequality_forall(); lemma_mul_auto(); }
  forall i, j | 0 <= i <= j ensures b[i].environment.time <= b[j].environment.time { lemma_TimeAdvancesBetween(b, asp, i, j); }
  processing_sync_start, processing_bound := Lemma_EventuallyAllPacketsAlwaysReceivedInTime(asp.synchrony_start, asp.latency_bound, sources, destinations, eb, asp.burst_size, receive_period);
}

predicate PacketProcessingSynchronousOneStep(
  b:Behavior<RslState>,
  i:int,
  processing_bound:int,
  sources:set<NodeIdentity>,
  destinations:set<NodeIdentity>
  )
  requires imaptotal(b)
{
  forall p {:trigger PacketSentDuringAction(b[i], p)} ::
      PacketSentDuringAction(b[i], p) && p.src in sources && p.dst in destinations
      ==> sat(i, next(eventuallynextwithin(PacketProcessedTemporal(b, p), processing_bound, PaxosTimeMap(b))))
}

function{:opaque} PacketProcessingSynchronousTemporal(
  b:Behavior<RslState>,
  processing_bound:int,
  sources:set<NodeIdentity>,
  destinations:set<NodeIdentity>
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, PacketProcessingSynchronousTemporal(b, processing_bound, sources, destinations))} ::
             sat(i, PacketProcessingSynchronousTemporal(b, processing_bound, sources, destinations)) <==>
             PacketProcessingSynchronousOneStep(b, i, processing_bound, sources, destinations)
{
  stepmap(imap i :: PacketProcessingSynchronousOneStep(b, i, processing_bound, sources, destinations))
}

predicate PacketProcessingSynchronous(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  start_step:int,
  processing_bound:int
  )
  requires LivenessAssumptions(b, asp)
{
  var sources := SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids) + {asp.persistent_request.client};
  var destinations := SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids);
  && asp.synchrony_start <= start_step
  && processing_bound >= 0
  && sat(start_step, always(PacketProcessingSynchronousTemporal(b, processing_bound, sources, destinations)))
}


lemma lemma_EventuallyPacketProcessingSynchronous(
  b:Behavior<RslState>,
  asp:AssumptionParameters
  ) returns (
  processing_sync_start:int,
  processing_bound:int
  )
  requires LivenessAssumptions(b, asp)
  ensures  PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
{
  TemporalAssist();

  var eb := RestrictBehaviorToEnvironment(b);
  var f := PaxosTimeMap(b);
  var sources := SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids) + {asp.persistent_request.client};
  var destinations := SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids);
  var receive_period := TimeToPerformGenericAction(asp);

  processing_sync_start, processing_bound := lemma_AllPacketsReceivedInTime(b, asp);

  forall i | processing_sync_start <= i
    ensures sat(i, PacketProcessingSynchronousTemporal(b, processing_bound, sources, destinations))
  {
    forall p{:trigger PacketSentDuringAction(b[i], p)} | PacketSentDuringAction(b[i], p) && p.src in sources && p.dst in destinations
      ensures sat(i+1, eventuallynextwithin(PacketProcessedTemporal(b, p), processing_bound, f))
    {
      TemporalDeduceFromAlways(processing_sync_start, i, AllPacketsReceivedWithinTemporal(eb, processing_bound, sources, destinations));
      assert PacketSentBetweenHosts(eb[i], p, sources, destinations); // TRIGGER
      assert sat(i, AllPacketsReceivedWithinTemporal(eb, processing_bound, sources, destinations));
      assert AllPacketsReceivedWithin(eb, i, processing_bound, sources, destinations);
      assert sat(i, next(eventuallynextwithin(PacketReceivedTemporal(eb, p), processing_bound, f)));
      var j := TemporalDeduceFromEventual(i+1, nextbefore(PacketReceivedTemporal(eb, p), f[i+1] + processing_bound, f));
      assert sat(j, PacketReceivedTemporal(eb, p));
      lemma_PacketReceiveCausesPacketProcessing(b, asp, p, j);
      assert sat(j, imply(PacketReceivedTemporal(eb, p), PacketProcessedTemporal(b, p)));
      assert sat(j, PacketProcessedTemporal(b, p));
      TemporalEventually(i+1, j, nextbefore(PacketProcessedTemporal(b, p), f[i+1] + processing_bound, f));
    }
  }
  TemporalAlways(processing_sync_start, PacketProcessingSynchronousTemporal(b, processing_bound, sources, destinations));
  lemma_mul_nonnegative(asp.burst_size, receive_period);
}

lemma lemma_IfPacketProcessingSynchronousThenAlways(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  start_step:int,
  later_step:int,
  processing_bound:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, start_step, processing_bound)
  requires start_step <= later_step
  ensures  PacketProcessingSynchronous(b, asp, later_step, processing_bound)
{
  var sources := SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids) + {asp.persistent_request.client};
  var destinations := SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids);
  Lemma_AlwaysImpliesLaterAlways(start_step, later_step, PacketProcessingSynchronousTemporal(b, processing_bound, sources, destinations));
}

lemma lemma_SchedulerActionThatReceivesReceivesFirst(
  s:LScheduler,
  s':LScheduler,
  p:RslPacket,
  ios:seq<RslIo>
  )
  requires LIoOpReceive(p) in ios
  requires LSchedulerNext(s, s', ios)
  ensures  LIoOpReceive(p) == ios[0]
{
  if LReplicaNextProcessPacket(s.replica, s'.replica, ios)
  {
    assert ios[0].LIoOpReceive?;
    if ios[0].r.msg.RslMessage_Heartbeat?
    {
      assert ios[1].LIoOpReadClock?;
      assert forall i :: 1 < i < |ios| ==> ios[i].LIoOpSend?;
      assert LIoOpReceive(p) == ios[0];
    }
    else
    {
      assert LReplicaNextProcessPacketWithoutReadingClock(s.replica, s'.replica, ios);
      assert ios[0].LIoOpReceive?;
      assert forall i :: 0 < i < |ios| ==> ios[i].LIoOpSend?;
      assert LIoOpReceive(p) == ios[0];
    }
  }
}

lemma lemma_PacketSentToIndexProcessedByIt(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  send_step:int,
  idx:int,
  p:RslPacket
  ) returns (
  processing_step:int,
  ios:seq<RslIo>
  )
  requires LivenessAssumptions(b, asp)
  requires idx in asp.live_quorum
  requires PacketSentDuringAction(b[send_step], p)
  requires p.src in SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids) + { asp.persistent_request.client }
  requires p.dst == asp.c.config.replica_ids[idx]
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires processing_sync_start <= send_step
  ensures  send_step+1 <= processing_step
  ensures  PacketProcessedViaIos(b[processing_step], b[processing_step+1], p, idx, ios)
  ensures  b[processing_step+1].environment.time <= b[send_step+1].environment.time + processing_bound
{
  TemporalAssist();

  var timefun := PaxosTimeMap(b);

  assert TLe(processing_sync_start, send_step);
  processing_step :| && TLe(send_step+1, processing_step)
                     && sat(processing_step, PacketProcessedTemporal(b, p))
                     && timefun[processing_step+1] <= timefun[send_step+1] + processing_bound;

  lemma_ConstantsAllConsistent(b, asp.c, processing_step);
  lemma_ConstantsAllConsistent(b, asp.c, processing_step+1);
  lemma_AssumptionsMakeValidTransition(b, asp.c, processing_step);
                       
  assert b[processing_step].environment.nextStep.LEnvStepHostIos?;
  ios := b[processing_step].environment.nextStep.ios;
  var actor := b[processing_step].environment.nextStep.actor;
  assert p.dst == actor;
  assert RslNext(b[processing_step], b[processing_step+1]);
  if exists idx', ios' {:trigger RslNextOneReplica(b[processing_step], b[processing_step+1], idx', ios')} ::
                  RslNextOneReplica(b[processing_step], b[processing_step+1], idx', ios')
  {
    var idx', ios' :| RslNextOneReplica(b[processing_step], b[processing_step+1], idx', ios');
    assert ReplicasDistinct(asp.c.config.replica_ids, idx, idx');
    assert idx' == idx && ios' == ios;
    assert LSchedulerNext(b[processing_step].replicas[idx], b[processing_step+1].replicas[idx], ios);
    assert LIoOpReceive(p) in ios;
    lemma_SchedulerActionThatReceivesReceivesFirst(b[processing_step].replicas[idx], b[processing_step+1].replicas[idx], p, ios);
    assert PacketProcessedViaIos(b[processing_step], b[processing_step+1], p, idx, ios);
  }
  else if exists eid, ios' {:trigger RslNextOneExternal(b[processing_step], b[processing_step+1], eid, ios')} ::
                      RslNextOneExternal(b[processing_step], b[processing_step+1], eid, ios')
  {
    var eid, ios' :| RslNextOneExternal(b[processing_step], b[processing_step+1], eid, ios');
    assert false;
  }
  else
  {
    assert false;
  }
}

} 
