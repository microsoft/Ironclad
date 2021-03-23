include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "../CommonProof/Constants.i.dfy"
include "../CommonProof/Environment.i.dfy"
include "../../../Common/Logic/Temporal/Heuristics.i.dfy"
include "../../../Common/Logic/Temporal/Induction.i.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"
include "../../../Common/Logic/Temporal/Time.i.dfy"

module LivenessProof__Environment_i {
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Environment_i
import opened Temporal__Temporal_s
import opened Temporal__Heuristics_i
import opened Temporal__Induction_i
import opened Temporal__Rules_i
import opened Temporal__Time_s
import opened Temporal__Time_i
import opened Environment_s
import opened EnvironmentSynchrony_s

lemma lemma_AssumptionsMakeValidEnvironmentBehavior(
  b:Behavior<RslState>,
  c:LConstants
  )
  requires IsValidBehavior(b, c)
  ensures  LEnvironment_BehaviorSatisfiesSpec(RestrictBehaviorToEnvironment(b))
{
  var eb := RestrictBehaviorToEnvironment(b);
  var x := EnvironmentNextTemporal(eb);

  forall i | i >= 0
    ensures sat(i, x)
  {
    assert RslNext(b[i], b[i+1]);
    assert LEnvironment_Next(eb[i], eb[i+1]);
  }

  TemporalAlways(0, x);
  assert LEnvironment_Init(eb[0]);
  assert LEnvironment_BehaviorSatisfiesSpec(eb);
}

lemma lemma_ClockAmbiguityLimitApplies(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int,
  io:RslIo
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires idx in asp.live_quorum
  requires 0 <= idx < |asp.c.config.replica_ids|
  requires b[i].environment.nextStep.LEnvStepHostIos?
  requires b[i].environment.nextStep.actor == asp.c.config.replica_ids[idx]
  requires io in b[i].environment.nextStep.ios
  requires io.LIoOpReadClock?
  ensures  b[i].environment.time - asp.max_clock_ambiguity <= io.t <= b[i].environment.time + asp.max_clock_ambiguity
  ensures  b[i].environment.time == b[i+1].environment.time
{
  var live_hosts := SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids);
  TemporalDeduceFromAlways(0, i, ClockAmbiguityLimitedForHostsTemporal(RestrictBehaviorToEnvironment(b), asp.max_clock_ambiguity,
                                                                       live_hosts));
  lemma_AssumptionsMakeValidTransition(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i);
}

lemma lemma_PacketSentAppearsInSentPackets(
  b:Behavior<RslState>,
  c:LConstants,
  send_step:int,
  p:RslPacket
  )
  requires IsValidBehavior(b, c)
  requires b[send_step].environment.nextStep.LEnvStepHostIos?
  requires LIoOpSend(p) in b[send_step].environment.nextStep.ios
  requires send_step >= 0
  ensures  p in b[send_step + 1].environment.sentPackets
{
  assert RslNext(b[send_step], b[send_step + 1]);
}

lemma lemma_PacketSentAppearsInSentPacketsEnvironment<IdType, MessageType>(
  b:Behavior<LEnvironment<IdType, MessageType>>,
  send_step:int,
  p:LPacket<IdType, MessageType>
  )
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires b[send_step].nextStep.LEnvStepHostIos?
  requires LIoOpSend(p) in b[send_step].nextStep.ios
  requires send_step >= 0
  ensures  p in b[send_step + 1].sentPackets
{
  TemporalDeduceFromAlways(0, send_step, EnvironmentNextTemporal(b));
}

lemma lemma_PacketSentEventuallyDelivered(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  send_step:int,
  p:RslPacket
  ) returns (
  delivery_step:int
  )
  requires LivenessAssumptions(b, asp)
  requires asp.synchrony_start <= send_step
  requires var hosts := SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids) + { asp.persistent_request.client };
           PacketSentBetweenHosts(b[send_step].environment, p, hosts, hosts)
  ensures  send_step <= delivery_step
  ensures  b[delivery_step].environment.nextStep == LEnvStepDeliverPacket(p)
  ensures  b[delivery_step+1].environment.time <= b[send_step+1].environment.time + asp.latency_bound
{
  var eb := RestrictBehaviorToEnvironment(b);
  var hosts := SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids) + { asp.persistent_request.client };
  assert NetworkSynchronousForHosts(eb, asp.synchrony_start, asp.latency_bound, hosts, hosts);
  TemporalDeduceFromAlways(asp.synchrony_start, send_step, PacketsSynchronousForHostsTemporal(eb, asp.latency_bound, hosts, hosts));
  assert PacketSentBetweenHosts(eb[send_step], p, hosts, hosts); // TRIGGER
  lemma_PacketSentAppearsInSentPackets(b, asp.c, send_step, p);
  assert p in eb[send_step + 1].sentPackets;
  assert sat(send_step, next(eventuallynextwithin(PacketDeliveredTemporal(eb, p), asp.latency_bound, BehaviorToTimeMap(eb))));
  assert sat(send_step+1, eventuallynextwithin(PacketDeliveredTemporal(eb, p), asp.latency_bound, BehaviorToTimeMap(eb)));
  delivery_step := TemporalDeduceFromEventuallyNextWithin(send_step+1, PacketDeliveredTemporal(eb, p), asp.latency_bound,
                                                          BehaviorToTimeMap(eb));
}

} 
