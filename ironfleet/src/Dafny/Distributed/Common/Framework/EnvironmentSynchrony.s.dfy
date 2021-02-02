include "Environment.s.dfy"
include "../Logic/Temporal/Temporal.s.dfy"
include "../Logic/Temporal/Time.s.dfy"
include "../Collections/Multisets.s.dfy"

module EnvironmentSynchrony_s {
import opened Environment_s
import opened Temporal__Time_s
import opened Collections__Multisets_s

function{:opaque} BehaviorToTimeMap<IdType, MessageType>(
    b:Behavior<LEnvironment<IdType, MessageType>>
    ):imap<int, int>
    requires imaptotal(b);
    ensures  imaptotal(BehaviorToTimeMap(b));
    ensures  forall i {:trigger BehaviorToTimeMap(b)[i]} :: BehaviorToTimeMap(b)[i] == b[i].time;
{
    imap i :: b[i].time
}

///////////////////////////
// HOST QUEUES
///////////////////////////

predicate HostQueue_PerformIos<IdType, MessageType>(
    hostQueue:seq<LPacket<IdType, MessageType>>,
    hostQueue':seq<LPacket<IdType, MessageType>>,
    ios:seq<LIoOp<IdType, MessageType>>
    )
{
    if |ios| == 0 then
        hostQueue' == hostQueue
    else if ios[0].LIoOpReceive? then
        (   |hostQueue| > 0
         && ios[0] == LIoOpReceive(hostQueue[0])
         && HostQueue_PerformIos(hostQueue[1..], hostQueue', ios[1..])
        )
    else if ios[0].LIoOpTimeoutReceive? then
        hostQueue' == hostQueue == []
    else
        hostQueue' == hostQueue
}

predicate HostQueues_Init<IdType, MessageType>(
    e:LEnvironment<IdType, MessageType>
    )
{
       (forall id :: id in e.hostInfo ==> e.hostInfo[id] == LHostInfo([]))
    && e.time >= 0
}

predicate HostQueues_Next<IdType, MessageType>(
    e:LEnvironment<IdType, MessageType>,
    e':LEnvironment<IdType, MessageType>
    )
{
    match e.nextStep
        case LEnvStepHostIos(actor, ios) =>
               actor in e.hostInfo
            && actor in e'.hostInfo
            && e'.hostInfo == e.hostInfo[actor := e'.hostInfo[actor]]
            && LIoOpSeqCompatibleWithReduction(ios)
            && HostQueue_PerformIos(e.hostInfo[actor].queue, e'.hostInfo[actor].queue, ios)

        case LEnvStepDeliverPacket(p) =>
               p in e.sentPackets
            && p.dst in e.hostInfo
            && e'.hostInfo == e.hostInfo[p.dst := LHostInfo(e.hostInfo[p.dst].queue + [p])]

        case LEnvStepAdvanceTime => e'.hostInfo == e.hostInfo
        case LEnvStepStutter => e'.hostInfo == e.hostInfo
}

function{:opaque} HostQueuesNextTemporal<IdType, MessageType>(
    b:Behavior<LEnvironment<IdType, MessageType>>
    ):temporal
    requires imaptotal(b);
    ensures  forall i{:trigger sat(i, HostQueuesNextTemporal(b))} :: sat(i, HostQueuesNextTemporal(b)) == HostQueues_Next(b[i], b[i+1]);
{
    stepmap(imap i :: HostQueues_Next(b[i], b[i+1]))
}

predicate HostQueuesLive<IdType, MessageType>(
    b:Behavior<LEnvironment<IdType, MessageType>>
    )
    requires imaptotal(b);
{
      HostQueues_Init(b[0])
    && sat(0, always(HostQueuesNextTemporal(b)))
}

///////////////////////////
// SYNCHRONOUS NETWORK
///////////////////////////

function{:opaque} PacketDeliveredTemporal<IdType, MessageType>(
    b:Behavior<LEnvironment<IdType, MessageType>>,
    p:LPacket<IdType, MessageType>
    ):temporal
    requires imaptotal(b);
    ensures  forall i {:trigger sat(i, PacketDeliveredTemporal(b, p))} ::
             sat(i, PacketDeliveredTemporal(b, p)) <==> b[i].nextStep == LEnvStepDeliverPacket(p);
{
    stepmap(imap i :: b[i].nextStep == LEnvStepDeliverPacket(p))
}

predicate PacketSentBetweenHosts<IdType, MessageType>(
    e:LEnvironment<IdType, MessageType>,
    p:LPacket<IdType, MessageType>,
    sources:set<IdType>,
    destinations:set<IdType>
    )
{
       e.nextStep.LEnvStepHostIos?
    && LIoOpSend(p) in e.nextStep.ios
    && (p.src in sources || e.nextStep.actor in sources)
    && p.dst in destinations
}

predicate PacketsSynchronousForHosts<IdType, MessageType>(
    b:Behavior<LEnvironment<IdType, MessageType>>,
    i:int,
    latency_bound:int,
    sources:set<IdType>,
    destinations:set<IdType>
    )
    requires imaptotal(b);
{
    forall p {:trigger PacketSentBetweenHosts(b[i], p, sources, destinations)} ::
        p in b[i+1].sentPackets
     && PacketSentBetweenHosts(b[i], p, sources, destinations) ==>
        sat(i, next(eventuallynextwithin(PacketDeliveredTemporal(b, p), latency_bound, BehaviorToTimeMap(b))))
}

function{:opaque} PacketsSynchronousForHostsTemporal<IdType, MessageType>(
    b:Behavior<LEnvironment<IdType, MessageType>>,
    latency_bound:int,
    sources:set<IdType>,
    destinations:set<IdType>
    ):temporal
    requires imaptotal(b);
    ensures  forall i {:trigger sat(i, PacketsSynchronousForHostsTemporal(b, latency_bound, sources, destinations))} ::
        sat(i, PacketsSynchronousForHostsTemporal(b, latency_bound, sources, destinations)) <==>
        PacketsSynchronousForHosts(b, i, latency_bound, sources, destinations);
{
    stepmap(imap i :: PacketsSynchronousForHosts(b, i, latency_bound, sources, destinations))
}

predicate NetworkSynchronousForHosts<IdType, MessageType>(
    b:Behavior<LEnvironment<IdType, MessageType>>,
    start_step:int,
    latency_bound:int,
    sources:set<IdType>,
    destinations:set<IdType>
    )
    requires imaptotal(b);
{
    sat(start_step, always(PacketsSynchronousForHostsTemporal(b, latency_bound, sources, destinations)))
}

///////////////////////////
// TIME NEVER STOPS
///////////////////////////

function{:opaque} TimeReachesTemporal<IdType, MessageType>(
    b:Behavior<LEnvironment<IdType, MessageType>>,
    t:int
    ):temporal
    requires imaptotal(b);
    ensures  forall i {:trigger sat(i, TimeReachesTemporal(b, t))} :: sat(i, TimeReachesTemporal(b, t)) <==> b[i].time >= t;
{
    stepmap(imap i :: b[i].time >= t)
}

predicate NoZenoBehavior<IdType, MessageType>(
    b:Behavior<LEnvironment<IdType, MessageType>>
    )
    requires imaptotal(b);
{
    forall t :: sat(0, eventual(TimeReachesTemporal(b, t)))
}

//////////////////////////////
// CLOCK AMBIGUITY LIMITED
//////////////////////////////

predicate ClockAmbiguityLimitedForHostsInStep<IdType, MessageType>(
    e:LEnvironment,
    max_clock_ambiguity:int,
    hosts:set<IdType>
    )
{
    e.nextStep.LEnvStepHostIos? && e.nextStep.actor in hosts ==>
        (forall io :: io in e.nextStep.ios && io.LIoOpReadClock? ==> e.time - max_clock_ambiguity <= io.t <= e.time + max_clock_ambiguity)
}

function{:opaque} ClockAmbiguityLimitedForHostsTemporal<IdType, MessageType>(
    b:Behavior<LEnvironment<IdType, MessageType>>,
    max_clock_ambiguity:int,
    hosts:set<IdType>
    ):temporal
    requires imaptotal(b);
    ensures  forall i{:trigger sat(i, ClockAmbiguityLimitedForHostsTemporal(b, max_clock_ambiguity, hosts))} ::
             sat(i, ClockAmbiguityLimitedForHostsTemporal(b, max_clock_ambiguity, hosts)) ==
             ClockAmbiguityLimitedForHostsInStep(b[i], max_clock_ambiguity, hosts);
{
    stepmap(imap i :: ClockAmbiguityLimitedForHostsInStep(b[i], max_clock_ambiguity, hosts))
}

predicate ClockAmbiguityLimitedForHosts<IdType, MessageType>(
    b:Behavior<LEnvironment<IdType, MessageType>>,
    start_step:int,
    max_clock_ambiguity:int,
    hosts:set<IdType>
    )
    requires imaptotal(b);
{
    sat(start_step, always(ClockAmbiguityLimitedForHostsTemporal(b, max_clock_ambiguity, hosts)))
}

//////////////////////////////
// RATE-LIMITED HOSTS
//////////////////////////////

function{:opaque} PacketDeliveredToHostTemporal<IdType, MessageType>(b:Behavior<LEnvironment<IdType, MessageType>>, host:IdType):temporal
    requires imaptotal(b);
    ensures  forall i {:trigger sat(i, PacketDeliveredToHostTemporal(b, host))} :: sat(i, PacketDeliveredToHostTemporal(b, host)) <==>
             b[i].nextStep.LEnvStepDeliverPacket? && b[i].nextStep.p.dst == host;
{
    stepmap(imap i :: b[i].nextStep.LEnvStepDeliverPacket? && b[i].nextStep.p.dst == host)
}

function{:opaque} NetworkDeliveryRateForHostBoundedSinceTemporal<IdType, MessageType>(
    b:Behavior<LEnvironment<IdType, MessageType>>,
    i:int,
    burst_size:int,
    host:IdType
    ):temporal
    requires imaptotal(b);
    ensures  forall j{:trigger sat(j, NetworkDeliveryRateForHostBoundedSinceTemporal(b, i, burst_size, host))} ::
        sat(j, NetworkDeliveryRateForHostBoundedSinceTemporal(b, i, burst_size, host)) <==>
        countWithin(i, j, PacketDeliveredToHostTemporal(b, host)) <= burst_size;
{
    stepmap(imap j :: countWithin(i, j, PacketDeliveredToHostTemporal(b, host)) <= burst_size)
}

function{:opaque} NetworkDeliveryRateForHostBoundedTemporal<IdType, MessageType>(
    b:Behavior<LEnvironment<IdType, MessageType>>,
    burst_size:int,
    burst_period:int,
    host:IdType
    ):temporal
    requires imaptotal(b);
    ensures  forall i {:trigger sat(i, NetworkDeliveryRateForHostBoundedTemporal(b, burst_size, burst_period, host))} ::
                 sat(i, NetworkDeliveryRateForHostBoundedTemporal(b, burst_size, burst_period, host)) <==>
                 sat(i, alwayswithin(NetworkDeliveryRateForHostBoundedSinceTemporal(b, i, burst_size, host), burst_period, BehaviorToTimeMap(b)));
{
    stepmap(imap i :: sat(i, alwayswithin(NetworkDeliveryRateForHostBoundedSinceTemporal(b, i, burst_size, host), burst_period, BehaviorToTimeMap(b))))
}

predicate NetworkDeliveryRateBoundedForHosts<IdType, MessageType>(
    b:Behavior<LEnvironment<IdType, MessageType>>,
    start_step:int,
    burst_size:int,
    burst_period:int,
    hosts:set<IdType>
    )
    requires imaptotal(b);
{
    forall host :: host in hosts ==> sat(start_step, always(NetworkDeliveryRateForHostBoundedTemporal(b, burst_size, burst_period, host)))
}

} 
