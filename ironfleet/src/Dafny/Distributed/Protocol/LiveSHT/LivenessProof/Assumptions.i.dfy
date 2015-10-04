include "../RefinementProof/SHT.i.dfy"
include "../../../Common/Framework/EnvironmentSynchrony.s.dfy"
module LivenessProof__Assumptions_i {
import opened LiveSHT__SHT_i
import opened EnvironmentSynchrony_s

///////////////////////
// TYPES
///////////////////////

type LSHTMessage = SingleMessage<Message> 

datatype AssumptionParameters = AssumptionParameters(c:SHTConfiguration)

///////////////////////
// HELPERS
///////////////////////

function{:opaque} RestrictBehaviorToEnvironment(
    b:Behavior<LSHT_State>
    ):Behavior<LEnvironment<NodeIdentity, LSHTMessage>>
    requires imaptotal(b);
    ensures  imaptotal(RestrictBehaviorToEnvironment(b));
    ensures  forall i {:trigger RestrictBehaviorToEnvironment(b)[i]} :: RestrictBehaviorToEnvironment(b)[i] == b[i].environment;
{
    imap i :: b[i].environment
}

predicate IsValidBehaviorPrefix(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int
    )
{
       imaptotal(b)
    && LSHT_Init(c, b[0])
    && (forall j {:trigger LSHT_Next(b[j], b[j+1])} :: 0 <= j < i ==> LSHT_Next(b[j], b[j+1]))
}

predicate IsValidBehavior(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration
    )
{
       imaptotal(b)
    && LSHT_Init(c, b[0])
    && (forall i {:trigger LSHT_Next(b[i], b[i+1])} :: i >= 0 ==> LSHT_Next(b[i], b[i+1]))
}

predicate LSHTHostTakesAction(
    ps:LSHT_State,
    ps':LSHT_State,
    host_index:int
    )
{
       ps.environment.nextStep.LEnvStepHostIos? 
    && 0 <= host_index < |ps.config.hostIds|
    && ps.environment.nextStep.actor == ps.config.hostIds[host_index] 
    && var ios := ps.environment.nextStep.ios;
          LSHT_NextOneHost(ps, ps', host_index, ios)
       && LScheduler_Next(ps.hosts[host_index], ps'.hosts[host_index], ios)
}

function{:opaque} LSHTHostTakesActionTemporal(
    b:Behavior<LSHT_State>,
    host_index:int
    ):temporal
    requires imaptotal(b);
    ensures  forall i {:trigger sat(i, LSHTHostTakesActionTemporal(b, host_index))} ::
                 sat(i, LSHTHostTakesActionTemporal(b, host_index)) <==> LSHTHostTakesAction(b[i], b[i+1], host_index);
{
    stepmap(imap i :: LSHTHostTakesAction(b[i], b[i+1], host_index))
}

function AllShardPacketsSent(packets:set<LSHTPacket>):set<LSHTPacket>
{
    set p | p in packets && p.msg.SingleMessage? && p.msg.m.Shard?
}

///////////////////////
// ASSUMPTIONS
///////////////////////

function{:opaque} PacketSentBetweenHostsTemporal<IdType, MessageType>(
    b:Behavior<LEnvironment<IdType, MessageType>>,
    p:LPacket<IdType, MessageType>,
    sources:set<IdType>,
    destinations:set<IdType>
    ):temporal
    requires imaptotal(b);
    ensures  forall i {:trigger sat(i, PacketSentBetweenHostsTemporal(b, p, sources, destinations))} ::
                 sat(i, PacketSentBetweenHostsTemporal(b, p, sources, destinations)) <==>
                 PacketSentBetweenHosts(b[i], p, sources, destinations);
{
    stepmap(imap i :: PacketSentBetweenHosts(b[i], p, sources, destinations))
}

function SeqToSet<X>(xs:seq<X>) : set<X>
{
    set x | x in xs
}

predicate NetworkWeaklyFair<IdType, MessageType>(
    b:Behavior<LEnvironment<IdType, MessageType>>,
    hosts:seq<IdType>
    )
    requires imaptotal(b);
{
    var host_set := SeqToSet(hosts);
    forall p  :: sat(0, always(imply(always(eventual(PacketSentBetweenHostsTemporal(b, p, host_set, host_set))), 
                                     eventual(PacketDeliveredTemporal(b, p)))))
}

///////////////////////////
// TOP-LEVEL ASSUMPTIONS
///////////////////////////

predicate LivenessAssumptions(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters
    )
{
       IsValidBehavior(b, asp.c)
    && var eb := RestrictBehaviorToEnvironment(b);
       HostQueuesLive(eb)

    // Each host executes its scheduler infinitely often
    && (forall host_index :: 0 <= host_index < |asp.c.hostIds| ==> sat(0, always(eventual(LSHTHostTakesActionTemporal(b, host_index)))))

    // Admin doesn't send too many shard requests
    && (forall step :: 0 <= step ==> |AllShardPacketsSent(b[step].environment.sentPackets)| < asp.c.params.max_delegations - 4)

    // Messages sent infinitely often are delivered infinitely often
    //&& sat(0, always(NetworkWeaklyFairTemporal(eb, asp.c.hostIds)))
    && NetworkWeaklyFair(eb, asp.c.hostIds)
}

} 
