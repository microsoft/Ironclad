include "../DistributedSystem.i.dfy"
include "../CommonProof/Assumptions.i.dfy"
include "../../../Common/Framework/EnvironmentSynchrony.s.dfy"

module LivenessProof__Assumptions_i {
import opened LiveRSL__Configuration_i
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Message_i
import opened LiveRSL__Parameters_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened CommonProof__Assumptions_i
import opened EnvironmentSynchrony_s
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Concrete_NodeIdentity_i
import opened Collections__Maps2_s
import opened Environment_s
import opened Common__UpperBound_s

///////////////////////
// TYPES
///////////////////////

datatype AssumptionParameters = AssumptionParameters(
                                    c:LConstants,
                                    live_quorum:set<int>,
                                    synchrony_start:int,
                                    latency_bound:int,
                                    host_period:int,
                                    burst_size:int,
                                    persistent_request:Request,
                                    persistent_period:int,
                                    max_clock_ambiguity:int
                                    )

///////////////////////
// HELPERS
///////////////////////

function SetOfReplicaIndicesToSetOfHosts(s:set<int>, ids:seq<NodeIdentity>):set<NodeIdentity>
{
  set idx | idx in s && 0 <= idx < |ids| :: ids[idx]
}

predicate RslSchedulerActionOccursForReplica(
  ps:RslState,
  ps':RslState,
  replica_index:int
  )
{
  exists ios {:trigger RslNextOneReplica(ps, ps', replica_index, ios)}
        {:trigger LSchedulerNext(ps.replicas[replica_index], ps'.replicas[replica_index], ios) } ::
    && RslNextOneReplica(ps, ps', replica_index, ios)
    && LSchedulerNext(ps.replicas[replica_index], ps'.replicas[replica_index], ios)
}

function{:opaque} MakeRslActionTemporalFromSchedulerFunction(
  b:Behavior<RslState>,
  replica_index:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, MakeRslActionTemporalFromSchedulerFunction(b, replica_index))} ::
               sat(i, MakeRslActionTemporalFromSchedulerFunction(b, replica_index)) <==>
               RslSchedulerActionOccursForReplica(b[i], b[nextstep(i)], replica_index)
{
  stepmap(imap i :: RslSchedulerActionOccursForReplica(b[i], b[nextstep(i)], replica_index))
}

function{:opaque} PaxosTimeMap(b:Behavior<RslState>):imap<int, int>
  requires imaptotal(b)
  ensures  imaptotal(PaxosTimeMap(b))
  ensures  forall i {:trigger PaxosTimeMap(b)[i]} :: PaxosTimeMap(b)[i] == b[i].environment.time
{
  imap i :: b[i].environment.time
}

predicate ClientSendsRequestToReplica(ps:RslState, request:Request, replica:NodeIdentity)
  requires request.Request?
{
  && ps.environment.nextStep.LEnvStepHostIos?
  && ps.environment.nextStep.actor == request.client
  && LIoOpSend(LPacket(replica, request.client, RslMessage_Request(request.seqno, request.request))) in ps.environment.nextStep.ios
}

function{:opaque} ClientSendsRequestToReplicaTemporal(
  b:Behavior<RslState>,
  request:Request,
  replica:NodeIdentity
  ):temporal
  requires imaptotal(b)
  requires request.Request?
  ensures  forall i {:trigger sat(i, ClientSendsRequestToReplicaTemporal(b, request, replica))} ::
               sat(i, ClientSendsRequestToReplicaTemporal(b, request, replica)) <==>
               ClientSendsRequestToReplica(b[i], request, replica)
{
  stepmap(imap i :: ClientSendsRequestToReplica(b[i], request, replica))
}

predicate ClientNeverSentHigherSequenceNumberRequest(ps:RslState, request:Request)
  requires request.Request?
{
  forall p :: p in ps.environment.sentPackets && p.src == request.client && p.msg.RslMessage_Request? ==>
        p.msg.seqno_req < request.seqno || (p.msg.seqno_req == request.seqno && p.msg.val == request.request)
}

function{:opaque} ClientNeverSentHigherSequenceNumberRequestTemporal(
  b:Behavior<RslState>,
  asp:AssumptionParameters
  ):temporal
  requires imaptotal(b)
  requires asp.persistent_request.Request?
  ensures  forall i {:trigger sat(i, ClientNeverSentHigherSequenceNumberRequestTemporal(b, asp))} ::
               sat(i, ClientNeverSentHigherSequenceNumberRequestTemporal(b, asp)) <==>
               ClientNeverSentHigherSequenceNumberRequest(b[i], asp.persistent_request)
{
  stepmap(imap i :: ClientNeverSentHigherSequenceNumberRequest(b[i], asp.persistent_request))
}

///////////////////////
// ASSUMPTIONS
///////////////////////

predicate HostExecutesPeriodically(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  replica_index:int
  )
  requires imaptotal(b)
{
  var scheduler_action := MakeRslActionTemporalFromSchedulerFunction(b, replica_index);
  sat(asp.synchrony_start, always(eventuallynextwithin(scheduler_action, asp.host_period, PaxosTimeMap(b))))
}

predicate PersistentClientSendsRequestPeriodically(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  replica_index:int
  )
  requires imaptotal(b)
  requires asp.persistent_request.Request?
  requires 0 <= replica_index < |asp.c.config.replica_ids|
{
  var client_send := ClientSendsRequestToReplicaTemporal(b, asp.persistent_request, asp.c.config.replica_ids[replica_index]);
  sat(asp.synchrony_start, always(eventuallynextwithin(client_send, asp.persistent_period, PaxosTimeMap(b))))
}

predicate ReplyDeliveredDuringStep(ps:RslState, req:Request)
{
  && req.Request?
  && ps.environment.nextStep.LEnvStepDeliverPacket?
  && var p := ps.environment.nextStep.p;
    && p.src in ps.constants.config.replica_ids
    && p.dst == req.client
    && p.msg.RslMessage_Reply?
    && p.msg.seqno_reply == req.seqno
}

function{:opaque} ReplyDeliveredTemporal(b:Behavior<RslState>, req:Request):temporal
  requires imaptotal(b)
  ensures forall i {:trigger sat(i, ReplyDeliveredTemporal(b, req))} ::
              sat(i, ReplyDeliveredTemporal(b, req)) <==> ReplyDeliveredDuringStep(b[i], req)
{
  stepmap(imap i :: ReplyDeliveredDuringStep(b[i], req))
}

predicate OverflowProtectionNotUsedForReplica(ps:RslState, replica_index:int, params:LParameters, max_clock_ambiguity:int)
  requires 0 <= replica_index < |ps.replicas|
{
  var s := ps.replicas[replica_index].replica;
  && LtUpperBound(s.proposer.election_state.current_view.seqno, params.max_integer_val)
  && LeqUpperBound(ps.environment.time + max_clock_ambiguity + s.proposer.election_state.epoch_length, params.max_integer_val)
  && LeqUpperBound(s.proposer.election_state.epoch_length + s.proposer.election_state.epoch_length, params.max_integer_val)
  && LeqUpperBound(s.acceptor.log_truncation_point + params.max_log_length, params.max_integer_val)
  && LtUpperBound(s.proposer.next_operation_number_to_propose, params.max_integer_val)
  && LtUpperBound(s.executor.ops_complete, params.max_integer_val)
  && LeqUpperBound(|s.proposer.election_state.requests_received_prev_epochs + s.proposer.election_state.requests_received_this_epoch|,
                  params.max_integer_val)
  && LtUpperBound(|s.proposer.election_state.requests_received_this_epoch|, params.max_integer_val)
}

predicate OverflowProtectionNotUsed(ps:RslState, params:LParameters, max_clock_ambiguity:int)
{
  forall replica_index :: 0 <= replica_index < |ps.replicas| ==> OverflowProtectionNotUsedForReplica(ps, replica_index, params, max_clock_ambiguity)
}

function{:opaque} OverflowProtectionNotUsedTemporal(b:Behavior<RslState>, params:LParameters, max_clock_ambiguity:int):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, OverflowProtectionNotUsedTemporal(b, params, max_clock_ambiguity))} ::
           sat(i, OverflowProtectionNotUsedTemporal(b, params, max_clock_ambiguity))
           <==> OverflowProtectionNotUsed(b[i], params, max_clock_ambiguity)
{
  stepmap(imap i :: OverflowProtectionNotUsed(b[i], params, max_clock_ambiguity))
}

///////////////////////////
// TOP-LEVEL ASSUMPTIONS
///////////////////////////

predicate LivenessAssumptions(
  b:Behavior<RslState>,
  asp:AssumptionParameters
  )
{
  && IsValidBehavior(b, asp.c)
  && var eb := RestrictBehaviorToEnvironment(b);
    var live_hosts := SetOfReplicaIndicesToSetOfHosts(asp.live_quorum, asp.c.config.replica_ids);
    && HostQueuesLive(eb)

    // The synchrony period start time is valid
    && 0 <= asp.synchrony_start

    // Time goes forward without Zeno behaviors
    && NoZenoBehavior(eb)

    // Live replicas have fairly accurate time sync
    && 0 <= asp.max_clock_ambiguity
    && ClockAmbiguityLimitedForHosts(eb, 0, asp.max_clock_ambiguity, live_hosts)

    // Overflow protection is never used
    && sat(0, always(OverflowProtectionNotUsedTemporal(b, asp.c.params, asp.max_clock_ambiguity)))

    // The live quorum is a set of replica indices and is big enough to constitute a quorum
    && (forall replica_index :: replica_index in asp.live_quorum ==> 0 <= replica_index < |asp.c.config.replica_ids|)
    && |asp.live_quorum| >= LMinQuorumSize(asp.c.config)

    // Each host in the live quorum executes periodically, with period asp.host_period
    && 0 < asp.host_period
    && (forall replica_index {:trigger HostExecutesPeriodically(b, asp, replica_index)} ::
         replica_index in asp.live_quorum ==> HostExecutesPeriodically(b, asp, replica_index))

    // The persistent client sends its request periodically, with period asp.persistent_period
    && 0 < asp.persistent_period
    && asp.persistent_request.Request?
    && (forall replica_index {:trigger PersistentClientSendsRequestPeriodically(b, asp, replica_index)} ::
         replica_index in asp.live_quorum ==> PersistentClientSendsRequestPeriodically(b, asp, replica_index))

    // and the persistent client never sends a request with a higher sequence number
    && sat(0, always(ClientNeverSentHigherSequenceNumberRequestTemporal(b, asp)))

    // ..but it never receives a reply.
    && sat(0, always(not(ReplyDeliveredTemporal(b, asp.persistent_request))))

    // The network delivers packets among the client and live quorum within time asp.latency_bound
    && 0 < asp.latency_bound
    && NetworkSynchronousForHosts(eb, asp.synchrony_start, asp.latency_bound,
                                  live_hosts + {asp.persistent_request.client}, live_hosts + {asp.persistent_request.client})

    // The network doesn't deliver packets to any host in the live quorum faster than it can process them
    && 0 < asp.burst_size
    && NetworkDeliveryRateBoundedForHosts(eb, asp.synchrony_start, asp.burst_size,
                                          asp.burst_size * asp.host_period * LReplicaNumActions() + 1, live_hosts)
}

} 
