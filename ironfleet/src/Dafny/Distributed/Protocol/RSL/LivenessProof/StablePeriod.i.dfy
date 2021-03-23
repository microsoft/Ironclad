include "Assumptions.i.dfy"
include "PacketHandling.i.dfy"
    
module LivenessProof__StablePeriod_i {

import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__PacketHandling_i
import opened LivenessProof__RoundRobin_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Collections__Maps2_s
    
function CurrentViewOfHost(
  ps:RslState,
  replica_index:int
  ):Ballot
  requires 0 <= replica_index < |ps.replicas|
{
  ps.replicas[replica_index].replica.proposer.election_state.current_view
}

predicate StablePeriodStarted(
  ps:RslState,
  live_quorum:set<int>,
  view:Ballot,
  ahead_idx:int
  )
{
  && ahead_idx in live_quorum
  && 0 <= ahead_idx < |ps.replicas|
  && BalLeq(view, CurrentViewOfHost(ps, ahead_idx))
  && view.proposer_id in live_quorum
  && (forall idx :: 0 <= idx < |ps.replicas| ==> BalLt(ps.replicas[idx].replica.proposer.max_ballot_i_sent_1a, view))
}

function{:opaque} StablePeriodStartedTemporal(
  b:Behavior<RslState>,
  live_quorum:set<int>,
  view:Ballot,
  ahead_idx:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, StablePeriodStartedTemporal(b, live_quorum, view, ahead_idx))} ::
             sat(i, StablePeriodStartedTemporal(b, live_quorum, view, ahead_idx))
             <==> StablePeriodStarted(b[i], live_quorum, view, ahead_idx)
{
  stepmap(imap i :: StablePeriodStarted(b[i], live_quorum, view, ahead_idx))
}

predicate NoReplicaBeyondView(
  ps:RslState,
  view:Ballot
  )
{
  forall idx :: 0 <= idx < |ps.replicas| ==> BalLeq(CurrentViewOfHost(ps, idx), view)
}

function{:opaque} NoReplicaBeyondViewTemporal(
  b:Behavior<RslState>,
  view:Ballot
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, NoReplicaBeyondViewTemporal(b, view))} ::
             sat(i, NoReplicaBeyondViewTemporal(b, view)) <==> NoReplicaBeyondView(b[i], view)
{
  stepmap(imap i :: NoReplicaBeyondView(b[i], view))
}

predicate NoMaxBallotISent1aBeyondView(
  ps:RslState,
  view:Ballot
  )
{
  forall idx :: 0 <= idx < |ps.replicas| ==> BalLeq(ps.replicas[idx].replica.proposer.max_ballot_i_sent_1a, view)
}

function{:opaque} NoMaxBallotISent1aBeyondViewTemporal(
  b:Behavior<RslState>,
  view:Ballot
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, NoMaxBallotISent1aBeyondViewTemporal(b, view))} ::
             sat(i, NoMaxBallotISent1aBeyondViewTemporal(b, view)) <==> NoMaxBallotISent1aBeyondView(b[i], view)
{
  stepmap(imap i :: NoMaxBallotISent1aBeyondView(b[i], view))
}

predicate ObjectInFirstNOfSequence<T>(obj:T, s:seq<T>, n:int)
{
  if |s| <= n then (obj in s) else (n > 0 && obj in s[..n])
}

predicate RequestInFirstN(
  ps:RslState,
  idx:int,
  req:Request,
  n:int
  )
{
  && 0 <= idx < |ps.replicas|
  && ObjectInFirstNOfSequence(req, ps.replicas[idx].replica.proposer.election_state.requests_received_prev_epochs, n)
}

function{:opaque} RequestInFirstNTemporal(
  b:Behavior<RslState>,
  idx:int,
  req:Request,
  n:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, RequestInFirstNTemporal(b, idx, req, n))} ::
             sat(i, RequestInFirstNTemporal(b, idx, req, n)) <==> RequestInFirstN(b[i], idx, req, n)
{
  stepmap(imap i :: RequestInFirstN(b[i], idx, req, n))
}

predicate RequestInFirstNOfRequestQueue(
  ps:RslState,
  idx:int,
  req:Request,
  n:int
  )
{
  && 0 <= idx < |ps.replicas|
  && ObjectInFirstNOfSequence(req, ps.replicas[idx].replica.proposer.request_queue, n)
}

datatype Phase2Params = Phase2Params(
  start_step:int,
  duration:int,
  base_duration:int,
  per_request_duration:int,
  processing_bound:int,
  view:Ballot,
  log_truncation_point:int,
  king_idx:int,
  num_requests:int,
  ios:seq<RslIo>
  )

function TimeToBeginPhase2(asp:AssumptionParameters, processing_bound:int):int
{
  processing_bound * 3
}

function TimeToAdvanceOneOperation(asp:AssumptionParameters, processing_bound:int):int
  requires asp.host_period > 0
{
  asp.c.params.max_batch_delay + asp.max_clock_ambiguity * 4 + asp.c.params.heartbeat_period + TimeToPerformGenericAction(asp) * 6 + processing_bound * 3
}

predicate Phase2Started(
  ps:RslState,
  ps':RslState,
  asp:AssumptionParameters,
  h:Phase2Params
  )
{
  && 0 <= h.king_idx < |ps'.replicas|
  && 0 <= h.view.proposer_id < |ps.replicas|
  && 0 <= h.view.proposer_id < |ps'.replicas|
  && ps'.replicas[h.king_idx].replica.executor.ops_complete >= h.log_truncation_point
  && var s := ps.replicas[h.view.proposer_id].replica;
    var s' := ps'.replicas[h.view.proposer_id].replica;
    && RslNextOneReplica(ps, ps', h.view.proposer_id, h.ios)
    && LProposerMaybeEnterPhase2(s.proposer, s'.proposer, s.acceptor.log_truncation_point, ExtractSentPacketsFromIos(h.ios))
    && s.proposer.current_state == 1
    && s'.proposer.current_state == 2
    && s'.proposer.max_ballot_i_sent_1a == h.view
    && s'.proposer.next_operation_number_to_propose == h.log_truncation_point
    && ObjectInFirstNOfSequence(asp.persistent_request, s'.proposer.request_queue, h.num_requests)
    && s'.acceptor.log_truncation_point == h.log_truncation_point
}

function{:opaque} Phase2StartedTemporal(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, Phase2StartedTemporal(b, asp, h))} ::
               sat(i, Phase2StartedTemporal(b, asp, h)) <==>
               Phase2Started(b[i], b[nextstep(i)], asp, h);
{
  stepmap(imap i :: Phase2Started(b[i], b[nextstep(i)], asp, h))
}

predicate Phase2StableWithRequest(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params
  )
{
  && LivenessAssumptions(b, asp)
  && asp.synchrony_start <= h.start_step
  && PacketProcessingSynchronous(b, asp, h.start_step, h.processing_bound)
  && h.base_duration >= 0
  && h.per_request_duration >= 0
  && h.duration == h.base_duration + h.num_requests * h.per_request_duration
  && h.view.proposer_id in asp.live_quorum
  && h.king_idx in asp.live_quorum
  && h.num_requests > 0
  && sat(h.start_step, Phase2StartedTemporal(b, asp, h))
  && sat(h.start_step+1, alwayswithin(NoReplicaBeyondViewTemporal(b, h.view), h.duration, PaxosTimeMap(b)))
}

}
