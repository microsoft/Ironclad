include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "StablePeriod.i.dfy"
include "../CommonProof/Actions.i.dfy"

module LivenessProof__RequestQueue_i {

import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Environment_i
import opened LivenessProof__Invariants_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened LivenessProof__StablePeriod_i
import opened Temporal__Temporal_s
import opened Temporal__Rules_i
import opened Environment_s
import opened Collections__Maps2_s

lemma lemma_RequestInFirstNOfRequestQueueDuringPhase1(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  start_step:int,
  view:Ballot,
  ahead_idx:int,
  req:Request,
  n:int
  )
  requires LivenessAssumptions(b, asp)
  requires sat(start_step, StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx))
  requires sat(start_step, always(RequestInFirstNTemporal(b, view.proposer_id, req, n)))
  requires 0 <= start_step <= i
  requires 0 <= view.proposer_id < |b[i].replicas|
  requires b[i].replicas[view.proposer_id].replica.proposer.max_ballot_i_sent_1a == view
  requires b[i].replicas[view.proposer_id].replica.proposer.current_state == 1
  ensures  RequestInFirstNOfRequestQueue(b[i], view.proposer_id, req, n)
{
  if i == start_step
  {
    assert false;
  }
  else
  {
    lemma_ConstantsAllConsistent(b, asp.c, i-1);
    lemma_ConstantsAllConsistent(b, asp.c, i);
    lemma_AssumptionsMakeValidTransition(b, asp.c, i-1);

    var idx := view.proposer_id;
    var s := b[i-1].replicas[idx].replica.proposer;
    var s' := b[i].replicas[idx].replica.proposer;

    if s.max_ballot_i_sent_1a == view && s.current_state == 1
    {
      lemma_RequestInFirstNOfRequestQueueDuringPhase1(b, asp, i-1, start_step, view, ahead_idx, req, n);
      if s'.request_queue == s.request_queue
      {
        assert RequestInFirstNOfRequestQueue(b[i], idx, req, n);
      }
      else
      {
        var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i-1, idx);
        var action_index := b[i-1].replicas[idx].nextActionIndex;
        assert action_index == 0 && ios[0].LIoOpReceive? && ios[0].r.msg.RslMessage_Request?;
        assert s.request_queue <= s'.request_queue;
      }
    }
    else
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i-1, idx);
      TemporalDeduceFromAlways(start_step, i-1, RequestInFirstNTemporal(b, idx, req, n));
      var action_index := b[i-1].replicas[idx].nextActionIndex;
      assert action_index == 1;
      assert s.election_state.requests_received_prev_epochs <= s'.request_queue;
    }
  }
}

}
