include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "StablePeriod.i.dfy"
include "../CommonProof/Actions.i.dfy"

module LivenessProof__RequestQueue_i {

import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened CommonProof__Actions_i
import opened LivenessProof__StablePeriod_i

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
    requires LivenessAssumptions(b, asp);
    requires sat(start_step, StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx));
    requires sat(start_step, always(RequestInFirstNTemporal(b, view.proposer_id, req, n)));
    requires 0 <= start_step <= i;
    requires 0 <= view.proposer_id < |b[i].replicas|;
    requires b[i].replicas[view.proposer_id].replica.proposer.max_ballot_i_sent_1a == view;
    requires b[i].replicas[view.proposer_id].replica.proposer.current_state == 1;
    ensures  RequestInFirstNOfRequestQueue(b[i], view.proposer_id, req, n);
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
            }
        }
        else
        {
            var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i-1, idx);
            TemporalDeduceFromAlways(start_step, i-1, RequestInFirstNTemporal(b, idx, req, n));
        }
    }
}

}
