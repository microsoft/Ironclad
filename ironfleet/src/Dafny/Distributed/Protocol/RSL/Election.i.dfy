include "Constants.i.dfy"
include "Environment.i.dfy"
include "Types.i.dfy"
include "../../Common/Collections/Seqs.i.dfy"

module LiveRSL__Election_i {
import opened LiveRSL__Constants_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Types_i
import opened LiveRSL__Configuration_i
import opened Collections__Seqs_i
import opened Common__UpperBound_s

//////////////////////
// ELECTION STATE
//////////////////////

datatype ElectionState = ElectionState(
  constants:LReplicaConstants,
  // The replica constants, duplicated here for convenience

  current_view:Ballot,
  // The last view I think has won a leader election

  current_view_suspectors:set<int>,
  // The set of indices of nodes who suspect current_view.  When this constitutes
  // a quorum, I'll elect the next view.

  epoch_end_time:int,
  // When the next view-test epoch will end.

  epoch_length:int,
  // How long the current view-test epoch length is.  When we enter a new view,
  // we double this.
    
  requests_received_this_epoch:seq<Request>,
  // The set of requests we've received this epoch but haven't executed this epoch yet
  // and didn't execute in the previous epoch.

  requests_received_prev_epochs:seq<Request>
  // The set of requests we received in the previous epoch but haven't executed in
  // the current epoch, the previous epoch, or the epoch before that.
  )

//////////////////////
// BALLOT MATH
//////////////////////

function ComputeSuccessorView(b:Ballot, c:LConstants):Ballot
{
  if b.proposer_id + 1 < |c.config.replica_ids| then
    Ballot(b.seqno, b.proposer_id + 1)
  else
    Ballot(b.seqno + 1, 0)
}

//////////////////////
// SEQUENCE MATH
//////////////////////

function BoundRequestSequence(s:seq<Request>, lengthBound:UpperBound):seq<Request>
{
  if lengthBound.UpperBoundFinite? && 0 <= lengthBound.n < |s| then s[..lengthBound.n] else s
}

//////////////////////
// REQUESTS
//////////////////////

predicate RequestsMatch(r1:Request, r2:Request)
{
  r1.Request? && r2.Request? && r1.client == r2.client && r1.seqno == r2.seqno
}

predicate RequestSatisfiedBy(r1:Request, r2:Request)
{
  r1.Request? && r2.Request? && r1.client == r2.client && r1.seqno <= r2.seqno
}

function RemoveAllSatisfiedRequestsInSequence(s:seq<Request>, r:Request):seq<Request>
{
  if |s| == 0 then
    []
  else if RequestSatisfiedBy(s[0], r) then
    RemoveAllSatisfiedRequestsInSequence(s[1..], r)
  else
    [s[0]] + RemoveAllSatisfiedRequestsInSequence(s[1..], r)
}

//////////////////////
// INITIALIZATION
//////////////////////

predicate ElectionStateInit(
  es:ElectionState,
  c:LReplicaConstants
  )
  requires |c.all.config.replica_ids| > 0
{
  && es.constants == c
  && es.current_view == Ballot(1, 0)
  && es.current_view_suspectors == {}
  && es.epoch_end_time == 0
  && es.epoch_length == c.all.params.baseline_view_timeout_period
  && es.requests_received_this_epoch == []
  && es.requests_received_prev_epochs == []
}

//////////////////////
// ACTIONS
//////////////////////

predicate ElectionStateProcessHeartbeat(
  es:ElectionState,
  es':ElectionState,
  p:RslPacket,
  clock:int
  )
  requires p.msg.RslMessage_Heartbeat?
{
  if p.src !in es.constants.all.config.replica_ids then
    es' == es
  else
    var sender_index := GetReplicaIndex(p.src, es.constants.all.config);
    if p.msg.bal_heartbeat == es.current_view && p.msg.suspicious then
      es' == es.(current_view_suspectors := es.current_view_suspectors + {sender_index})
    else if BalLt(es.current_view, p.msg.bal_heartbeat)  then
      var new_epoch_length := UpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val);
      es' == es.(current_view := p.msg.bal_heartbeat,
                 current_view_suspectors := (if p.msg.suspicious then {sender_index} else {}),
                 epoch_length := new_epoch_length,
                 epoch_end_time := UpperBoundedAddition(clock, new_epoch_length, es.constants.all.params.max_integer_val),
                 requests_received_prev_epochs := BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val),
                 requests_received_this_epoch := [])
    else
      es' == es
}

predicate ElectionStateCheckForViewTimeout(
  es:ElectionState,
  es':ElectionState,
  clock:int
  )
{
  if clock < es.epoch_end_time then
    es' == es
  else if |es.requests_received_prev_epochs| == 0 then
    var new_epoch_length := es.constants.all.params.baseline_view_timeout_period;
    es' == es.(epoch_length := new_epoch_length,
               epoch_end_time := UpperBoundedAddition(clock, new_epoch_length, es.constants.all.params.max_integer_val),
               requests_received_prev_epochs := es.requests_received_this_epoch,
               requests_received_this_epoch := [])
  else
    es' == es.(current_view_suspectors := es.current_view_suspectors + {es.constants.my_index},
               epoch_end_time := UpperBoundedAddition(clock, es.epoch_length, es.constants.all.params.max_integer_val),
               requests_received_prev_epochs := BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val),
               requests_received_this_epoch := [])
}

predicate ElectionStateCheckForQuorumOfViewSuspicions(
  es:ElectionState,
  es':ElectionState,
  clock:int
  )
{
  if |es.current_view_suspectors| < LMinQuorumSize(es.constants.all.config) || !LtUpperBound(es.current_view.seqno, es.constants.all.params.max_integer_val) then
    es' == es
  else
    var new_epoch_length := UpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val);
    es' == es.(current_view := ComputeSuccessorView(es.current_view, es.constants.all),
               current_view_suspectors := {},
               epoch_length := new_epoch_length,
               epoch_end_time := UpperBoundedAddition(clock, new_epoch_length, es.constants.all.params.max_integer_val),
               requests_received_prev_epochs := BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val),
               requests_received_this_epoch := [])
}

predicate ElectionStateReflectReceivedRequest(
  es:ElectionState,
  es':ElectionState,
  req:Request
  )
{
  if exists earlier_req :: && (earlier_req in es.requests_received_prev_epochs || earlier_req in es.requests_received_this_epoch)
                     && RequestsMatch(earlier_req, req) then
    es' == es
  else
    es' == es.(requests_received_this_epoch := BoundRequestSequence(es.requests_received_this_epoch + [req], es.constants.all.params.max_integer_val))
}

function RemoveExecutedRequestBatch(reqs:seq<Request>, batch:RequestBatch):seq<Request>
  decreases |batch|
{
  if |batch| == 0 then
    reqs
  else
    RemoveExecutedRequestBatch(RemoveAllSatisfiedRequestsInSequence(reqs, batch[0]), batch[1..])
}

predicate ElectionStateReflectExecutedRequestBatch(
  es:ElectionState,
  es':ElectionState,
  batch:RequestBatch
  )
{
  es' == es.(requests_received_prev_epochs := RemoveExecutedRequestBatch(es.requests_received_prev_epochs, batch),
             requests_received_this_epoch := RemoveExecutedRequestBatch(es.requests_received_this_epoch, batch))
}

}
