include "../../Protocol/RSL/Election.i.dfy"
include "CTypes.i.dfy"
include "ReplicaConstantsState.i.dfy"

module LiveRSL__ElectionState_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__Election_i
import opened LiveRSL__ReplicaConstantsState_i
import opened Common__SeqIsUniqueDef_i
import opened Common__NodeIdentity_i

datatype CRequestHeader = CRequestHeader(client:EndPoint, seqno:uint64)

datatype CElectionState = CElectionState(
  constants:ReplicaConstantsState,
  // The replica constants, duplicated here for convenience

  current_view:CBallot,
  // The last view I think has won a leader election

  current_view_suspectors:seq<uint64>,
  // The set of nodes who suspect current_view.  When this constitutes
  // a quorum, I'll elect the next view.

  epoch_end_time:uint64,
  // When the next view-test epoch will end.

  epoch_length:uint64,
  // How long the current view-test epoch length is.  When we enter a new view,
  // we double this.

  requests_received_this_epoch:seq<CRequest>,
  // The set of requests we've received this epoch but haven't executed this epoch yet
  // and didn't execute in the previous epoch.

  ghost cur_req_set:set<CRequestHeader>,
  // Duplicates the sequence above for faster lookups

  requests_received_prev_epochs:seq<CRequest>,
  // The set of requests we received in the previous epoch but haven't executed in
  // the current epoch, the previous epoch, or the epoch before that.

  ghost prev_req_set:set<CRequestHeader>
  // Duplicates the sequence above for faster lookups
  )

predicate ElectionRequestQueueValid(queue:seq<CRequest>) 
{
  forall i :: 0 <= i < |queue| ==> ValidRequest(queue[i])
}

predicate CElectionStateIsAbstractable(election:CElectionState)
{
  && ReplicaConstantsStateIsAbstractable(election.constants)
  && CBallotIsAbstractable(election.current_view)
  && SeqIsUnique(election.current_view_suspectors)
  && CRequestsSeqIsAbstractable(election.requests_received_this_epoch)
  && CRequestsSeqIsAbstractable(election.requests_received_prev_epochs)
}

function AbstractifyCElectionStateToElectionState(election:CElectionState) : ElectionState
  requires CElectionStateIsAbstractable(election)
{
  ElectionState(AbstractifyReplicaConstantsStateToLReplicaConstants(election.constants),
                AbstractifyCBallotToBallot(election.current_view),
                AbstractifySeqOfUint64sToSetOfInts(election.current_view_suspectors),
                election.epoch_end_time as int,
                election.epoch_length as int,
                AbstractifyCRequestsSeqToRequestsSeq(election.requests_received_this_epoch), 
                AbstractifyCRequestsSeqToRequestsSeq(election.requests_received_prev_epochs))
}

predicate method CRequestsMatch(r1:CRequest, r2:CRequest)
{
  r1.client == r2.client && r1.seqno == r2.seqno
}

predicate method CRequestSatisfiedBy(r1:CRequest, r2:CRequest)
{
  r1.client == r2.client && r1.seqno <= r2.seqno
}

predicate HeadersMatch(requests:seq<CRequest>, headers:set<CRequestHeader>)
{
  &&  |requests| == |headers|
  && (forall r :: r in requests ==> CRequestHeader(r.client, r.seqno) in headers)
  && (forall i,j {:trigger CRequestsMatch(requests[i], requests[j])} :: 0 <= i < j < |requests| && CRequestsMatch(requests[i], requests[j]) ==> i == j)
}

predicate CElectionStateIsValid(election:CElectionState)
{
  && CElectionStateIsAbstractable(election)
  && ReplicaConstantsState_IsValid(election.constants)
  && ReplicaIndicesValid(election.current_view_suspectors, election.constants.all.config)
  && |election.requests_received_this_epoch|  < 0x8000_0000_0000_0000
  && |election.requests_received_prev_epochs| < 0x8000_0000_0000_0000
  && ElectionRequestQueueValid(election.requests_received_this_epoch)
  && ElectionRequestQueueValid(election.requests_received_prev_epochs)
  && HeadersMatch(election.requests_received_this_epoch, election.cur_req_set)
  && HeadersMatch(election.requests_received_prev_epochs, election.prev_req_set)
  && HeadersMatch(election.requests_received_prev_epochs + election.requests_received_this_epoch, election.prev_req_set + election.cur_req_set)
}


} 
