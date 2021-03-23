include "../../Protocol/RSL/Proposer.i.dfy"
include "ElectionState.i.dfy"
include "ReplicaConstantsState.i.dfy"

module LiveRSL__ProposerState_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__ElectionState_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__ReplicaConstantsState_i

datatype CIncompleteBatchTimer = CIncompleteBatchTimerOn(when:uint64) | CIncompleteBatchTimerOff()

datatype ProposerState = ProposerState(
  constants:ReplicaConstantsState,

  current_state:byte,
  // What state the proposer is in:
  // 0 = not leader
  // 1 = leader in phase 1
  // 2 = leader in phase 2

  request_queue:seq<CRequest>,
  // Values that clients have requested that I need to eventually
  // propose, in the order I should propose them

  max_ballot_i_sent_1a:CBallot,
  // The maximum ballot I've sent a 1a message for

  next_operation_number_to_propose:uint64,
  // The next operation number I should propose

  received_1b_packets:set<CPacket>,
  // The set of 1b messages I've received concerning max_ballot_i_sent_1a

  highest_seqno_requested_by_client_this_view:map<EndPoint, uint64>,
  // For each client, the highest sequence number for a request
  // I proposed in max_ballot_i_sent_1a

  incomplete_batch_timer:CIncompleteBatchTimer,
  // If the incomplete batch timer is set, it indicates when I should
  // give up on trying to amass a full-size batch and just propose
  // whatever I have.  If it's not set, I shouldn't propose an
  // incomplete batch.

  election_state:CElectionState,

  maxOpnWithProposal:COperationNumber,

  maxLogTruncationPoint:COperationNumber
  )

// Implied by Received1bPacketsIsModest
//predicate Received1bPacketsIsModest(proposer:ProposerState)
//{
//  |proposer.received_1b_packets| < 0xffffffff_ffffffff
//}

predicate ProposerIsAbstractable(proposer:ProposerState)
{
  && ReplicaConstantsStateIsAbstractable(proposer.constants)
  && CRequestsSeqIsAbstractable(proposer.request_queue)
  && CBallotIsAbstractable(proposer.max_ballot_i_sent_1a)
  && CPacketsIsAbstractable(proposer.received_1b_packets)
  && MapOfSeqNumsIsAbstractable(proposer.highest_seqno_requested_by_client_this_view)
  && CElectionStateIsAbstractable(proposer.election_state)
}

function AbstractifyCIncompleteBatchTimerToIncompleteBatchTimer(timer:CIncompleteBatchTimer) : IncompleteBatchTimer
{
  match timer {
    case CIncompleteBatchTimerOn(when) => IncompleteBatchTimerOn(when as int)
    case CIncompleteBatchTimerOff => IncompleteBatchTimerOff()
  }
}

function AbstractifyProposerStateToLProposer(proposer:ProposerState) : LProposer
  requires ProposerIsAbstractable(proposer)
{
  LProposer(AbstractifyReplicaConstantsStateToLReplicaConstants(proposer.constants),
            proposer.current_state as int,
            AbstractifyCRequestsSeqToRequestsSeq(proposer.request_queue),
            AbstractifyCBallotToBallot(proposer.max_ballot_i_sent_1a),
            proposer.next_operation_number_to_propose as int,
            AbstractifySetOfCPacketsToSetOfRslPackets(proposer.received_1b_packets),
            AbstractifyMapOfSeqNums(proposer.highest_seqno_requested_by_client_this_view),
            AbstractifyCIncompleteBatchTimerToIncompleteBatchTimer(proposer.incomplete_batch_timer),
            AbstractifyCElectionStateToElectionState(proposer.election_state))
}

predicate RequestQueueValid(queue:seq<CRequest>) 
{
  forall i :: 0 <= i < |queue| ==> ValidRequest(queue[i])
}

predicate MaxOpnWithProposalInVotes(proposer:ProposerState)
{
  forall p :: p in proposer.received_1b_packets && p.msg.CMessage_1b? ==> MaxOpnWithProposal(proposer, p.msg.votes)
}

predicate MaxOpnWithProposal(proposer:ProposerState, votes:CVotes)
{
  forall opn :: opn in votes.v ==> opn.n < proposer.maxOpnWithProposal.n
}

predicate MaxLogTruncationPoint(proposer:ProposerState)
{
  forall p :: p in proposer.received_1b_packets && p.msg.CMessage_1b? ==> p.msg.log_truncation_point.n <= proposer.maxLogTruncationPoint.n
}

predicate {:opaque} Received1bProperties(received_1b_packets:set<CPacket>, constants:ReplicaConstantsState)
{
  && (forall p :: p in received_1b_packets ==> p.src in constants.all.config.replica_ids)
  && (forall p1,p2 :: p1 in received_1b_packets && p2 in received_1b_packets && p1.src == p2.src ==> p1 == p2)
}

predicate ProposerIsValid(proposer:ProposerState) 
{
  && ProposerIsAbstractable(proposer)
  && ReplicaConstantsState_IsValid(proposer.constants)
  && CElectionStateIsValid(proposer.election_state)
  && (forall p :: p in proposer.received_1b_packets ==> 
           && p.msg.CMessage_1b? 
           && p.msg.bal_1b == proposer.max_ballot_i_sent_1a  // Useful invariant to simplify MaybeEnterPhase2
           && ValidVotes(p.msg.votes))
  && Received1bProperties(proposer.received_1b_packets, proposer.constants)
  && RequestQueueValid(proposer.request_queue)
  && (proposer.current_state == 2 ==> (proposer.maxOpnWithProposal.n < 0xffff_ffff_ffff_ffff ==> MaxOpnWithProposalInVotes(proposer)))
  && (proposer.current_state == 2 ==> MaxLogTruncationPoint(proposer))
}

} 
