include "../../Services/RSL/AppStateMachine.i.dfy"
include "../Common/NodeIdentity.i.dfy"

module LiveRSL__Types_i {

import opened AppStateMachine_i
import opened Concrete_NodeIdentity_i

type OperationNumber = int
datatype Ballot = Ballot(seqno:int, proposer_id:int)
    
datatype Request = Request(client:NodeIdentity, seqno:int, request:AppMessage)
datatype Reply = Reply(client:NodeIdentity, seqno:int, reply:AppMessage)

type RequestBatch = seq<Request>
type ReplyCache = map<NodeIdentity, Reply>

datatype Vote = Vote(max_value_bal:Ballot, ghost max_val:RequestBatch)
type Votes = map<OperationNumber, Vote>

datatype LearnerTuple = LearnerTuple(received_2b_message_senders:set<NodeIdentity>, candidate_learned_value:RequestBatch)
type LearnerState = map<OperationNumber, LearnerTuple>

predicate BalLt(ba:Ballot, bb:Ballot)
{
  || ba.seqno < bb.seqno
  || (ba.seqno==bb.seqno && ba.proposer_id < bb.proposer_id)
}

predicate BalLeq(ba:Ballot, bb:Ballot)
{
  || ba.seqno < bb.seqno
  || (ba.seqno==bb.seqno && ba.proposer_id <= bb.proposer_id)
}

lemma lemma_BalLtMiddle(ba:Ballot, bb:Ballot)
  requires !BalLt(ba,bb)
  requires ba!=bb
  ensures BalLt(bb, ba)
{
}

lemma lemma_BalLtProperties()
  ensures forall ba,bb :: !BalLt(ba,bb) && ba!=bb ==> BalLt(bb,ba)
  ensures forall ba,bb :: BalLeq(ba,bb) ==> BalLt(ba,bb) || ba==bb
  // Transitivity
  ensures forall ba,bb,bc :: BalLt(ba, bb) && BalLt(bb, bc) ==> BalLt(ba,bc)
  ensures forall ba,bb,bc :: BalLt(ba, bb) && BalLeq(bb, bc) ==> BalLt(ba,bc)
  ensures forall ba,bb,bc :: BalLeq(ba, bb) && BalLt(bb, bc) ==> BalLt(ba,bc)
{
  forall (ba,bb | !BalLt(ba,bb) && ba!=bb)
    ensures BalLt(bb,ba)
  {
    lemma_BalLtMiddle(ba,bb);
  }
}

} 
