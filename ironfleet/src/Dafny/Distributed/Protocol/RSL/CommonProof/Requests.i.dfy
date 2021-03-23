include "../DistributedSystem.i.dfy"
include "../CommonProof/Assumptions.i.dfy"
include "../CommonProof/Constants.i.dfy"
include "../CommonProof/Actions.i.dfy"
include "../CommonProof/Environment.i.dfy"
include "../CommonProof/PacketSending.i.dfy"
include "../CommonProof/Chosen.i.dfy"

module CommonProof__Requests_i {

import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Election_i
import opened LiveRSL__Types_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened CommonProof__Environment_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Chosen_i

lemma lemma_RemoveAllSatisfiedRequestsInSequenceProducesSubsequence(s':seq<Request>, s:seq<Request>, r:Request)
  requires s' == RemoveAllSatisfiedRequestsInSequence(s, r)
  ensures  forall x :: x in s' ==> x in s
  decreases s, 1
{
  if |s| > 0 && !RequestsMatch(s[0], r)
  {
    lemma_RemoveAllSatisfiedRequestsInSequenceProducesSubsequence(RemoveAllSatisfiedRequestsInSequence(s[1..], r), s[1..], r);
  }
}

lemma lemma_RemoveExecutedRequestBatchProducesSubsequence(s':seq<Request>, s:seq<Request>, batch:RequestBatch)
  requires s' == RemoveExecutedRequestBatch(s, batch)
  ensures  forall x :: x in s' ==> x in s
  decreases |batch|
{
  if |batch| > 0
  {
    var s'' := RemoveAllSatisfiedRequestsInSequence(s, batch[0]);
    lemma_RemoveAllSatisfiedRequestsInSequenceProducesSubsequence(s'', s, batch[0]);
    lemma_RemoveExecutedRequestBatchProducesSubsequence(s', s'', batch[1..]);
  }
}
    
}
