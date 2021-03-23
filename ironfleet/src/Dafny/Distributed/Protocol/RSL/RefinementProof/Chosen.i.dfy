include "../DistributedSystem.i.dfy"
include "../CommonProof/Constants.i.dfy"
include "../CommonProof/Actions.i.dfy"
include "../CommonProof/PacketSending.i.dfy"
include "../CommonProof/Chosen.i.dfy"
include "../../../Common/Collections/Seqs.s.dfy"
include "../../../Common/Collections/Sets.i.dfy"
include "HandleRequestBatch.i.dfy"

module DirectRefinement__Chosen_i {

import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__StateMachine_i
import opened LiveRSL__Types_i
import opened CommonProof__Actions_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Chosen_i
import opened CommonProof__Constants_i
import opened CommonProof__Environment_i
import opened CommonProof__PacketSending_i
import opened Collections__Seqs_s
import opened Collections__Sets_i
import opened DirectRefinement__HandleRequestBatch_i
import opened Temporal__Temporal_s

predicate IsValidQuorumOf2bsSequence(ps:RslState, qs:seq<QuorumOf2bs>)
{
  forall opn :: 0 <= opn < |qs| ==> qs[opn].opn == opn && IsValidQuorumOf2bs(ps, qs[opn])
}

predicate IsMaximalQuorumOf2bsSequence(ps:RslState, qs:seq<QuorumOf2bs>)
{
  && IsValidQuorumOf2bsSequence(ps, qs)
  && !exists q :: IsValidQuorumOf2bs(ps, q) && q.opn == |qs|
}

function GetSequenceOfRequestBatches(qs:seq<QuorumOf2bs>):seq<RequestBatch>
  ensures |GetSequenceOfRequestBatches(qs)| == |qs|
{
  if |qs| == 0 then
    []
  else
    GetSequenceOfRequestBatches(all_but_last(qs)) + [last(qs).v]
}

lemma lemma_SequenceOfRequestBatchesNthElement(qs:seq<QuorumOf2bs>, n:int)
  requires 0 <= n < |qs|
  ensures  GetSequenceOfRequestBatches(qs)[n] == qs[n].v
{
  if n < |qs| - 1
  {
    lemma_SequenceOfRequestBatchesNthElement(all_but_last(qs), n);
  }
}

lemma lemma_GetUpperBoundOnQuorumOf2bsOperationNumber(
  b:Behavior<RslState>,
  c:LConstants,
  i:int
  ) returns (
  bound:OperationNumber
  )
  requires IsValidBehaviorPrefix(b, c, i)
  ensures  bound >= 0
  ensures  !exists q :: IsValidQuorumOf2bs(b[i], q) && q.opn == bound
{
  var opns := set p | p in b[i].environment.sentPackets && p.msg.RslMessage_2b? :: p.msg.opn_2b;
  bound := if |opns| > 0 && intsetmax(opns) >= 0 then intsetmax(opns) + 1 else 1;
  if exists q :: IsValidQuorumOf2bs(b[i], q) && q.opn == bound
  {
    var q :| IsValidQuorumOf2bs(b[i], q) && q.opn == bound;
    var idx :| idx in q.indices;
    var p := q.packets[idx];
    assert p.msg.opn_2b in opns;
    assert p.msg.opn_2b > intsetmax(opns);
    assert p.msg.opn_2b in opns;
    assert false;
  }
}

lemma lemma_GetMaximalQuorumOf2bsSequenceWithinBound(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  bound:OperationNumber
  ) returns (
  qs:seq<QuorumOf2bs>
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= bound
  ensures  IsValidQuorumOf2bsSequence(b[i], qs)
  ensures  |qs| == bound || !exists q :: IsValidQuorumOf2bs(b[i], q) && q.opn == |qs|
{
  if bound == 0
  {
    qs := [];
    return;
  }

  qs := lemma_GetMaximalQuorumOf2bsSequenceWithinBound(b, c, i, bound-1);
  if !exists q :: IsValidQuorumOf2bs(b[i], q) && q.opn == |qs|
  {
    return;
  }

  assert |qs| == bound - 1;
  var q :| IsValidQuorumOf2bs(b[i], q) && q.opn == bound - 1;
  qs := qs + [q];
}

lemma lemma_GetMaximalQuorumOf2bsSequence(
  b:Behavior<RslState>,
  c:LConstants,
  i:int
  ) returns (
  qs:seq<QuorumOf2bs>
  )
  requires IsValidBehaviorPrefix(b, c, i)
  ensures  IsMaximalQuorumOf2bsSequence(b[i], qs)
{
  var bound := lemma_GetUpperBoundOnQuorumOf2bsOperationNumber(b, c, i);
  qs := lemma_GetMaximalQuorumOf2bsSequenceWithinBound(b, c, i, bound);
}

lemma lemma_IfValidQuorumOf2bsSequenceNowThenNext(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  qs:seq<QuorumOf2bs>
  )
  requires IsValidBehaviorPrefix(b, c, i+1)
  requires 0 <= i
  requires IsValidQuorumOf2bsSequence(b[i], qs)
  ensures  IsValidQuorumOf2bsSequence(b[i+1], qs)
{
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i+1);

  forall opn | 0 <= opn < |qs|
    ensures qs[opn].opn == opn
    ensures IsValidQuorumOf2bs(b[i+1], qs[opn])
  {
    assert qs[opn].opn == opn && IsValidQuorumOf2bs(b[i], qs[opn]);
    forall idx | idx in qs[opn].indices
      ensures qs[opn].packets[idx] in b[i+1].environment.sentPackets
    {
      lemma_PacketStaysInSentPackets(b, c, i, i+1, qs[opn].packets[idx]);
    }
  }
}

lemma lemma_TwoMaximalQuorumsOf2bsMatch(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  qs1:seq<QuorumOf2bs>,
  qs2:seq<QuorumOf2bs>
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires IsMaximalQuorumOf2bsSequence(b[i], qs1)
  requires IsMaximalQuorumOf2bsSequence(b[i], qs2)
  ensures  GetSequenceOfRequestBatches(qs1) == GetSequenceOfRequestBatches(qs2)
{
  var batches1 := GetSequenceOfRequestBatches(qs1);
  var batches2 := GetSequenceOfRequestBatches(qs2);

  if |qs1| > |qs2|
  {
    assert IsValidQuorumOf2bs(b[i], qs1[|qs2|]) && qs1[|qs2|].opn == |qs2|;
    assert false;
  }
  if |qs2| > |qs1|
  {
    assert IsValidQuorumOf2bs(b[i], qs2[|qs1|]) && qs2[|qs1|].opn == |qs1|;
    assert false;
  }
    
  forall opn | 0 <= opn < |qs1|
    ensures batches1[opn] == batches2[opn]
  {
    lemma_ChosenQuorumsMatchValue(b, c, i, qs1[opn], qs2[opn]);
    lemma_SequenceOfRequestBatchesNthElement(qs1, opn);
    lemma_SequenceOfRequestBatchesNthElement(qs2, opn);
  }
}

lemma lemma_RegularQuorumOf2bSequenceIsPrefixOfMaximalQuorumOf2bSequence(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  qs_regular:seq<QuorumOf2bs>,
  qs_maximal:seq<QuorumOf2bs>
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires IsValidQuorumOf2bsSequence(b[i], qs_regular)
  requires IsMaximalQuorumOf2bsSequence(b[i], qs_maximal)
  ensures  |GetSequenceOfRequestBatches(qs_regular)| <= |GetSequenceOfRequestBatches(qs_maximal)|
  ensures  GetSequenceOfRequestBatches(qs_regular) == GetSequenceOfRequestBatches(qs_maximal)[..|GetSequenceOfRequestBatches(qs_regular)|]
{
  var batches1 := GetSequenceOfRequestBatches(qs_regular);
  var batches2 := GetSequenceOfRequestBatches(qs_maximal);

  if |qs_regular| > |qs_maximal|
  {
    assert IsValidQuorumOf2bs(b[i], qs_regular[|qs_maximal|]) && qs_regular[|qs_maximal|].opn == |qs_maximal|;
    assert false;
  }
    
  forall opn | 0 <= opn < |qs_regular|
    ensures batches1[opn] == batches2[opn]
  {
    lemma_ChosenQuorumsMatchValue(b, c, i, qs_regular[opn], qs_maximal[opn]);
    lemma_SequenceOfRequestBatchesNthElement(qs_regular, opn);
    lemma_SequenceOfRequestBatchesNthElement(qs_maximal, opn);
  }
}

}
