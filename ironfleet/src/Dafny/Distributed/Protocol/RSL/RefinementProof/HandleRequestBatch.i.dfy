include "../DistributedSystem.i.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module DirectRefinement__HandleRequestBatch_i {

import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__StateMachine_i
import opened LiveRSL__Types_i
import opened Collections__Seqs_s
import opened AppStateMachine_i

function GetAppStateFromRequestBatches(batches:seq<RequestBatch>):AppState
{
  if |batches| == 0 then
    AppInitialize()
  else
    last(HandleRequestBatch(GetAppStateFromRequestBatches(all_but_last(batches)), last(batches)).0)
}

function GetReplyFromRequestBatches(batches:seq<RequestBatch>, batch_num:int, req_num:int):Reply
  requires 0 <= batch_num < |batches|
  requires 0 <= req_num < |batches[batch_num]|
{
  var prev_state := GetAppStateFromRequestBatches(batches[..batch_num]);
  var result := HandleRequestBatch(prev_state, batches[batch_num]);
  result.1[req_num]
}

lemma lemma_GetReplyFromRequestBatchesMatchesInSubsequence(batches1:seq<RequestBatch>, batches2:seq<RequestBatch>,
                                                           batch_num:int, req_num:int)
  requires 0 <= batch_num < |batches1| <= |batches2|
  requires batches1 == batches2[..|batches1|]
  requires 0 <= req_num < |batches1[batch_num]|
  ensures  GetReplyFromRequestBatches(batches1, batch_num, req_num) == GetReplyFromRequestBatches(batches2, batch_num, req_num)
{
  assert batches1[..batch_num] == batches2[..batch_num];
  assert batches1[batch_num] == batches2[batch_num];
}

}
