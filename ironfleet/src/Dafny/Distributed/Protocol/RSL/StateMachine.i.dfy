include "../../Services/RSL/AppStateMachine.i.dfy"
include "Types.i.dfy"
    
module LiveRSL__StateMachine_i {

import opened AppStateMachine_i
import opened LiveRSL__Types_i

function HandleRequest(state:AppState, request:Request) : (AppState, Reply)
{
  var (new_state, reply) := AppHandleRequest(state, request.request);
  (new_state, Reply(request.client, request.seqno, reply))
}

function {:opaque} HandleRequestBatchHidden(state:AppState, batch:RequestBatch) : (seq<AppState>, seq<Reply>)
  ensures var (states, replies) := HandleRequestBatchHidden(state, batch); 
          && |states| == |batch|+1
          && |replies| == |batch|
          && forall i :: 0 <= i < |batch| ==> replies[i].Reply?
  decreases |batch|
{
  //lemma_HandleRequestBatch(state, batch, HandleRequestBatch(state, batch).0, HandleRequestBatch(state, batch).1);
  if |batch| == 0 then
    ([state], [])
  else
    var (restStates, restReplies) := HandleRequestBatchHidden(state, batch[..|batch|-1]);
    var (new_state, reply) := AppHandleRequest(restStates[|restStates|-1], batch[|batch|-1].request);
    (restStates+[new_state], restReplies+[Reply(batch[|batch|-1].client, batch[|batch|-1].seqno, reply)])
}

lemma{:timeLimitMultiplier 2} lemma_HandleRequestBatchHidden(state:AppState, batch:RequestBatch, states:seq<AppState>, replies:seq<Reply>)
  requires (states, replies) == HandleRequestBatchHidden(state, batch);
  ensures  && states[0] == state
           && |states| == |batch|+1 
           && |replies| == |batch|
           && forall i :: 0 <= i < |batch| ==>
                    && replies[i].Reply? 
                    && ((states[i+1], replies[i].reply) == AppHandleRequest(states[i], batch[i].request))
                    && replies[i].client == batch[i].client
                    && replies[i].seqno == batch[i].seqno
  decreases |batch|
{
  reveal HandleRequestBatchHidden();
  if |batch| == 0 {
    assert && |states| == |batch|+1 
           && |replies| == |batch|
           && (forall i :: 0 <= i < |batch| ==> ((states[i+1], replies[i].reply) == AppHandleRequest(states[i], batch[i].request)));
  } else {
    var restBatch := HandleRequestBatchHidden(state, batch[..|batch|-1]);
    var restStates := restBatch.0;
    var AHR_result := AppHandleRequest(restStates[|restStates|-1], batch[|batch|-1].request);
    lemma_HandleRequestBatchHidden(state, batch[..|batch|-1], restStates, restBatch.1);
    assert replies[|batch|-1].reply == AHR_result.1;
  }
}

lemma lemma_HandleBatchRequestSizes(state:AppState, batch:RequestBatch, states:seq<AppState>, replies:seq<Reply>)
  requires (states, replies) == HandleRequestBatch(state, batch)
  ensures  states[0] == state
  ensures  |states| == |batch| + 1
  ensures  |replies| == |batch|
{
  assert states == HandleRequestBatchHidden(state, batch).0;         // OBSERVE
  assert replies == HandleRequestBatchHidden(state, batch).1;        // OBSERVE
  assert (states, replies) == HandleRequestBatchHidden(state, batch);
  lemma_HandleRequestBatchHidden(state, batch, states,replies);
}

lemma lemma_HandleBatchRequestProperties(state:AppState, batch:RequestBatch, states:seq<AppState>, replies:seq<Reply>, i:int)
  requires (states, replies) == HandleRequestBatch(state, batch)
  requires 0 <= i < |batch|
  ensures  states[0] == state
  ensures  |states| == |batch| + 1
  ensures  |replies| == |batch|
  ensures  replies[i].Reply?
  ensures  var (s, r) := AppHandleRequest(states[i], batch[i].request);
           s == states[i+1] && r == replies[i].reply
  //ensures  (states[i+1], replies[i]) == AppHandleRequest(states[i], batch[i].request)
  ensures  replies[i].client == batch[i].client
  ensures  replies[i].seqno == batch[i].seqno
{
  assert states == HandleRequestBatchHidden(state, batch).0;         // OBSERVE
  assert replies == HandleRequestBatchHidden(state, batch).1;        // OBSERVE
  assert (states, replies) == HandleRequestBatchHidden(state, batch);
  lemma_HandleRequestBatchHidden(state, batch, states,replies);
}

// TODO: The forall in the ensures should have an explicit trigger,
//       but the proof appears to be depending on the overly generous triggers in several places
lemma lemma_HandleRequestBatchTriggerHappy(state:AppState, batch:RequestBatch, states:seq<AppState>, replies:seq<Reply>)
  requires (states, replies) == HandleRequestBatch(state, batch);
  ensures  && states[0] == state
           && |states| == |batch|+1 
           && |replies| == |batch|
           && forall i :: 0 <= i < |batch| ==>
                    && replies[i].Reply? 
                    && ((states[i+1], replies[i].reply) == AppHandleRequest(states[i], batch[i].request))
                    && replies[i].client == batch[i].client
                    && replies[i].seqno == batch[i].seqno
{
  assert states == HandleRequestBatchHidden(state, batch).0;         // OBSERVE
  assert replies == HandleRequestBatchHidden(state, batch).1;        // OBSERVE
  assert (states, replies) == HandleRequestBatchHidden(state, batch);
  lemma_HandleRequestBatchHidden(state, batch, states, replies);
}

function HandleRequestBatch(state:AppState, batch:RequestBatch) : (seq<AppState>, seq<Reply>)
//  ensures var (states, replies) := HandleRequestBatch(state, batch); 
//          && states[0] == state
//          && |states| == |batch|+1 
//          && |replies| == |batch|
//          && (forall i :: 0 <= i < |batch| ==>
//                   && replies[i].Reply? 
//                   && ((states[i+1], replies[i].reply) == AppHandleRequest(states[i], batch[i].request))
//                   && replies[i].client == batch[i].client
//                   && replies[i].seqno == batch[i].seqno)
{
   var (states, replies) := HandleRequestBatchHidden(state, batch); 
   lemma_HandleRequestBatchHidden(state, batch, states, replies);
   (states, replies)
}

}
