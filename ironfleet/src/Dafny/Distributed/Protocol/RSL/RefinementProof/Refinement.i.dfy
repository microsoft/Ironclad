include "StateMachine.i.dfy"
include "HandleRequestBatch.i.dfy"
include "Chosen.i.dfy"
include "Execution.i.dfy"
include "Requests.i.dfy"
include "../DistributedSystem.i.dfy"
include "../CommonProof/Chosen.i.dfy"
include "../../../Common/Collections/Seqs.s.dfy"
    
module DirectRefinement__Refinement_i {

import opened DirectRefinement__StateMachine_i
import opened DirectRefinement__HandleRequestBatch_i
import opened DirectRefinement__Chosen_i
import opened DirectRefinement__Execution_i
import opened DirectRefinement__Requests_i
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__StateMachine_i
import opened LiveRSL__Types_i
import opened Concrete_NodeIdentity_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Chosen_i
import opened CommonProof__Constants_i
import opened Collections__Seqs_s
import opened Collections__Sets_i
import opened Collections__Maps2_s
import opened Temporal__Temporal_s
import opened AppStateMachine_i

function GetServerAddresses(ps:RslState):set<NodeIdentity>
{
  MapSeqToSet(ps.constants.config.replica_ids, x=>x)
}

function ProduceIntermediateAbstractState(server_addresses:set<NodeIdentity>, batches:seq<RequestBatch>, reqs_in_last_batch:int)
  :RSLSystemState
  requires |batches| > 0
  requires 0 <= reqs_in_last_batch <= |last(batches)|
{
  var requests := set batch_num, req_num | 0 <= batch_num < |batches| && 0 <= req_num < (if batch_num == |batches|-1 then reqs_in_last_batch else |batches[batch_num]|) :: batches[batch_num][req_num];
  var replies := set batch_num, req_num | 0 <= batch_num < |batches| && 0 <= req_num < (if batch_num == |batches|-1 then reqs_in_last_batch else |batches[batch_num]|) :: GetReplyFromRequestBatches(batches, batch_num, req_num);
  var stateBeforePrevBatch := GetAppStateFromRequestBatches(all_but_last(batches));
  var appStatesDuringBatch := HandleRequestBatch(stateBeforePrevBatch, last(batches)).0;
  RSLSystemState(server_addresses, appStatesDuringBatch[reqs_in_last_batch], requests, replies)
}

function ProduceAbstractState(server_addresses:set<NodeIdentity>, batches:seq<RequestBatch>):RSLSystemState
{
  var requests := set batch_num, req_num | 0 <= batch_num < |batches| && 0 <= req_num < |batches[batch_num]| :: batches[batch_num][req_num];
  var replies := set batch_num, req_num | 0 <= batch_num < |batches| && 0 <= req_num < |batches[batch_num]|
                                        :: GetReplyFromRequestBatches(batches, batch_num, req_num);
  RSLSystemState(server_addresses, GetAppStateFromRequestBatches(batches), requests, replies)
}

predicate SystemRefinementRelation(ps:RslState, rs:RSLSystemState)
{
  exists qs :: IsMaximalQuorumOf2bsSequence(ps, qs) && rs == ProduceAbstractState(GetServerAddresses(ps), GetSequenceOfRequestBatches(qs))
}

lemma lemma_ProduceAbstractStateSatisfiesRefinementRelation(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  qs:seq<QuorumOf2bs>,
  rs:RSLSystemState
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires IsMaximalQuorumOf2bsSequence(b[i], qs)
  requires rs == ProduceAbstractState(GetServerAddresses(b[i]), GetSequenceOfRequestBatches(qs))
  ensures  RslSystemRefinement(b[i], rs)
{
  var ps := b[i];
  var batches := GetSequenceOfRequestBatches(qs);

  lemma_ConstantsAllConsistent(b, c, i);
    
  forall p | p in ps.environment.sentPackets && p.src in rs.server_addresses && p.msg.RslMessage_Reply?
    ensures Reply(p.dst, p.msg.seqno_reply, p.msg.reply) in rs.replies
  {
    assert p.src in GetServerAddresses(ps);
    var qs', batches', batch_num, req_num := lemma_ReplySentIsAllowed(b, c, i, p);
    lemma_RegularQuorumOf2bSequenceIsPrefixOfMaximalQuorumOf2bSequence(b, c, i, qs', qs);
    lemma_GetReplyFromRequestBatchesMatchesInSubsequence(batches', batches, batch_num, req_num);
  }

  forall req | req in rs.requests
    ensures exists p :: && p in ps.environment.sentPackets
                  && p.dst in rs.server_addresses
                  && p.msg.RslMessage_Request?
                  && req == Request(p.src, p.msg.seqno_req, p.msg.val);
  {
    var batch_num, req_num :| 0 <= batch_num < |batches| && 0 <= req_num < |batches[batch_num]| && req == batches[batch_num][req_num];
    var p := lemma_DecidedRequestWasSentByClient(b, c, i, qs, batches, batch_num, req_num);
  }
}

lemma lemma_ProduceIntermediateAbstractStatesSatisfiesNext(
  server_addresses:set<NodeIdentity>,
  batches:seq<RequestBatch>,
  reqs_in_last_batch:int
  ) returns (
  request:Request
  )
  requires |batches| > 0
  requires 0 <= reqs_in_last_batch < |last(batches)|
  ensures  request == last(batches)[reqs_in_last_batch]
  ensures  RslSystemNextServerExecutesRequest(ProduceIntermediateAbstractState(server_addresses, batches, reqs_in_last_batch),
                                              ProduceIntermediateAbstractState(server_addresses, batches, reqs_in_last_batch+1), request)
{
  var rs := ProduceIntermediateAbstractState(server_addresses, batches, reqs_in_last_batch);
  var rs' := ProduceIntermediateAbstractState(server_addresses, batches, reqs_in_last_batch+1);

  request := last(batches)[reqs_in_last_batch];
  var reply := GetReplyFromRequestBatches(batches, |batches|-1, reqs_in_last_batch);

  assert rs'.requests == rs.requests + { request };
  assert rs'.replies == rs.replies + { reply };

  var stateBeforePrevBatch := GetAppStateFromRequestBatches(all_but_last(batches));
  var appStatesDuringBatch := HandleRequestBatch(stateBeforePrevBatch, last(batches)).0;
  var g_replies := HandleRequestBatch(stateBeforePrevBatch, last(batches)).1;
  lemma_HandleRequestBatchTriggerHappy(stateBeforePrevBatch, last(batches), appStatesDuringBatch, g_replies);
  var result := AppHandleRequest(rs.app, last(batches)[reqs_in_last_batch].request);
  assert rs'.app == result.0;
  assert reply.reply == result.1;

  assert RslSystemNextServerExecutesRequest(rs, rs', request);
}

lemma lemma_FirstProduceIntermediateAbstractStateProducesAbstractState(
  server_addresses:set<NodeIdentity>,
  batches:seq<RequestBatch>
  )
  requires |batches| > 0
  ensures  ProduceAbstractState(server_addresses, all_but_last(batches)) == ProduceIntermediateAbstractState(server_addresses, batches, 0)
{
  var rs := ProduceAbstractState(server_addresses, all_but_last(batches));
  var rs' := ProduceIntermediateAbstractState(server_addresses, batches, 0);

  var requests := set batch_num, req_num | 0 <= batch_num < |batches| && 0 <= req_num < (if batch_num == |batches|-1 then 0 else |batches[batch_num]|) :: batches[batch_num][req_num];
  var replies := set batch_num, req_num | 0 <= batch_num < |batches| && 0 <= req_num < (if batch_num == |batches|-1 then 0 else |batches[batch_num]|) :: GetReplyFromRequestBatches(batches, batch_num, req_num);
  var stateBeforePrevBatch := GetAppStateFromRequestBatches(all_but_last(batches));
  var appStatesDuringBatch := HandleRequestBatch(stateBeforePrevBatch, last(batches)).0;
  var replies' := HandleRequestBatch(stateBeforePrevBatch, last(batches)).1;
  lemma_HandleRequestBatchTriggerHappy(stateBeforePrevBatch, last(batches), appStatesDuringBatch, replies');

  forall req | req in rs'.requests
    ensures req in rs.requests
  {
    var batch_num, req_num :| && 0 <= batch_num < |batches|
                              && 0 <= req_num < (if batch_num == |batches|-1 then 0 else |batches[batch_num]|)
                              && req == batches[batch_num][req_num];
    assert 0 <= batch_num < |all_but_last(batches)|;
    assert 0 <= req_num < |batches[batch_num]|;
    assert 0 <= req_num < |all_but_last(batches)[batch_num]|;
  }

  assert rs'.requests == rs.requests;

  forall reply | reply in rs'.replies
    ensures reply in rs.replies
  {
    var batch_num, req_num :| && 0 <= batch_num < |batches|
                              && 0 <= req_num < (if batch_num == |batches|-1 then 0 else |batches[batch_num]|)
                              && reply == GetReplyFromRequestBatches(batches, batch_num, req_num);
    assert 0 <= batch_num < |all_but_last(batches)|;
    assert 0 <= req_num < |batches[batch_num]|;
    assert 0 <= req_num < |all_but_last(batches)[batch_num]|;
    lemma_GetReplyFromRequestBatchesMatchesInSubsequence(all_but_last(batches), batches, batch_num, req_num);
  }

  forall reply | reply in rs.replies
    ensures reply in rs'.replies
  {
    var batch_num, req_num :| && 0 <= batch_num < |all_but_last(batches)|
                              && 0 <= req_num < |batches[batch_num]|
                              && reply == GetReplyFromRequestBatches(all_but_last(batches), batch_num, req_num);
    lemma_GetReplyFromRequestBatchesMatchesInSubsequence(all_but_last(batches), batches, batch_num, req_num);
  }

  assert rs'.replies == rs.replies;
}

lemma lemma_LastProduceIntermediateAbstractStateProducesAbstractState(
  server_addresses:set<NodeIdentity>,
  batches:seq<RequestBatch>
  )
  requires |batches| > 0
  ensures  ProduceAbstractState(server_addresses, batches) == ProduceIntermediateAbstractState(server_addresses, batches, |last(batches)|)
{
  var rs := ProduceAbstractState(server_addresses, batches);
  var rs' := ProduceIntermediateAbstractState(server_addresses, batches, |last(batches)|);

  assert rs'.requests == rs.requests;

  forall reply | reply in rs'.replies
    ensures reply in rs.replies
  {
    var batch_num, req_num :| && 0 <= batch_num < |batches|
                              && 0 <= req_num < (if batch_num == |batches|-1 then |last(batches)| else |batches[batch_num]|)
                              && reply == GetReplyFromRequestBatches(batches, batch_num, req_num);
    assert 0 <= req_num < |batches[batch_num]|;
  }

  assert rs'.replies == rs.replies;
}

function {:opaque} ConvertBehaviorSeqToImap<T>(s:seq<T>):imap<int, T>
  requires |s| > 0
  ensures  imaptotal(ConvertBehaviorSeqToImap(s))
  ensures  forall i :: 0 <= i < |s| ==> ConvertBehaviorSeqToImap(s)[i] == s[i]
{
  imap i {:trigger s[i]} :: if i < 0 then s[0] else if 0 <= i < |s| then s[i] else last(s)
}

predicate RslSystemBehaviorRefinementCorrectImap(
  b:Behavior<RslState>,
  prefix_len:int,
  high_level_behavior:seq<RSLSystemState>
  )
{
  && imaptotal(b)
  && |high_level_behavior| == prefix_len
  && (forall i :: 0 <= i < prefix_len ==> RslSystemRefinement(b[i], high_level_behavior[i]))
  && |high_level_behavior| > 0
  && RslSystemInit(high_level_behavior[0], MapSeqToSet(b[0].constants.config.replica_ids, x=>x))
  && (forall i {:trigger RslSystemNext(high_level_behavior[i], high_level_behavior[i+1])} ::
         0 <= i < |high_level_behavior| - 1 ==> RslSystemNext(high_level_behavior[i], high_level_behavior[i+1]))
}

lemma lemma_GetBehaviorRefinementForBehaviorOfOneStep(
  b:Behavior<RslState>,
  c:LConstants
  ) returns (
  high_level_behavior:seq<RSLSystemState>
  )
  requires imaptotal(b)
  requires RslInit(c, b[0])
  ensures  RslSystemBehaviorRefinementCorrectImap(b, 1, high_level_behavior)
  ensures  |high_level_behavior| == 1
  ensures  SystemRefinementRelation(b[0], high_level_behavior[0])
{
  var qs := [];
  var rs := ProduceAbstractState(GetServerAddresses(b[0]), GetSequenceOfRequestBatches(qs));
  if exists q :: IsValidQuorumOf2bs(b[0], q) && q.opn == 0
  {
    var q :| IsValidQuorumOf2bs(b[0], q) && q.opn == 0;
    var idx :| idx in q.indices;
    var packet := q.packets[idx];
    assert false;
  }
  assert IsMaximalQuorumOf2bsSequence(b[0], qs);
  assert SystemRefinementRelation(b[0], rs);
  high_level_behavior := [ rs ];
}

lemma lemma_DemonstrateRslSystemNextWhenBatchExtended(
  server_addresses:set<NodeIdentity>,
  s:RSLSystemState,
  s':RSLSystemState,
  batches:seq<RequestBatch>,
  count:int
  ) returns (
  intermediate_states:seq<RSLSystemState>,
  batch:seq<Request>
  )
  requires |batches| > 0
  requires 0 <= count <= |last(batches)|
  requires s == ProduceIntermediateAbstractState(server_addresses, batches, 0)
  requires s' == ProduceIntermediateAbstractState(server_addresses, batches, count)
  ensures  RslStateSequenceReflectsBatchExecution(s, s', intermediate_states, batch)
  ensures  RslSystemNext(s, s')
  decreases count
{
  if count == 0 {
    assert s' == s;
    intermediate_states := [s];
    batch := [];
    assert RslStateSequenceReflectsBatchExecution(s, s', intermediate_states, batch);
    return;
  }

  var s_middle := ProduceIntermediateAbstractState(server_addresses, batches, count - 1);
  var intermediate_states_middle, batch_middle := lemma_DemonstrateRslSystemNextWhenBatchExtended(server_addresses, s, s_middle,
                                                                                                  batches, count - 1);

  intermediate_states := intermediate_states_middle + [s'];

  var next_request := lemma_ProduceIntermediateAbstractStatesSatisfiesNext(server_addresses, batches, count-1);
  batch := batch_middle + [next_request];
  assert RslSystemNextServerExecutesRequest(s_middle, s', next_request);
  assert RslStateSequenceReflectsBatchExecution(s, s', intermediate_states, batch);
}

lemma lemma_DemonstrateRslSystemNextWhenBatchesAdded(
  server_addresses:set<NodeIdentity>,
  s:RSLSystemState,
  s':RSLSystemState,
  batches:seq<RequestBatch>,
  batches':seq<RequestBatch>
  ) returns (
  intermediate_states:seq<RSLSystemState>,
  batch:seq<Request>
  )
  requires s == ProduceAbstractState(server_addresses, batches)
  requires s' == ProduceAbstractState(server_addresses, batches')
  requires |batches| <= |batches'|
  requires batches'[..|batches|] == batches
  ensures  RslStateSequenceReflectsBatchExecution(s, s', intermediate_states, batch)
  ensures  RslSystemNext(s, s')
  decreases |batches'|
{
  if |batches| == |batches'| {
    assert batches' == batches;
    assert s == s';
    intermediate_states := [s];
    batch := [];
    assert RslStateSequenceReflectsBatchExecution(s, s', intermediate_states, batch);
    return;
  }

  var s_middle := ProduceAbstractState(server_addresses, all_but_last(batches'));
  var intermediate_states_middle, batch_middle := lemma_DemonstrateRslSystemNextWhenBatchesAdded(server_addresses, s, s_middle,
                                                                                                   batches, all_but_last(batches'));
  lemma_FirstProduceIntermediateAbstractStateProducesAbstractState(server_addresses, batches');
  lemma_LastProduceIntermediateAbstractStateProducesAbstractState(server_addresses, batches');
  var intermediate_states_next, batch_next := lemma_DemonstrateRslSystemNextWhenBatchExtended(server_addresses, s_middle, s', batches',
                                                                                              |last(batches')|);
  intermediate_states := all_but_last(intermediate_states_middle) + intermediate_states_next;
  batch := batch_middle + batch_next;
  assert RslStateSequenceReflectsBatchExecution(s, s', intermediate_states, batch);
}

lemma lemma_GetBehaviorRefinementForPrefix(
  b:Behavior<RslState>,
  c:LConstants,
  i:int
  ) returns (
  high_level_behavior:seq<RSLSystemState>
  )
  requires 0 <= i
  requires IsValidBehaviorPrefix(b, c, i)
  ensures  RslSystemBehaviorRefinementCorrectImap(b, i+1, high_level_behavior)
  ensures  SystemRefinementRelation(b[i], last(high_level_behavior))
{
  if i == 0
  {
    high_level_behavior := lemma_GetBehaviorRefinementForBehaviorOfOneStep(b, c);
    return;
  }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  assert GetServerAddresses(b[i-1]) == GetServerAddresses(b[i]);
  var server_addresses := GetServerAddresses(b[i-1]);

  var prev_high_level_behavior := lemma_GetBehaviorRefinementForPrefix(b, c, i-1);
  var prev_rs := last(prev_high_level_behavior);
  var prev_qs :| && IsMaximalQuorumOf2bsSequence(b[i-1], prev_qs)
                 && prev_rs == ProduceAbstractState(server_addresses, GetSequenceOfRequestBatches(prev_qs));
  var prev_batches := GetSequenceOfRequestBatches(prev_qs);

  var qs := lemma_GetMaximalQuorumOf2bsSequence(b, c, i);
  var batches := GetSequenceOfRequestBatches(qs);

  lemma_IfValidQuorumOf2bsSequenceNowThenNext(b, c, i-1, prev_qs);
  lemma_RegularQuorumOf2bSequenceIsPrefixOfMaximalQuorumOf2bSequence(b, c, i, prev_qs, qs);

  var s' := ProduceAbstractState(server_addresses, batches);
  var intermediate_states, batch := lemma_DemonstrateRslSystemNextWhenBatchesAdded(server_addresses, last(prev_high_level_behavior),
                                                                                   s', prev_batches, batches);

  high_level_behavior := prev_high_level_behavior + [s'];
    
  lemma_ProduceAbstractStateSatisfiesRefinementRelation(b, c, i, qs, last(high_level_behavior));
  assert RslSystemRefinement(b[i], last(high_level_behavior));
}

lemma lemma_GetBehaviorRefinement(
  low_level_behavior:seq<RslState>,
  c:LConstants
  ) returns (
  high_level_behavior:seq<RSLSystemState>
  )
  requires |low_level_behavior| > 0
  requires RslInit(c, low_level_behavior[0])
  requires forall i {:trigger RslNext(low_level_behavior[i], low_level_behavior[i+1])} ::
             0 <= i < |low_level_behavior| - 1 ==> RslNext(low_level_behavior[i], low_level_behavior[i+1])
  ensures  RslSystemBehaviorRefinementCorrect(MapSeqToSet(c.config.replica_ids, x=>x), low_level_behavior, high_level_behavior)
{
  var b := ConvertBehaviorSeqToImap(low_level_behavior);
  high_level_behavior := lemma_GetBehaviorRefinementForPrefix(b, c, |low_level_behavior|-1);
}

}
