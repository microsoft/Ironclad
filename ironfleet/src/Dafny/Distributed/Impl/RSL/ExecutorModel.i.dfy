include "AppInterface.i.dfy"
include "ExecutorState.i.dfy"
include "Broadcast.i.dfy"
include "../Common/Util.i.dfy"
include "../../Common/Native/IoLemmas.i.dfy"

module LiveRSL__ExecutorModel_i {
import opened Native__Io_s
import opened Native__IoLemmas_i
import opened Native__NativeTypes_s
import opened LiveRSL__AppInterface_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Executor_i
import opened LiveRSL__ExecutorState_i
import opened LiveRSL__Message_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__ReplicaConstantsState_i
import opened LiveRSL__StateMachine_i
import opened LiveRSL__Types_i
import opened Impl__LiveRSL__Broadcast_i
import opened Common__NodeIdentity_i
import opened Common__NetClient_i
import opened Common__UpperBound_s
import opened Common__UpperBound_i
import opened Common__Util_i
import opened Concrete_NodeIdentity_i
import opened Collections__Maps_i
import opened Logic__Option_i
import opened Environment_s
import opened AppStateMachine_s
import opened Temporal__Temporal_s

predicate ClientIndexMatches(req_idx:int, client:EndPoint, newReplyCache:CReplyCache, batch:CRequestBatch, replies:seq<CReply>) 
  requires |batch| == |replies|
  requires client in newReplyCache
{
  0 <= req_idx < |batch| && replies[req_idx].client == client && newReplyCache[client] == replies[req_idx] 
}

predicate ReplyCacheUpdated(client:EndPoint, oldReplyCache:CReplyCache, newReplyCache:CReplyCache, batch:CRequestBatch, replies:seq<CReply>) 
  requires client in newReplyCache
  requires |batch| == |replies|
{
  || (client in oldReplyCache && newReplyCache[client] == oldReplyCache[client])
  || (exists req_idx :: ClientIndexMatches(req_idx, client, newReplyCache, batch, replies))
}

lemma lemma_CReplyCacheUpdate(batch:CRequestBatch, reply_cache:CReplyCache, replies:seq<CReply>, newReplyCache:CReplyCache) 
  requires |batch| == |replies|
  requires ValidReplyCache(reply_cache)
  requires ValidReplyCache(newReplyCache)
  requires CReplyCacheIsAbstractable(reply_cache)
  requires CReplyCacheIsAbstractable(newReplyCache)
  requires CReplySeqIsAbstractable(replies);
  requires forall client :: client in newReplyCache ==> ReplyCacheUpdated(client, reply_cache, newReplyCache, batch, replies)
  ensures  var r_newReplyCache := AbstractifyCReplyCacheToReplyCache(newReplyCache);
           var r_replyCache := AbstractifyCReplyCacheToReplyCache(reply_cache);
           forall client :: client in r_newReplyCache ==> 
                   (|| (client in r_replyCache && r_newReplyCache[client] == r_replyCache[client])
                    || ExistsReqIdx(|batch|, replies, reply_cache, newReplyCache, client))
{
  ghost var r_newReplyCache := AbstractifyCReplyCacheToReplyCache(newReplyCache);
  ghost var r_replyCache    := AbstractifyCReplyCacheToReplyCache(reply_cache);
  forall r_client | r_client in r_newReplyCache 
    ensures || (r_client in r_replyCache && r_newReplyCache[r_client] == r_replyCache[r_client])
            || ExistsReqIdx(|batch|, replies, reply_cache, newReplyCache, r_client)
  {
    lemma_AbstractifyCReplyCacheToReplyCache_properties(reply_cache);
    lemma_AbstractifyCReplyCacheToReplyCache_properties(newReplyCache);
    assert exists e :: e in newReplyCache && r_client == AbstractifyEndPointToNodeIdentity(e);
    var client :| client in newReplyCache && AbstractifyEndPointToNodeIdentity(client) == r_client;
    assert EndPointIsValidPublicKey(client);
    if client in reply_cache && newReplyCache[client] == reply_cache[client] {
      lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
      assert r_client in r_replyCache;
      calc {
        r_newReplyCache[r_client];
        AbstractifyCReplyToReply(newReplyCache[client]);
        AbstractifyCReplyToReply(reply_cache[client]);
        r_replyCache[r_client];
      }
    } else {
      lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
      ghost var req_idx :| ClientIndexMatches(req_idx, client, newReplyCache, batch, replies);
      assert 0 <= req_idx < |batch| && AbstractifyCReplySeqToReplySeq(replies)[req_idx].client == r_client && r_newReplyCache[r_client] == AbstractifyCReplySeqToReplySeq(replies)[req_idx];
      assert ExistsReqIdx(|batch|, replies, reply_cache, newReplyCache, r_client);
    }
  }
}

method {:timeLimitMultiplier 2} HandleRequestBatchImpl(
  state:AppStateMachine,
  batch:CRequestBatch,
  ghost reply_cache:CReplyCache,
  reply_cache_mutable:MutableMap<EndPoint, CReply>
  ) returns (
  replies_seq:seq<CReply>,
  ghost newReplyCache:CReplyCache,
  ghost g_states:seq<AppState>,
  ghost g_replies:seq<Reply>
  )
  requires ValidReplyCache(reply_cache)
  requires ValidRequestBatch(batch)
  requires CReplyCacheIsAbstractable(reply_cache)
  requires forall req :: req in batch ==> EndPointIsValidPublicKey(req.client)
  requires MutableMap.MapOf(reply_cache_mutable) == reply_cache
  modifies reply_cache_mutable
  modifies state
  ensures (g_states, g_replies) == HandleRequestBatch(old(state.Abstractify()), AbstractifyCRequestBatchToRequestBatch(batch));
  ensures |replies_seq| == |batch|
  ensures forall i :: 0 <= i < |batch| ==> HelperPredicateHRBI(i, batch, replies_seq, g_states)
  ensures g_states[0] == old(state.Abstractify())
  ensures g_states[|g_states|-1] == state.Abstractify()
  ensures CReplySeqIsAbstractable(replies_seq)
  ensures AbstractifyCReplySeqToReplySeq(replies_seq) == g_replies
  ensures ValidReplyCache(newReplyCache)
  ensures CReplyCacheIsAbstractable(newReplyCache)
  ensures forall client :: client in newReplyCache ==> ReplyCacheUpdated(client, reply_cache, newReplyCache, batch, replies_seq);
  ensures var r_newReplyCache := AbstractifyCReplyCacheToReplyCache(newReplyCache);
          var r_replyCache := AbstractifyCReplyCacheToReplyCache(reply_cache);
          forall client :: client in r_newReplyCache ==> 
                   (|| (client in r_replyCache && r_newReplyCache[client] == r_replyCache[client])
                    || ExistsReqIdx(|batch|, replies_seq, reply_cache, newReplyCache, client))
  ensures newReplyCache == MutableMap.MapOf(reply_cache_mutable);
  ensures forall r :: r in replies_seq ==> ValidReply(r) && CReplyIsAbstractable(r)
{
  ghost var g_state0 := state.Abstractify();
  ghost var g_batch := AbstractifyCRequestBatchToRequestBatch(batch);
  ghost var tuple := HandleRequestBatch(g_state0, g_batch);
  g_states := tuple.0;
  g_replies := tuple.1;

  assert tuple == HandleRequestBatchHidden(g_state0, g_batch);
  lemma_HandleRequestBatchHidden(g_state0, g_batch, g_states, g_replies);
    
  var i:uint64 := 0;
  ghost var replies := [];
  var repliesArr := new CReply[|batch| as uint64];
  newReplyCache := reply_cache;
    
  while i < |batch| as uint64
    invariant 0 <= i as int <= |batch|
    invariant |replies| == i as int
    invariant forall j :: 0 <= j < i as int ==> HelperPredicateHRBI(j, batch, replies, g_states)
    invariant ValidReplyCache(newReplyCache)
    invariant CReplyCacheIsAbstractable(newReplyCache)
    invariant forall r :: r in replies ==> ValidReply(r) && CReplyIsAbstractable(r)
    invariant AbstractifyCReplySeqToReplySeq(replies) == g_replies[..i]
    invariant repliesArr[..i] == replies
    invariant g_states[0] == g_state0
    invariant g_states[i] == state.Abstractify()
    invariant forall client {:trigger ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies)} :: 
                    client in newReplyCache ==> ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies)
    invariant MutableMap.MapOf(reply_cache_mutable) == newReplyCache
  {
    ghost var old_replies := replies;
    ghost var old_newReplyCache := newReplyCache;

    var old_state := state.Abstractify();
    var reply := state.HandleRequest(batch[i].request);
    var newReply := CReply(batch[i].client, batch[i].seqno, reply);
    assert ValidReply(newReply);

    replies := replies + [newReply];
    repliesArr[i] := newReply;
    newReplyCache := UpdateReplyCache(newReplyCache, reply_cache_mutable, batch[i].client, newReply, reply, i, batch, replies);
    i := i + 1;
        
    // Prove the invariant about HelperPredicateHRBI(j, batch, states, replies, g_states)
    forall j | 0 <= j < i as int 
      ensures HelperPredicateHRBI(j, batch, replies, g_states)
    {
      if j < (i as int) - 1 {
        assert HelperPredicateHRBI(j, batch, old_replies, g_states);    // From the loop invariant
        assert HelperPredicateHRBI(j, batch, replies, g_states);
      }
    }

    // Prove: AbstractifyCReplySeqToReplySeq(replies) == g_replies_prefix;
    ghost var g_replies_prefix := g_replies[..i];
    forall k | 0 <= k < |replies|
      ensures AbstractifyCReplySeqToReplySeq(replies)[k] == g_replies_prefix[k]
    {
      if k < |replies| - 1 {
        assert AbstractifyCReplySeqToReplySeq(old_replies) == g_replies[..i-1];
      } else {
        assert k == (i as int) - 1;
        ghost var reply' := AppHandleRequest(g_states[i-1], AbstractifyCAppRequestToAppRequest(batch[i-1].request)).1;
        calc {
          AbstractifyCReplySeqToReplySeq(replies)[k];
          AbstractifyCReplyToReply(replies[k]);
          Reply(AbstractifyEndPointToNodeIdentity(batch[i-1].client), batch[i-1].seqno as int, reply');
          Reply(g_batch[i-1].client, g_batch[i-1].seqno, 
                AppHandleRequest(g_states[i-1], g_batch[i-1].request).1);
            { lemma_HandleBatchRequestProperties(g_state0, g_batch, g_states, g_replies, (i as int)-1); } 
          g_replies_prefix[k];
        }
      }
    }
    assert AbstractifyCReplySeqToReplySeq(replies) == g_replies_prefix;

    // Prove the invariant about cache updates
    forall client | client in newReplyCache
      ensures ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies)
    {
      assert ReplyCacheUpdated(client, old_newReplyCache, newReplyCache, batch[..i], replies);
      assert || (client in old_newReplyCache && newReplyCache[client] == old_newReplyCache[client])
             || (exists req_idx :: ClientIndexMatches(req_idx, client, newReplyCache, batch[..i], replies));

      if client in old_newReplyCache {
        assert ReplyCacheUpdated(client, reply_cache, old_newReplyCache, batch[..i-1], old_replies);
//        assert || (client in reply_cache && old_newReplyCache[client] == reply_cache[client])
//               || (exists req_idx :: ClientIndexMatches(req_idx, client, old_newReplyCache, batch[..i-1], old_replies));
        if client in reply_cache && old_newReplyCache[client] == reply_cache[client] {
          if client in old_newReplyCache && newReplyCache[client] == old_newReplyCache[client] {
            assert client in reply_cache && newReplyCache[client] == reply_cache[client];
            assert ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies);
          } else {
            ghost var req_idx :| ClientIndexMatches(req_idx, client, newReplyCache, batch[..i], replies);
            assert ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies);
          }
        } else {
          ghost var req_idx :| ClientIndexMatches(req_idx, client, old_newReplyCache, batch[..i-1], old_replies);
          assert && 0 <= req_idx < |batch[..i-1]| 
                 && replies[req_idx].client == client 
                 && old_newReplyCache[client] == replies[req_idx];
          if client in old_newReplyCache && newReplyCache[client] == old_newReplyCache[client] {
            assert ClientIndexMatches(req_idx, client, newReplyCache, batch[..i], replies);
          } else {
            ghost var req_idx' :| ClientIndexMatches(req_idx', client, newReplyCache, batch[..i], replies);
          }
          assert ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies);
        }
      }

      assert || (client in reply_cache && newReplyCache[client] == reply_cache[client])
             || (exists req_idx :: ClientIndexMatches(req_idx, client, newReplyCache, batch[..i], replies));
    }
  }
    
  replies_seq := repliesArr[..];
    
  // Connect the while-loop invariant to the ensures
  forall client | client in newReplyCache
    ensures replies_seq == replies
    ensures ReplyCacheUpdated(client, reply_cache, newReplyCache, batch, replies)
  {
    assert ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies);
    assert i as int == |batch|;
    assert batch[..i] == batch;
  }
    
  assert replies_seq == replies;
  assert forall j :: 0 <= j < |batch| ==> j < |replies_seq| && HelperPredicateHRBI(j, batch, replies_seq, g_states);

  lemma_CReplyCacheUpdate(batch, reply_cache, replies, newReplyCache);
}

method {:timeLimitMultiplier 6} UpdateReplyCache(ghost reply_cache:CReplyCache, reply_cache_mutable:MutableMap<EndPoint, CReply>, ep:EndPoint, newReply:CReply, reply:CAppReply, i:uint64, batch:CRequestBatch, ghost replies:seq<CReply>) returns (ghost newReplyCache:CReplyCache)
  requires EndPointIsValidPublicKey(ep)
  requires ValidReply(newReply)
  requires CReplyIsAbstractable(newReply)
  requires 0 <= i as int < |batch|
  requires |replies| == |batch[..(i as int)+1]|
  requires replies[i] == newReply
  requires newReply.client == ep
  requires ValidReplyCache(reply_cache)
  requires CReplyCacheIsAbstractable(reply_cache)
  requires forall r :: r in replies ==> CReplyIsAbstractable(r)
  requires newReply == CReply(batch[i].client, batch[i].seqno, reply)
  requires MutableMap.MapOf(reply_cache_mutable) == reply_cache
  modifies reply_cache_mutable
  ensures ValidReplyCache(newReplyCache)
  ensures CReplyCacheIsAbstractable(newReplyCache)
  ensures forall client :: client in newReplyCache ==> ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..(i as int)+1], replies)
  ensures forall client :: client in newReplyCache ==> (|| (client in reply_cache && newReplyCache[client] == reply_cache[client])
                                                 || ExistsReqIdxConcrete((i as int)+1, replies, reply_cache, newReplyCache, client))
  ensures var r_newReplyCache := AbstractifyCReplyCacheToReplyCache(newReplyCache);
          var r_replyCache := AbstractifyCReplyCacheToReplyCache(reply_cache);
          forall client :: client in r_newReplyCache ==> (|| (client in r_replyCache && r_newReplyCache[client] == r_replyCache[client])
                                                   || ExistsReqIdx((i as int)+1, replies, reply_cache, newReplyCache, client))
  ensures newReplyCache == MutableMap.MapOf(reply_cache_mutable)
{
  lemma_AbstractifyCReplyCacheToReplyCache_properties(reply_cache);
  ghost var slimReplyCache:CReplyCache;
  var staleEntry;
  var cache_size := reply_cache_mutable.SizeModest();
  if cache_size == 255 as uint64 {    // max_reply_cache_size()
    staleEntry :| staleEntry in MutableMap.MapOf(reply_cache_mutable);      // TODO: Choose based on age // TODO: This is very inefficient.  Optimize value selection.
    slimReplyCache := RemoveElt(reply_cache, staleEntry);
    reply_cache_mutable.Remove(staleEntry);
  } else {
    slimReplyCache := reply_cache;
  }
  lemma_AbstractifyCReplyCacheToReplyCache_properties(slimReplyCache);
  assert ValidReplyCache(slimReplyCache);
  forall e {:trigger EndPointIsValidPublicKey(e)} | e in slimReplyCache 
    ensures EndPointIsValidPublicKey(e) && CReplyIsAbstractable(slimReplyCache[e])
  {
  }
  newReplyCache := slimReplyCache[ep := newReply];
  reply_cache_mutable.Set(ep, newReply);
  forall e {:trigger EndPointIsValidPublicKey(e)} | e in newReplyCache 
    ensures EndPointIsValidPublicKey(e) && CReplyIsAbstractable(newReplyCache[e])
  {
    if (e == ep) {

    }
  }
//  assert forall e {:trigger EndPointIsValidPublicKey(e)} :: e in newReplyCache ==> EndPointIsValidPublicKey(e) && CReplyIsAbstractable(newReplyCache[e]);
  assert CReplyCacheIsAbstractable(newReplyCache);
  lemma_AbstractifyCReplyCacheToReplyCache_properties(newReplyCache);
  assert ep in newReplyCache;
  assert EndPointIsValidPublicKey(ep);
  assert CReplyCacheIsAbstractable(newReplyCache);
  assert ValidReplyCache(newReplyCache);
  ghost var r_newReplyCache := AbstractifyCReplyCacheToReplyCache(newReplyCache);
  ghost var r_replyCache := AbstractifyCReplyCacheToReplyCache(reply_cache);
  forall client | client in r_newReplyCache
    ensures || (client in r_replyCache && r_newReplyCache[client] == r_replyCache[client])
            || ExistsReqIdx((i as int)+1, replies, reply_cache, newReplyCache, client)
    ensures ReplyCacheUpdated(RefineNodeIdentityToEndPoint(client), reply_cache, newReplyCache, batch[..i+1], replies)
  {
    var e := RefineNodeIdentityToEndPoint(client);
    if e == ep {
      assert AbstractifyCReplySeqToReplySeq(replies)[i].client == AbstractifyCReplyToReply(replies[i]).client;
      assert AbstractifyCReplySeqToReplySeq(replies)[i].client == client && r_newReplyCache[client] == AbstractifyCReplySeqToReplySeq(replies)[i];
      assert ExistsReqIdx((i as int)+1, replies, reply_cache, newReplyCache, client);
      assert ClientIndexMatches(i as int, e, newReplyCache, batch[..(i as int)+1], replies);
      assert ReplyCacheUpdated(RefineNodeIdentityToEndPoint(client), reply_cache, newReplyCache, batch[..(i as int)+1], replies);
    } else {
      assert e in reply_cache;
      if e == staleEntry && |reply_cache| == 0x1_0000_0000 - 1 {
        assert e !in slimReplyCache;
                
        assert e !in newReplyCache;
        assert AbstractifyEndPointToNodeIdentity(e) !in r_newReplyCache;
        assert false;
      } else {
        assert e in slimReplyCache;
      }
      assert e in slimReplyCache;
      
      assert newReplyCache[e] == reply_cache[e];
      assert AbstractifyCReplyCacheToReplyCache(newReplyCache)[AbstractifyEndPointToNodeIdentity(e)] == AbstractifyCReplyToReply(newReplyCache[e]);
      assert AbstractifyCReplyCacheToReplyCache(reply_cache)[AbstractifyEndPointToNodeIdentity(e)] == AbstractifyCReplyToReply(reply_cache[e]);
      assert ReplyCacheUpdated(RefineNodeIdentityToEndPoint(client), reply_cache, newReplyCache, batch[..(i as int)+1], replies);
    }
  }

  forall client | client in newReplyCache 
    ensures ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i+1], replies)
  {
    assert EndPointIsValidPublicKey(client); // OBSERVE: Needed b/c someone put an oddly strict trigger on lemma_AbstractifyCReplyCacheToReplyCache_properties
    lemma_AbstractifyCReplyCacheToReplyCache_properties(newReplyCache);
    assert AbstractifyEndPointToNodeIdentity(client) in r_newReplyCache;
    lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
    assert client == RefineNodeIdentityToEndPoint(AbstractifyEndPointToNodeIdentity(client));
  }
}

lemma lemma_HelperPredicateHRBI(j:int, batch:CRequestBatch, replies:seq<CReply>, g_states:seq<AppState>)
  requires 0 <= j < |batch|
  requires 0 <= j < |g_states|-1
  requires 0 <= j < |replies|
  requires HelperPredicateHRBI(j, batch, replies, g_states)
  ensures  replies[j].CReply?
  ensures  (g_states[j+1], AbstractifyCAppReplyToAppReply(replies[j].reply)) == AppHandleRequest(g_states[j], AbstractifyCAppRequestToAppRequest(batch[j].request))
  ensures  replies[j].client == batch[j].client
  ensures  replies[j].seqno == batch[j].seqno
{
}

predicate HelperPredicateHRBI(j:int, batch:CRequestBatch, replies:seq<CReply>, g_states:seq<AppState>)
  requires 0 <= j < |batch|
  requires 0 <= j < |g_states|-1
  requires 0 <= j < |replies|
{
  && replies[j].CReply?
  && ((g_states[j+1], AbstractifyCAppReplyToAppReply(replies[j].reply)) == AppHandleRequest(g_states[j], AbstractifyCAppRequestToAppRequest(batch[j].request)))
  && replies[j].client == batch[j].client
  && replies[j].seqno == batch[j].seqno
}

// Same as x == y, but triggers extensional equality on fields and provides better error diagnostics
predicate Eq_ExecutorState(x:LExecutor, y:LExecutor)
{
  && x.constants == y.constants
  && x.app == y.app
  && x.ops_complete == y.ops_complete
  && x.next_op_to_execute == y.next_op_to_execute
}

method ExecutorInit(ccons:ReplicaConstantsState) returns(cs:ExecutorState, reply_cache_mutable:MutableMap<EndPoint, CReply>)
  requires ReplicaConstantsState_IsValid(ccons)
  ensures  ExecutorState_IsValid(cs)
  ensures  LExecutorInit(AbstractifyExecutorStateToLExecutor(cs), AbstractifyReplicaConstantsStateToLReplicaConstants(ccons))
  ensures  cs.constants == ccons
  ensures  fresh(reply_cache_mutable)
  ensures  cs.reply_cache == MutableMap.MapOf(reply_cache_mutable)
{
  ghost var c := AbstractifyReplicaConstantsStateToLReplicaConstants(ccons);
  ghost var s := LExecutor(
    c,
    AppInitialize(),
    0,
    Ballot(0, 0),
    OutstandingOpUnknown(),
    map[]);
  var app_state := AppStateMachine.Initialize();
  cs := ExecutorState(
    ccons,
    app_state,
    COperationNumber(0),
    CBallot(0, 0),
    COutstandingOpUnknown(),
    map[]);
  reply_cache_mutable := MutableMap.EmptyMap();

  lemma_AbstractifyCReplyCacheToReplyCache_properties(cs.reply_cache);
  assert Eq_ExecutorState(s, AbstractifyExecutorStateToLExecutor(cs));
}

method ExecutorGetDecision(cs:ExecutorState, cbal:CBallot, copn:COperationNumber, ca:CRequestBatch) returns(cs':ExecutorState)
  requires ExecutorState_IsValid(cs)
  requires ValidRequestBatch(ca)
  requires CBallotIsAbstractable(cbal)
  requires copn == cs.ops_complete
  requires cs.next_op_to_execute.COutstandingOpUnknown?
  ensures  ExecutorState_IsValid(cs')
  ensures  LExecutorGetDecision(AbstractifyExecutorStateToLExecutor(cs), AbstractifyExecutorStateToLExecutor(cs'), AbstractifyCBallotToBallot(cbal), AbstractifyCOperationNumberToOperationNumber(copn), AbstractifyCRequestBatchToRequestBatch(ca))
  ensures  cs.constants == cs'.constants
  ensures  cs'.reply_cache == cs.reply_cache
{
  ghost var s := AbstractifyExecutorStateToLExecutor(cs);
  ghost var v := AbstractifyCRequestBatchToRequestBatch(ca);
  ghost var opn := AbstractifyCOperationNumberToOperationNumber(copn);
  ghost var bal := AbstractifyCBallotToBallot(cbal);
  ghost var s' := s.(next_op_to_execute := OutstandingOpKnown(v, bal));
  cs' := cs.(next_op_to_execute := COutstandingOpKnown(ca, cbal));

  assert Eq_ExecutorState(s', AbstractifyExecutorStateToLExecutor(cs'));
}

predicate ExistsReqIdx(len:int, replies:seq<CReply>, reply_cache:CReplyCache, newReplyCache:CReplyCache, client:NodeIdentity)
  requires CReplyCacheIsAbstractable(reply_cache)
  requires CReplyCacheIsAbstractable(newReplyCache)
  requires client in AbstractifyCReplyCacheToReplyCache(newReplyCache)
  requires |replies| == len
  requires (forall i :: i in replies ==> CReplyIsAbstractable(i))
{
  var r_newReplyCache := AbstractifyCReplyCacheToReplyCache(newReplyCache);
  var r_replyCache := AbstractifyCReplyCacheToReplyCache(reply_cache );
  exists req_idx :: 0 <= req_idx < len && AbstractifyCReplySeqToReplySeq(replies)[req_idx].client == client && r_newReplyCache[client] == AbstractifyCReplySeqToReplySeq(replies)[req_idx]
}

predicate ExistsReqIdxConcrete(len:int, replies:seq<CReply>, reply_cache:CReplyCache, newReplyCache:CReplyCache, client:EndPoint)
  requires client in newReplyCache
  requires |replies| == len
  requires (forall i :: i in replies ==> CReplyIsAbstractable(i))
{
  exists req_idx :: 0 <= req_idx < len && replies[req_idx].client == client && newReplyCache[client] == replies[req_idx]
}

/*
lemma lemma_BatchEquivalence(cv:CRequestBatch, cstates:seq<CAppState>, creplies:seq<CReply>, v:RequestBatch, states:seq<AppState>, replies:seq<Reply>)
  requires var temp := HandleRequestBatch(s.app, v)
{

}
*/

lemma lemma_ExistsReqIdx(len:int, replies:seq<CReply>, reply_cache:CReplyCache, newReplyCache:CReplyCache, client:NodeIdentity)
  requires CReplyCacheIsAbstractable(reply_cache)
  requires CReplyCacheIsAbstractable(newReplyCache)
  requires client in AbstractifyCReplyCacheToReplyCache(newReplyCache)
  requires |replies| == len
  requires (forall i :: i in replies ==> CReplyIsAbstractable(i))
  requires ExistsReqIdx(len, replies, reply_cache, newReplyCache, client)
  ensures exists req_idx :: 0 <= req_idx < len && AbstractifyCReplySeqToReplySeq(replies)[req_idx].client == client && AbstractifyCReplyCacheToReplyCache(newReplyCache)[client] == AbstractifyCReplySeqToReplySeq(replies)[req_idx]
{
}


method GetPacketsFromRepliesImpl(me:EndPoint, requests:CRequestBatch, replies:seq<CReply>) returns (cout_seq:seq<CPacket>)
  requires |requests| == |replies| < 0x1_0000_0000_0000_0000
  requires forall r :: r in requests ==> ValidRequest(r)
  requires forall r :: r in replies ==> ValidReply(r) && CReplyIsAbstractable(r)
  requires EndPointIsValidPublicKey(me)
  ensures CPacketSeqIsAbstractable(cout_seq)
  ensures |cout_seq| == |replies|
  ensures  forall p :: p in cout_seq ==> p.src == me && p.msg.CMessage_Reply? && CPacketIsSendable(p)
  ensures AbstractifySeqOfCPacketsToSeqOfRslPackets(cout_seq) == GetPacketsFromReplies(AbstractifyEndPointToNodeIdentity(me), AbstractifyCRequestsSeqToRequestsSeq(requests), AbstractifyCReplySeqToReplySeq(replies))
{
  var i:uint64 := 0;
  ghost var cout := [];
  var coutArr := new CPacket[|replies| as uint64];

  while i < |replies| as uint64 
    invariant 0 <= i as int <= |replies|
    invariant |cout| == i as int
    invariant coutArr[..i] == cout
    invariant CPacketSeqIsAbstractable(cout)
    invariant forall p :: p in cout ==> p.src == me && p.msg.CMessage_Reply? && CPacketIsSendable(p)
    invariant forall j :: 0 <= j < i ==> cout[j] == CPacket(requests[j].client, me, CMessage_Reply(requests[j].seqno, replies[j].reply))
  {
    assert ValidRequest(requests[i]) && ValidReply(replies[i]);
    var cmsg := CMessage_Reply(requests[i].seqno, replies[i].reply);
    if PrintParams.ShouldPrintProgress() {
      print("Sending reply to client ");
      print(requests[i].client);
      print(" with sequence number ");
      print(requests[i].seqno);
      print("\n");
    }
    var cp := CPacket(requests[i].client, me, cmsg);
    cout := cout + [cp];
    coutArr[i] := cp;
    i := i + 1;
  }

  // Prove the final ensures clause
  ghost var r_cout := AbstractifySeqOfCPacketsToSeqOfRslPackets(cout);
  ghost var r_me := AbstractifyEndPointToNodeIdentity(me);
  ghost var r_requests := AbstractifyCRequestsSeqToRequestsSeq(requests);
  ghost var r_replies := AbstractifyCReplySeqToReplySeq(replies);
  ghost var r_cout' := GetPacketsFromReplies(r_me, r_requests, r_replies);

  calc {
    |r_cout|;
    |cout|;
    |replies|;
    |AbstractifyCReplySeqToReplySeq(replies)|;
      { lemma_SizeOfGetPacketsFromReplies(r_me, r_requests, r_replies, r_cout'); }
    |r_cout'|;
  }
  forall j | 0 <= j < |r_cout| 
    ensures r_cout[j] == r_cout'[j]
  {
    calc {
      r_cout[j];
      AbstractifyCPacketToRslPacket(cout[j]);
      AbstractifyCPacketToRslPacket(CPacket(requests[j].client, me, CMessage_Reply(requests[j].seqno, replies[j].reply)));
      LPacket(r_requests[j].client, r_me, RslMessage_Reply(r_requests[j].seqno, r_replies[j].reply));
        { lemma_SpecificPacketInGetPacketsFromReplies(r_me, r_requests, r_replies, r_cout', j); }
      r_cout'[j];
    }
  }
  cout_seq := coutArr[..];
}

lemma lemma_OutboundPackets(cout:OutboundPackets, me:EndPoint)
  requires cout.PacketSequence?
  requires forall p :: p in cout.s ==> CPacketIsSendable(p) && p.src == me
  requires CPacketSeqIsAbstractable(cout.s)
  requires |cout.s| < 0xFFFF_FFFF_FFFF_FFFF
  ensures OutboundPacketsIsValid(cout)
  ensures OutboundPacketsHasCorrectSrc(cout, me)
  ensures OutboundPacketsIsAbstractable(cout)
  ensures AbstractifyOutboundCPacketsToSeqOfRslPackets(cout) == AbstractifySeqOfCPacketsToSeqOfRslPackets(cout.s)
{
}

method {:timeLimitMultiplier 4} ExecutorExecute(cs:ExecutorState, reply_cache_mutable:MutableMap<EndPoint, CReply>) returns(cs':ExecutorState, cout:OutboundPackets)
  requires ExecutorState_IsValid(cs)
  requires cs.ops_complete.n < cs.constants.all.params.max_integer_val
  requires cs.next_op_to_execute.COutstandingOpKnown?
  requires MutableMap.MapOf(reply_cache_mutable) == cs.reply_cache
  modifies cs.app
  modifies reply_cache_mutable
  ensures  ExecutorState_IsValid(cs')
  ensures  OutboundPacketsIsValid(cout)
  ensures  OutboundPacketsHasCorrectSrc(cout, cs.constants.all.config.replica_ids[cs.constants.my_index])
  ensures  OutboundPacketsIsAbstractable(cout)
  ensures  LtUpperBound(AbstractifyExecutorStateToLExecutor(cs).ops_complete, AbstractifyExecutorStateToLExecutor(cs).constants.all.params.max_integer_val)
  ensures  LExecutorExecute(old(AbstractifyExecutorStateToLExecutor(cs)), AbstractifyExecutorStateToLExecutor(cs'), AbstractifyOutboundCPacketsToSeqOfRslPackets(cout))
  ensures  cs.constants == cs'.constants
  ensures  cs'.reply_cache == MutableMap.MapOf(reply_cache_mutable)
{
  var cv := cs.next_op_to_execute.v;
  //var start_time := Time.GetDebugTimeTicks();
  ghost var s := AbstractifyExecutorStateToLExecutor(cs);
  ghost var v := AbstractifyCRequestBatchToRequestBatch(cv);

  assert AbstractifyCRequestBatchToRequestBatch(cv) == AbstractifyExecutorStateToLExecutor(cs).next_op_to_execute.v;
  assert AbstractifyCAppStateToAppState(cs.app.Abstractify()) == AbstractifyExecutorStateToLExecutor(cs).app;

  ghost var g_tuple := HandleRequestBatch(s.app, v);
  lemma_AbstractifyCReplyCacheToReplyCache_properties(cs.reply_cache);
  var creplies;
  ghost var states, replies, newReplyCache;
  var start_time_request_batch := Time.GetDebugTimeTicks();
  creplies, newReplyCache, states, replies := HandleRequestBatchImpl(cs.app, cv, cs.reply_cache, reply_cache_mutable);
  var end_time_request_batch := Time.GetDebugTimeTicks();
  RecordTimingSeq("ExecutorExecute_HandleRequestBatch", start_time_request_batch, end_time_request_batch);
  assert replies == AbstractifyCReplySeqToReplySeq(creplies);
  ghost var new_state := states[|states|-1];
  assert forall i :: 0 <= i < |cv| ==> AbstractifyCRequestToRequest(cv[i]) == v[i];
    
  //var end_time_app := Time.GetDebugTimeTicks();

  lemma_AbstractifyCReplyCacheToReplyCache_properties(newReplyCache);
  assert forall client :: client in newReplyCache ==> (|| (client in cs.reply_cache && newReplyCache[client] == cs.reply_cache[client])
                                                || (exists req_idx :: 0 <= req_idx < |cv| && creplies[req_idx].client == client && newReplyCache[client] == creplies[req_idx]));

  var newMaxBalReflected := (if CBallotIsNotGreaterThan(cs.max_bal_reflected, cs.next_op_to_execute.bal) then cs.next_op_to_execute.bal else cs.max_bal_reflected);
  cs' := cs.(ops_complete := COperationNumber(cs.ops_complete.n + 1),
             max_bal_reflected := newMaxBalReflected,
             next_op_to_execute := COutstandingOpUnknown(),
             reply_cache := newReplyCache);
   
  assert cs'.ops_complete.COperationNumber?;
  assert COperationNumberIsAbstractable(cs'.ops_complete);
  ghost var s' :=  AbstractifyExecutorStateToLExecutor(cs');
    
  assert s'.reply_cache == AbstractifyCReplyCacheToReplyCache(newReplyCache);
  assert AbstractifyExecutorStateToLExecutor(cs).reply_cache == AbstractifyCReplyCacheToReplyCache(cs.reply_cache);
  assert s.reply_cache == AbstractifyCReplyCacheToReplyCache(cs.reply_cache);
    
  var i := |cv|-1;
  if |cv| > 0 {
    assert 0 <= i < |cv|;
  } else {
    assert nextstep(i) == 0;
  }
  calc {
    nextstep(i);
    |cv|-1+1;
    |cv|;
    |states|-1;
  }
  assert AbstractifyExecutorStateToLExecutor(cs').app == new_state;

  var cme := cs.constants.all.config.replica_ids[cs.constants.my_index];
  assert forall r :: r in creplies ==> ValidReply(r) && CReplyIsAbstractable(r);
  assert cme == cs.constants.all.config.replica_ids[cs.constants.my_index];
  lemma_InSequence(cs.constants.all.config.replica_ids, cme, cs.constants.my_index);
  assert cme in cs.constants.all.config.replica_ids;
  assert ReplicaConstantsState_IsValid(cs.constants);
  assert CPaxosConfigurationIsValid(cs.constants.all.config);
  assert forall r :: r in cs.constants.all.config.replica_ids ==> EndPointIsValidPublicKey(r);
  assert EndPointIsValidPublicKey(cme);
    
  var start_time_get_packets := Time.GetDebugTimeTicks();
  var packets := GetPacketsFromRepliesImpl(cme, cv, creplies);
  cout := PacketSequence(packets);
  var end_time_get_packets := Time.GetDebugTimeTicks();
  RecordTimingSeq("ExecutorExecute_GetPackets", start_time_get_packets, end_time_get_packets);
  assert forall p :: p in packets ==> CPacketIsSendable(p);
  assert cout.PacketSequence?;
  assert forall p :: p in cout.s ==> CPacketIsSendable(p);
  lemma_OutboundPackets(cout, cme);
  assert OutboundPacketsIsValid(cout);
    
  assert OutboundPacketsHasCorrectSrc(cout, cme);

  ghost var out := AbstractifyOutboundCPacketsToSeqOfRslPackets(cout);
  ghost var refinedSeq := AbstractifySeqOfCPacketsToSeqOfRslPackets(cout.s);
  assert out == refinedSeq;
  assert refinedSeq == GetPacketsFromReplies(AbstractifyEndPointToNodeIdentity(cme), AbstractifyCRequestsSeqToRequestsSeq(cv), AbstractifyCReplySeqToReplySeq(creplies));
  lemma_BatchAndRequestSeqEquivalence(cv);
  assert AbstractifyCRequestsSeqToRequestsSeq(cv) == AbstractifyCRequestBatchToRequestBatch(cv);
  assert refinedSeq == GetPacketsFromReplies(AbstractifyEndPointToNodeIdentity(cme), AbstractifyCRequestBatchToRequestBatch(cv), AbstractifyCReplySeqToReplySeq(creplies));
    
  assert AbstractifyEndPointToNodeIdentity(cme) == s.constants.all.config.replica_ids[s.constants.my_index];
  assert AbstractifyCRequestBatchToRequestBatch(cv) == AbstractifyExecutorStateToLExecutor(cs).next_op_to_execute.v;
  assert s.next_op_to_execute.v == AbstractifyCRequestBatchToRequestBatch(cv);
  assert replies == HandleRequestBatch(s.app, s.next_op_to_execute.v).1;
  assert replies == AbstractifyCReplySeqToReplySeq(creplies);
  assert refinedSeq == GetPacketsFromReplies(s.constants.all.config.replica_ids[s.constants.my_index], s.next_op_to_execute.v, replies);
  calc {
    out;
    refinedSeq;
    GetPacketsFromReplies(s.constants.all.config.replica_ids[s.constants.my_index], s.next_op_to_execute.v, replies);
  }
  assert out == GetPacketsFromReplies(s.constants.all.config.replica_ids[s.constants.my_index], s.next_op_to_execute.v, replies);
  assert AbstractifyExecutorStateToLExecutor(cs').ops_complete == AbstractifyExecutorStateToLExecutor(cs).ops_complete + 1;
}

lemma lemma_BatchAndRequestSeqEquivalence(s:seq<CRequest>)
  requires CRequestsSeqIsAbstractable(s)
  ensures AbstractifyCRequestsSeqToRequestsSeq(s) == AbstractifyCRequestBatchToRequestBatch(s)
{
  reveal AbstractifyCRequestBatchToRequestBatch();
}

lemma lemma_InSequence<T>(s:seq<T>, p:T, i:uint64)
  requires 0 <= i as int < |s|
  requires s[i] == p
  ensures p in s
{
}

method ExecutorProcessAppStateSupply(cs:ExecutorState, cinp:CPacket) returns(cs':ExecutorState)
  requires ExecutorState_IsValid(cs)
  requires CPacketIsAbstractable(cinp)
  requires cinp.msg.CMessage_AppStateSupply?
  requires CAppStateMarshallable(cinp.msg.app_state)
  requires cinp.src in cs.constants.all.config.replica_ids
  requires cinp.msg.opn_state_supply.n > cs.ops_complete.n
  ensures  ExecutorState_IsValid(cs')
  ensures  AbstractifyCPacketToRslPacket(cinp).msg.RslMessage_AppStateSupply?
  ensures  AbstractifyCPacketToRslPacket(cinp).src in AbstractifyExecutorStateToLExecutor(cs).constants.all.config.replica_ids
  ensures  AbstractifyCPacketToRslPacket(cinp).msg.opn_state_supply > AbstractifyExecutorStateToLExecutor(cs).ops_complete
  ensures  LExecutorProcessAppStateSupply(AbstractifyExecutorStateToLExecutor(cs), AbstractifyExecutorStateToLExecutor(cs'), AbstractifyCPacketToRslPacket(cinp))
  ensures  cs.constants == cs'.constants
  ensures  cs'.reply_cache == cs.reply_cache
{
  ghost var s := AbstractifyExecutorStateToLExecutor(cs);
  ghost var inp := AbstractifyCPacketToRslPacket(cinp);
  ghost var m := inp.msg;
  ghost var s' := s.(
        app := m.app_state,
        ops_complete := m.opn_state_supply,
        max_bal_reflected := m.bal_state_supply,
        next_op_to_execute := OutstandingOpUnknown());
  var cm := cinp.msg;
  var app_state := AppStateMachine.Deserialize(cm.app_state);

  cs' := cs.(
        app := app_state,
        ops_complete := cm.opn_state_supply,
        max_bal_reflected := cm.bal_state_supply,
        next_op_to_execute := COutstandingOpUnknown());

  assert Eq_ExecutorState(s', AbstractifyExecutorStateToLExecutor(cs'));
}

method ExecutorProcessAppStateRequest(cs:ExecutorState, cinp:CPacket, reply_cache_mutable:MutableMap<EndPoint, CReply>) returns(cs':ExecutorState, cout:OutboundPackets)
  requires ExecutorState_IsValid(cs)
  requires CPacketIsAbstractable(cinp)
  requires cinp.msg.CMessage_AppStateRequest?
  requires MutableMap.MapOf(reply_cache_mutable) == cs.reply_cache
  ensures  ExecutorState_IsValid(cs')
  ensures  OutboundPacketsIsValid(cout)
  ensures  AbstractifyCPacketToRslPacket(cinp).msg.RslMessage_AppStateRequest?
  ensures  OutboundPacketsHasCorrectSrc(cout, cs.constants.all.config.replica_ids[cs.constants.my_index])
  ensures  OutboundPacketsIsAbstractable(cout)
  ensures  LExecutorProcessAppStateRequest(AbstractifyExecutorStateToLExecutor(cs), AbstractifyExecutorStateToLExecutor(cs'), AbstractifyCPacketToRslPacket(cinp), AbstractifyOutboundCPacketsToSeqOfRslPackets(cout))
  ensures  cs == cs'
{
  ghost var s := AbstractifyExecutorStateToLExecutor(cs);
  ghost var inp := AbstractifyCPacketToRslPacket(cinp);
  ghost var m := inp.msg;
  ghost var s' := s;
  ghost var out:seq<RslPacket>;
  cs' := cs;

  reveal AbstractifySetOfCPacketsToSetOfRslPackets();
  lemma_AbstractifyEndPointsToNodeIdentities_properties(cs.constants.all.config.replica_ids);

  if cinp.src in cs.constants.all.config.replica_ids && CBallotIsNotGreaterThan(cs.max_bal_reflected, cinp.msg.bal_state_req) && cs.ops_complete.n >= cinp.msg.opn_state_req.n {
    ghost var me := s.constants.all.config.replica_ids[s.constants.my_index];
    var cme := cs.constants.all.config.replica_ids[cs.constants.my_index];
    var reply_cache := MutableMap.MapOf(reply_cache_mutable);
    var app_state := cs.app.Serialize();
    out := [ LPacket(inp.src, me, RslMessage_AppStateSupply(s.max_bal_reflected, s.ops_complete, s.app)) ];
    cout := OutboundPacket(Some(CPacket(cinp.src, cme, CMessage_AppStateSupply(cs.max_bal_reflected, cs.ops_complete, app_state))));
  } else {
    out := [];
    cout := OutboundPacket(None());
  }

  assert AbstractifyOutboundCPacketsToSeqOfRslPackets(cout) == out;
}

method ExecutorProcessStartingPhase2(cs:ExecutorState, cinp:CPacket) returns(cs':ExecutorState, cout:CBroadcast)
  requires ExecutorState_IsValid(cs)
  requires CPacketIsAbstractable(cinp)
  requires cinp.msg.CMessage_StartingPhase2?
  ensures  ExecutorState_IsValid(cs')
  ensures  CBroadcastIsValid(cout)
  ensures  OutboundPacketsHasCorrectSrc(Broadcast(cout), cs.constants.all.config.replica_ids[cs.constants.my_index])
  ensures  AbstractifyCPacketToRslPacket(cinp).msg.RslMessage_StartingPhase2?
  ensures  LExecutorProcessStartingPhase2(AbstractifyExecutorStateToLExecutor(cs), AbstractifyExecutorStateToLExecutor(cs'), AbstractifyCPacketToRslPacket(cinp), AbstractifyCBroadcastToRlsPacketSeq(cout))
  ensures  cs == cs'
  ensures  OutboundPacketsHasCorrectSrc(Broadcast(cout), cs'.constants.all.config.replica_ids[cs'.constants.my_index])
{
  var start_time := Time.GetDebugTimeTicks();
  ghost var s := AbstractifyExecutorStateToLExecutor(cs);
  ghost var inp := AbstractifyCPacketToRslPacket(cinp);
  ghost var opn := inp.msg.logTruncationPoint_2;
  ghost var s' := s;
  ghost var out:seq<RslPacket>;
  var copn := cinp.msg.logTruncationPoint_2;
  cs' := cs;

  reveal AbstractifySetOfCPacketsToSetOfRslPackets();
  lemma_AbstractifyEndPointsToNodeIdentities_properties(cs.constants.all.config.replica_ids);

  if cinp.src in cs.constants.all.config.replica_ids && copn.n > cs.ops_complete.n {
    ghost var msg := RslMessage_AppStateRequest(inp.msg.bal_2, opn);
    var cmsg := CMessage_AppStateRequest(cinp.msg.bal_2, copn);
    out := BuildLBroadcast(s.constants.all.config.replica_ids[s.constants.my_index], 
                           s.constants.all.config.replica_ids, msg);
    cout := BuildBroadcastToEveryone(cs.constants.all.config, cs.constants.my_index, cmsg);
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("ExecutorProcessStartingPhase2_request", start_time, end_time);
  } else {
    out := [];
    cout := CBroadcastNop;
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("ExecutorProcessStartingPhase2_nada", start_time, end_time);
  }
}

method ExecutorProcessRequest(cs:ExecutorState, cinp:CPacket, cachedReply:CReply, reply_cache_mutable:MutableMap<EndPoint, CReply>)
  returns(cout:OutboundPackets)
  requires ExecutorState_IsValid(cs)
  requires CPacketIsAbstractable(cinp)
  requires cinp.msg.CMessage_Request?
  requires cinp.src in cs.reply_cache
  requires cachedReply == cs.reply_cache[cinp.src]
  requires cachedReply.CReply?
  requires cinp.msg.seqno <= cachedReply.seqno
  requires MutableMap.MapOf(reply_cache_mutable) == cs.reply_cache
  ensures  OutboundPacketsIsValid(cout)
  ensures  OutboundPacketsHasCorrectSrc(cout, cs.constants.all.config.replica_ids[cs.constants.my_index])
  ensures  OutboundPacketsIsAbstractable(cout)
  ensures  AbstractifyCPacketToRslPacket(cinp).msg.RslMessage_Request?
  ensures  AbstractifyCPacketToRslPacket(cinp).src in AbstractifyExecutorStateToLExecutor(cs).reply_cache
  ensures  AbstractifyExecutorStateToLExecutor(cs).reply_cache[AbstractifyCPacketToRslPacket(cinp).src].Reply?
  ensures  AbstractifyCPacketToRslPacket(cinp).msg.seqno_req <= AbstractifyExecutorStateToLExecutor(cs).reply_cache[AbstractifyCPacketToRslPacket(cinp).src].seqno
  ensures  LExecutorProcessRequest(AbstractifyExecutorStateToLExecutor(cs), AbstractifyCPacketToRslPacket(cinp), AbstractifyOutboundCPacketsToSeqOfRslPackets(cout))
  ensures  OutboundPacketsHasCorrectSrc(cout, cs.constants.all.config.replica_ids[cs.constants.my_index])
{
  //ghost var s := AbstractifyExecutorStateToLExecutor(cs);
  ghost var inp := AbstractifyCPacketToRslPacket(cinp);
  lemma_AbstractifyCReplyCacheToReplyCache_properties(cs.reply_cache);
  ghost var out:seq<RslPacket>;
  // the assert below is the trigger needed since we added an explicit trigger in the corresponding ensures in lemma_AbstractifyCReplyCacheToReplyCache_properties
  assert AbstractifyCReplyCacheToReplyCache(cs.reply_cache)[AbstractifyEndPointToNodeIdentity(cinp.src)] == AbstractifyCReplyToReply(cs.reply_cache[cinp.src]); 
  assert cinp.msg.seqno <= cachedReply.seqno;
  var cr := cachedReply;
  var msg := CMessage_Reply(cr.seqno, cr.reply);
  if PrintParams.ShouldPrintProgress() {
    print("Sending cached reply to client ");
    print(cr.client);
    print(" with sequence number ");
    print(cr.seqno);
    print("\n");
  }
  cout := OutboundPacket(Some(CPacket(cr.client, cs.constants.all.config.replica_ids[cs.constants.my_index], msg)));
  assert cinp.src in cs.reply_cache;
  assert ValidReply(cs.reply_cache[cinp.src]);
  assert CAppReplyMarshallable(cr.reply);
  assert OutboundPacketsIsValid(cout);
}

} 
