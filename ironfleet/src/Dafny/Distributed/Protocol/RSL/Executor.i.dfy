include "Configuration.i.dfy"
include "Environment.i.dfy"
include "Types.i.dfy"
include "Constants.i.dfy"
include "../../Services/RSL/AppStateMachine.i.dfy"
include "StateMachine.i.dfy"
include "Broadcast.i.dfy"
include "../../Common/Collections/Maps.i.dfy"

module LiveRSL__Executor_i {
import opened LiveRSL__Configuration_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Types_i
import opened LiveRSL__Constants_i
import opened LiveRSL__Message_i
import opened LiveRSL__StateMachine_i
import opened LiveRSL__Broadcast_i
import opened AppStateMachine_i
import opened Collections__Maps_i
import opened Concrete_NodeIdentity_i
import opened Environment_s
import opened Common__UpperBound_s

datatype OutstandingOperation = OutstandingOpKnown(v:RequestBatch, bal:Ballot) | OutstandingOpUnknown()

datatype LExecutor = LExecutor(
  constants:LReplicaConstants,
  app:AppState,
  ops_complete:int,
  max_bal_reflected:Ballot,
  next_op_to_execute:OutstandingOperation,
  reply_cache:ReplyCache
  )

predicate LExecutorInit(s:LExecutor, c:LReplicaConstants)
{
  && s.constants == c
  && s.app == AppInitialize()
  && s.ops_complete == 0
  && s.max_bal_reflected == Ballot(0, 0)
  && s.next_op_to_execute == OutstandingOpUnknown()
  && s.reply_cache == map[]
}

predicate LExecutorGetDecision(s:LExecutor, s':LExecutor, bal:Ballot, opn:OperationNumber, v:RequestBatch)
  requires opn == s.ops_complete
  requires s.next_op_to_execute.OutstandingOpUnknown?
{
  s' == s.(next_op_to_execute := OutstandingOpKnown(v, bal))
}

function GetPacketsFromReplies(me:NodeIdentity, requests:seq<Request>, replies:seq<Reply>) : seq<RslPacket>
  requires |requests| == |replies|
  requires forall r :: r in replies ==> r.Reply?
  ensures  forall p :: p in GetPacketsFromReplies(me, requests, replies) ==> p.src == me && p.msg.RslMessage_Reply?
{
  if |requests| == 0 then
    []
  else
    [LPacket(requests[0].client, me, RslMessage_Reply(requests[0].seqno, replies[0].reply))]
    + GetPacketsFromReplies(me, requests[1..], replies[1..])
}

lemma lemma_SizeOfGetPacketsFromReplies(me:NodeIdentity, requests:seq<Request>, replies:seq<Reply>, packets:seq<RslPacket>)
  requires |requests| == |replies|
  requires forall r :: r in replies ==> r.Reply?
  requires packets == GetPacketsFromReplies(me, requests, replies)
  ensures  |packets| == |requests|
  decreases |requests|
{
  if |requests| > 0
  {
    lemma_SizeOfGetPacketsFromReplies(me, requests[1..], replies[1..], packets[1..]);
  }
}

lemma lemma_SpecificPacketInGetPacketsFromReplies(me:NodeIdentity, requests:seq<Request>, replies:seq<Reply>,
                                                  packets:seq<RslPacket>, batch_idx:int)
  requires |requests| == |replies|
  requires forall r :: r in replies ==> r.Reply?
  requires 0 <= batch_idx < |requests|
  requires packets == GetPacketsFromReplies(me, requests, replies)
  ensures  |packets| == |requests|
  ensures  packets[batch_idx] == LPacket(requests[batch_idx].client, me, RslMessage_Reply(requests[batch_idx].seqno, replies[batch_idx].reply))
  decreases |requests|
{
  lemma_SizeOfGetPacketsFromReplies(me, requests, replies, packets);

  if |requests| > 0
  {
    if batch_idx > 0
    {
      lemma_SpecificPacketInGetPacketsFromReplies(me, requests[1..], replies[1..], packets[1..], batch_idx-1);
    }
  }
}
    
predicate LExecutorExecute(s:LExecutor, s':LExecutor, sent_packets:seq<RslPacket>)
  requires s.next_op_to_execute.OutstandingOpKnown?
  requires LtUpperBound(s.ops_complete, s.constants.all.params.max_integer_val)
  requires LReplicaConstantsValid(s.constants)
{
  var batch := s.next_op_to_execute.v;
  var temp := HandleRequestBatch(s.app, batch);
  var new_state := temp.0[|temp.0|-1];
  var replies := temp.1;
  && s'.constants == s.constants
  && s'.app == new_state
  && s'.ops_complete == s.ops_complete + 1
  && s'.max_bal_reflected == (if BalLeq(s.max_bal_reflected, s.next_op_to_execute.bal) then s.next_op_to_execute.bal else s.max_bal_reflected)
  && s'.next_op_to_execute == OutstandingOpUnknown()
  && (forall client :: client in s'.reply_cache ==> (|| (client in s.reply_cache && s'.reply_cache[client] == s.reply_cache[client])
                                             || (exists req_idx :: && 0 <= req_idx < |batch|
                                                            && replies[req_idx].client == client
                                                            && s'.reply_cache[client] == replies[req_idx])))
  && sent_packets == GetPacketsFromReplies(s.constants.all.config.replica_ids[s.constants.my_index], batch, replies)
}

predicate LExecutorProcessAppStateSupply(s:LExecutor, s':LExecutor, inp:RslPacket)
  requires inp.msg.RslMessage_AppStateSupply?
  requires inp.src in s.constants.all.config.replica_ids && inp.msg.opn_state_supply > s.ops_complete
{
  var m := inp.msg;
  s' == s.(app := m.app_state,
           ops_complete := m.opn_state_supply,
           max_bal_reflected := m.bal_state_supply,
           next_op_to_execute := OutstandingOpUnknown(),
           reply_cache := m.reply_cache)
}

predicate LExecutorProcessAppStateRequest(s:LExecutor, s':LExecutor, inp:RslPacket, sent_packets:seq<RslPacket>)
  requires inp.msg.RslMessage_AppStateRequest?
{
  var m := inp.msg;
  if && inp.src in s.constants.all.config.replica_ids
     && BalLeq(s.max_bal_reflected, m.bal_state_req)
     && s.ops_complete >= m.opn_state_req
     && LReplicaConstantsValid(s.constants) then
     && s' == s
     && sent_packets == [ LPacket(inp.src, s.constants.all.config.replica_ids[s.constants.my_index],
                                 RslMessage_AppStateSupply(s.max_bal_reflected, s.ops_complete, s.app, s.reply_cache)) ]
  else
    s' == s && sent_packets == []
}

predicate LExecutorProcessStartingPhase2(s:LExecutor, s':LExecutor, inp:RslPacket, sent_packets:seq<RslPacket>)
  requires inp.msg.RslMessage_StartingPhase2?
{
  if inp.src in s.constants.all.config.replica_ids && inp.msg.logTruncationPoint_2 > s.ops_complete then
    s' == s && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index,
                                   RslMessage_AppStateRequest(inp.msg.bal_2, inp.msg.logTruncationPoint_2), sent_packets)
  else
    s' == s && sent_packets == []
}

predicate LExecutorProcessRequest(s:LExecutor, inp:RslPacket, sent_packets:seq<RslPacket>)
  requires inp.msg.RslMessage_Request?
  requires inp.src in s.reply_cache
  requires s.reply_cache[inp.src].Reply?
  requires inp.msg.seqno_req <= s.reply_cache[inp.src].seqno
{
  if inp.msg.seqno_req == s.reply_cache[inp.src].seqno && LReplicaConstantsValid(s.constants) then
    var r := s.reply_cache[inp.src];
    sent_packets == [ LPacket(r.client, s.constants.all.config.replica_ids[s.constants.my_index], RslMessage_Reply(r.seqno, r.reply)) ]
  else
    sent_packets == []
}

} 
