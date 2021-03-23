include "Environment.i.dfy"
include "Configuration.i.dfy"
include "Constants.i.dfy"
include "Broadcast.i.dfy"
include "../../Common/Collections/CountMatches.i.dfy"

module LiveRSL__Acceptor_i {
import opened LiveRSL__Environment_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__Constants_i
import opened LiveRSL__Broadcast_i
import opened LiveRSL__Types_i
import opened LiveRSL__Message_i
import opened Collections__CountMatches_i
import opened Environment_s
import opened Common__UpperBound_s

datatype LAcceptor = LAcceptor(
  constants:LReplicaConstants,
  max_bal:Ballot,
  votes:Votes,
  last_checkpointed_operation:seq<OperationNumber>,
  log_truncation_point:OperationNumber
  )

predicate IsLogTruncationPointValid(log_truncation_point:OperationNumber, last_checkpointed_operation:seq<OperationNumber>,
                                    config:LConfiguration)
{
  IsNthHighestValueInSequence(log_truncation_point,
                              last_checkpointed_operation,
                              LMinQuorumSize(config))
}

predicate RemoveVotesBeforeLogTruncationPoint(votes:Votes, votes':Votes, log_truncation_point:int)
{
  && (forall opn :: opn in votes' ==> opn in votes && votes'[opn] == votes[opn])
  && (forall opn :: opn < log_truncation_point ==> opn !in votes')
  && (forall opn :: opn >= log_truncation_point && opn in votes ==> opn in votes')
}

predicate LAddVoteAndRemoveOldOnes(votes:Votes, votes':Votes, new_opn:OperationNumber, new_vote:Vote, log_truncation_point:OperationNumber)
{
  && (forall opn :: opn in votes' <==> opn >= log_truncation_point && (opn in votes || opn == new_opn))
  && (forall opn :: opn in votes' ==> votes'[opn] == (if opn == new_opn then new_vote else votes[opn]))
}

predicate LAcceptorInit(a:LAcceptor, c:LReplicaConstants)
{
  && a.constants == c
  && a.max_bal == Ballot(0,0)
  && a.votes == map []
  && |a.last_checkpointed_operation| == |c.all.config.replica_ids|
  && (forall idx {:trigger a.last_checkpointed_operation[idx]} :: 0 <= idx < |a.last_checkpointed_operation| ==>
       a.last_checkpointed_operation[idx] == 0)
  && a.log_truncation_point == 0
}

predicate LAcceptorProcess1a(s:LAcceptor, s':LAcceptor, inp:RslPacket, sent_packets:seq<RslPacket>)
  requires inp.msg.RslMessage_1a?
{
  var m := inp.msg;
  if inp.src in s.constants.all.config.replica_ids && BalLt(s.max_bal, m.bal_1a) && LReplicaConstantsValid(s.constants) then
    && sent_packets == [ LPacket(inp.src, s.constants.all.config.replica_ids[s.constants.my_index],
                                RslMessage_1b(m.bal_1a, s.log_truncation_point, s.votes)) ]
    && s' == s.(max_bal := m.bal_1a)
  else
    s' == s && sent_packets == []
}

predicate LAcceptorProcess2a(s:LAcceptor, s':LAcceptor, inp:RslPacket, sent_packets:seq<RslPacket>)
  requires inp.msg.RslMessage_2a?
  requires inp.src in s.constants.all.config.replica_ids
  requires BalLeq(s.max_bal, inp.msg.bal_2a)
  requires LeqUpperBound(inp.msg.opn_2a, s.constants.all.params.max_integer_val)
{
  var m := inp.msg;
  var newLogTruncationPoint := if inp.msg.opn_2a - s.constants.all.params.max_log_length + 1 > s.log_truncation_point then 
                                 inp.msg.opn_2a - s.constants.all.params.max_log_length + 1
                               else
                                s.log_truncation_point;
  && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, RslMessage_2b(m.bal_2a, m.opn_2a, m.val_2a), sent_packets)
  && s'.max_bal == m.bal_2a
  && s'.log_truncation_point == newLogTruncationPoint
  && (if s.log_truncation_point <= inp.msg.opn_2a then
       LAddVoteAndRemoveOldOnes(s.votes, s'.votes, m.opn_2a, Vote(m.bal_2a, m.val_2a), newLogTruncationPoint)
     else
       s'.votes == s.votes
     )
  // UNCHANGED
  && s'.constants == s.constants
  && s'.last_checkpointed_operation == s.last_checkpointed_operation
}

predicate LAcceptorProcessHeartbeat(s:LAcceptor, s':LAcceptor, inp:RslPacket)
  requires inp.msg.RslMessage_Heartbeat?
{
  if inp.src in s.constants.all.config.replica_ids then
    var sender_index := GetReplicaIndex(inp.src, s.constants.all.config);
    if 0 <= sender_index < |s.last_checkpointed_operation| && inp.msg.opn_ckpt > s.last_checkpointed_operation[sender_index] then
      //s' == s[last_checkpointed_operation := s.last_checkpointed_operation[inp.src := inp.msg.opn_ckpt]]
      s'.last_checkpointed_operation == s.last_checkpointed_operation[sender_index := inp.msg.opn_ckpt]
      // UNCHANGED
      && s'.constants == s.constants
      && s'.max_bal == s.max_bal
      && s'.votes == s.votes
      && s'.log_truncation_point == s.log_truncation_point
    else
      s' == s
  else
    s' == s
}

predicate LAcceptorTruncateLog(s:LAcceptor, s':LAcceptor, opn:OperationNumber)
{
  if opn <= s.log_truncation_point then
    s' == s
  else
    && RemoveVotesBeforeLogTruncationPoint(s.votes, s'.votes, opn)
    && s' == s.(log_truncation_point := opn, votes := s'.votes)
}

}
