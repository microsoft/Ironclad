include "Configuration.i.dfy"
include "Environment.i.dfy"
include "Types.i.dfy"
include "Constants.i.dfy"
include "Executor.i.dfy"
include "../../Common/Collections/Maps.i.dfy"

module LiveRSL__Learner_i {
import opened LiveRSL__Configuration_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Types_i
import opened LiveRSL__Constants_i
import opened LiveRSL__Executor_i
import opened Collections__Maps_i

datatype LLearner = LLearner(
  constants:LReplicaConstants,
  max_ballot_seen:Ballot,
  unexecuted_learner_state:LearnerState
  )

predicate LLearnerInit(l:LLearner, c:LReplicaConstants)
{
  && l.constants == c
  && l.max_ballot_seen == Ballot(0,0)
  && l.unexecuted_learner_state == map[]
}

predicate LLearnerProcess2b(s:LLearner, s':LLearner, packet:RslPacket)
  requires packet.msg.RslMessage_2b?
{
  var m := packet.msg;
  var opn := m.opn_2b;
  if packet.src !in s.constants.all.config.replica_ids || BalLt(m.bal_2b, s.max_ballot_seen) then
    s' == s
  else if BalLt(s.max_ballot_seen, m.bal_2b) then
    var tup' := LearnerTuple({packet.src}, m.val_2b);
    s' == s.(max_ballot_seen := m.bal_2b,
             unexecuted_learner_state := map[opn := tup'])
  else if opn !in s.unexecuted_learner_state then
    var tup' := LearnerTuple({packet.src}, m.val_2b);
    s' == s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup'])
  else if packet.src in s.unexecuted_learner_state[opn].received_2b_message_senders then
    s' == s
  else
    var tup := s.unexecuted_learner_state[opn];
    var tup' := tup.(received_2b_message_senders := tup.received_2b_message_senders + {packet.src});
    s' == s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup'])
}

predicate LLearnerForgetDecision(s:LLearner, s':LLearner, opn:OperationNumber)
{
  if opn in s.unexecuted_learner_state then
    s' == s.(unexecuted_learner_state := RemoveElt(s.unexecuted_learner_state, opn))
  else
    s' == s
}

predicate LLearnerForgetOperationsBefore(s:LLearner, s':LLearner, ops_complete:OperationNumber)
{
  s' == s.(unexecuted_learner_state := (map op | op in s.unexecuted_learner_state && op >= ops_complete :: s.unexecuted_learner_state[op]))
}

} 
