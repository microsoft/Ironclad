include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "Environment.i.dfy"
include "../CommonProof/Actions.i.dfy"

module LivenessProof__Execution_i {

import opened LiveRSL__Constants_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Executor_i
import opened LiveRSL__Replica_i
import opened LiveRSL__StateMachine_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__Environment_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened Concrete_NodeIdentity_i
import opened Temporal__Temporal_s
import opened Temporal__Rules_i
import opened Environment_s
import opened EnvironmentSynchrony_s
import opened Collections__Maps2_s
import opened Common__UpperBound_s

predicate ReplySentToClientWithSeqno(ps:RslState, ps':RslState, client:NodeIdentity, seqno:int, idx:int, ios:seq<RslIo>, batch_idx:int)
{
  && 0 <= idx < |ps.replicas|
  && 0 <= idx < |ps'.replicas|
  && var s := ps.replicas[idx].replica;
     var s' := ps'.replicas[idx].replica;
     && RslNextOneReplica(ps, ps', idx, ios)
     && LReplicaNextSpontaneousMaybeExecute(s, s', ExtractSentPacketsFromIos(ios))
     && s.executor.next_op_to_execute.OutstandingOpKnown?
     && LtUpperBound(s.executor.ops_complete, s.executor.constants.all.params.max_integer_val)
     && LReplicaConstantsValid(s.executor.constants)
     && 0 <= batch_idx < |s.executor.next_op_to_execute.v|
     && s.executor.next_op_to_execute.v[batch_idx].Request?
     && s.executor.next_op_to_execute.v[batch_idx].client == client
     && s.executor.next_op_to_execute.v[batch_idx].seqno == seqno
}

predicate RequestWithSeqnoExecuted(ps:RslState, ps':RslState, client:NodeIdentity, seqno:int, idx:int)
{
  exists ios, batch_idx :: ReplySentToClientWithSeqno(ps, ps', client, seqno, idx, ios, batch_idx)
}

function {:opaque} RequestWithSeqnoExecutedTemporal(b:Behavior<RslState>, client:NodeIdentity, seqno:int, idx:int):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, RequestWithSeqnoExecutedTemporal(b, client, seqno, idx))} ::
             sat(i, RequestWithSeqnoExecutedTemporal(b, client, seqno, idx)) <==> RequestWithSeqnoExecuted(b[i], b[nextstep(i)], client, seqno, idx)
{
  stepmap(imap i :: RequestWithSeqnoExecuted(b[i], b[nextstep(i)], client, seqno, idx))
}

predicate ReplySentToClientAtLeastSeqno(ps:RslState, ps':RslState, client:NodeIdentity, seqno:int, idx:int, ios:seq<RslIo>, batch_idx:int)
{
  && 0 <= idx < |ps.replicas|
  && 0 <= idx < |ps'.replicas|
  && var s := ps.replicas[idx].replica;
     var s' := ps'.replicas[idx].replica;
     && RslNextOneReplica(ps, ps', idx, ios)
     && LReplicaNextSpontaneousMaybeExecute(s, s', ExtractSentPacketsFromIos(ios))
     && s.executor.next_op_to_execute.OutstandingOpKnown?
     && LtUpperBound(s.executor.ops_complete, s.executor.constants.all.params.max_integer_val)
     && LReplicaConstantsValid(s.executor.constants)
     && 0 <= batch_idx < |s.executor.next_op_to_execute.v|
     && s.executor.next_op_to_execute.v[batch_idx].Request?
     && s.executor.next_op_to_execute.v[batch_idx].client == client
     && s.executor.next_op_to_execute.v[batch_idx].seqno >= seqno
}

predicate RequestAtLeastSeqnoExecuted(ps:RslState, ps':RslState, client:NodeIdentity, seqno:int, idx:int)
{
  exists ios, batch_idx :: ReplySentToClientAtLeastSeqno(ps, ps', client, seqno, idx, ios, batch_idx)
}

function {:opaque} RequestAtLeastSeqnoExecutedTemporal(b:Behavior<RslState>, client:NodeIdentity, seqno:int, idx:int):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, RequestAtLeastSeqnoExecutedTemporal(b, client, seqno, idx))} ::
             sat(i, RequestAtLeastSeqnoExecutedTemporal(b, client, seqno, idx)) <==> RequestAtLeastSeqnoExecuted(b[i], b[nextstep(i)], client, seqno, idx)
{
  stepmap(imap i :: RequestAtLeastSeqnoExecuted(b[i], b[nextstep(i)], client, seqno, idx))
}


lemma lemma_PersistentRequestNeverExecuted(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires idx in asp.live_quorum
  ensures  sat(asp.synchrony_start, always(not(RequestWithSeqnoExecutedTemporal(b, asp.persistent_request.client, asp.persistent_request.seqno, idx))))
{
  var client := asp.persistent_request.client;
  var seqno := asp.persistent_request.seqno;
  var t := RequestWithSeqnoExecutedTemporal(b, client, seqno, idx);
    
  forall i | asp.synchrony_start <= i
    ensures !sat(i, t)
  {
    if sat(i, t)
    {
      lemma_ConstantsAllConsistent(b, asp.c, i);

      var ps := b[i];
      var ps' := b[i+1];
      var s := ps.replicas[idx].replica.executor;
      var ios, batch_idx :| ReplySentToClientWithSeqno(ps, ps', client, seqno, idx, ios, batch_idx);
      var sent_packets := ExtractSentPacketsFromIos(ios);
      assert LExecutorExecute(ps.replicas[idx].replica.executor, ps'.replicas[idx].replica.executor, sent_packets);

      var batch := s.next_op_to_execute.v;
      var temp := HandleRequestBatch(s.app, batch);
      var new_state := temp.0[|temp.0|-1];
      var replies := temp.1;

      var me := s.constants.all.config.replica_ids[s.constants.my_index];
      lemma_SpecificPacketInGetPacketsFromReplies(me, batch, replies, sent_packets, batch_idx);
      var p := sent_packets[batch_idx];
      assert LIoOpSend(p) in ios;

      var delivery_step := lemma_PacketSentEventuallyDelivered(b, asp, i, p);
      lemma_ConstantsAllConsistent(b, asp.c, delivery_step);
      assert ReplyDeliveredDuringStep(b[delivery_step], asp.persistent_request);
      TemporalDeduceFromAlways(0, delivery_step, not(ReplyDeliveredTemporal(b, asp.persistent_request)));
      assert false;
    }
  }

  TemporalAlways(asp.synchrony_start, not(t));
}
    
}
