include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "Seqno.i.dfy"
include "Execution.i.dfy"
include "RoundRobin.i.dfy"
include "StablePeriod.i.dfy"
include "WF1.i.dfy"
include "../CommonProof/Actions.i.dfy"
include "../../../Common/Logic/Temporal/WF1.i.dfy"

module LivenessProof__RequestsReceived_i {

import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Election_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Message_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Environment_i
import opened LivenessProof__Execution_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__PacketHandling_i
import opened LivenessProof__RoundRobin_i
import opened LivenessProof__Seqno_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__WF1_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened Temporal__Induction_i
import opened Temporal__Rules_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Temporal__Time_i
import opened Temporal__WF1_i
import opened Environment_s
import opened Collections__Maps2_s

predicate RequestInRequestsReceivedPrevEpochs(ps:RslState, req:Request, idx:int)
{
  && 0 <= idx < |ps.replicas|
  && req in ps.replicas[idx].replica.proposer.election_state.requests_received_prev_epochs
}

function {:opaque} RequestInRequestsReceivedPrevEpochsTemporal(b:Behavior<RslState>, req:Request, idx:int):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, RequestInRequestsReceivedPrevEpochsTemporal(b, req, idx))} ::
             sat(i, RequestInRequestsReceivedPrevEpochsTemporal(b, req, idx)) <==> RequestInRequestsReceivedPrevEpochs(b[i], req, idx)
{
  stepmap(imap i :: RequestInRequestsReceivedPrevEpochs(b[i], req, idx))
}

predicate RequestInRequestsReceivedThisOrPrevEpochs(ps:RslState, req:Request, idx:int)
{
  && 0 <= idx < |ps.replicas|
  && (|| req in ps.replicas[idx].replica.proposer.election_state.requests_received_prev_epochs
     || req in ps.replicas[idx].replica.proposer.election_state.requests_received_this_epoch)
}

function {:opaque} RequestInRequestsReceivedThisOrPrevEpochsTemporal(b:Behavior<RslState>, req:Request, idx:int):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, RequestInRequestsReceivedThisOrPrevEpochsTemporal(b, req, idx))} ::
             sat(i, RequestInRequestsReceivedThisOrPrevEpochsTemporal(b, req, idx))
             <==> RequestInRequestsReceivedThisOrPrevEpochs(b[i], req, idx)
{
  stepmap(imap i :: RequestInRequestsReceivedThisOrPrevEpochs(b[i], req, idx))
}

lemma lemma_RemoveAllSatisfiedRequestsRemoval(s:seq<Request>, r:Request, r':Request)
  ensures r' in s && r' !in RemoveAllSatisfiedRequestsInSequence(s, r) ==> RequestSatisfiedBy(r', r)
{
  if r' in s && r' !in RemoveAllSatisfiedRequestsInSequence(s, r)
  {
    assert |s| > 0;
    assert r' !in RemoveAllSatisfiedRequestsInSequence(s[1..], r);
    lemma_RemoveAllSatisfiedRequestsRemoval(s[1..], r, r');
    if RequestSatisfiedBy(s[0], r)
    {
      assert r' in s;
      if r' == s[0]
      {
        assert RequestSatisfiedBy(r', r);
      }
    }
    else
    {
      assert r' != s[0];
      assert r' in s[1..];
    }
  }
}

lemma lemma_RemoveExecutedRequestBatchRemoval(s:seq<Request>, batch:RequestBatch, r':Request) returns (req_idx:int)
  requires r' in s
  requires r' !in RemoveExecutedRequestBatch(s, batch)
  ensures  0 <= req_idx < |batch|
  ensures  RequestSatisfiedBy(r', batch[req_idx])
  decreases |batch|
{
  if |batch| == 0
  {
  }
  else if RequestSatisfiedBy(r', batch[0])
  {
    req_idx := 0;
  }
  else
  {
    lemma_RemoveAllSatisfiedRequestsRemoval(s, batch[0], r');
    assert r' in RemoveAllSatisfiedRequestsInSequence(s, batch[0]);
    var req_idx_minus_1 := lemma_RemoveExecutedRequestBatchRemoval(RemoveAllSatisfiedRequestsInSequence(s, batch[0]), batch[1..], r');
    req_idx := req_idx_minus_1 + 1;
  }
}

lemma lemma_IfObjectNotInFirstNOfSequenceItsNotTheFirst<T>(r:T, s:seq<T>, n:int)
  requires |s| > 0
  requires n > 0
  requires !ObjectInFirstNOfSequence(r, s, n)
  ensures  r != s[0]
{
}

lemma lemma_RemoveAllSatisfiedRequestsRemovalFromFirstN(s:seq<Request>, r:Request, r':Request, n:int)
  ensures ObjectInFirstNOfSequence(r', s, n) && !ObjectInFirstNOfSequence(r', RemoveAllSatisfiedRequestsInSequence(s, r), n)
          ==> RequestSatisfiedBy(r', r)
{
  if ObjectInFirstNOfSequence(r', s, n) && !ObjectInFirstNOfSequence(r', RemoveAllSatisfiedRequestsInSequence(s, r), n)
  {
    assert |s| > 0;
    assert n > 0;
    if RequestSatisfiedBy(s[0], r)
    {
      if !ObjectInFirstNOfSequence(r', s[1..], n)
      {
        if |s[1..]| <= n
        {
          assert r' !in s[1..];
          assert r' == s[0];
        }
        else
        {
          assert r' !in s[1..][..n];
          assert r' !in s[1..n];
          assert |s| >= n;
          assert r' in s[..n];
          assert r' == s[0];
        }
        assert RequestSatisfiedBy(r', r);
      }
      else
      {
        lemma_RemoveAllSatisfiedRequestsRemovalFromFirstN(s[1..], r, r', n-1);
        assert RequestSatisfiedBy(r', r);
      }
    }
    else
    {
      var s' := RemoveAllSatisfiedRequestsInSequence(s[1..], r);
      assert !ObjectInFirstNOfSequence(r', [s[0]] + s', n);
      lemma_IfObjectNotInFirstNOfSequenceItsNotTheFirst(r', [s[0]] + s', n);
      assert r' != s[0];
      lemma_RemoveAllSatisfiedRequestsRemovalFromFirstN(s[1..], r, r', n-1);
      forall ensures !ObjectInFirstNOfSequence(r', s', n-1)
      {
        if |[s[0]] + s'| > n > 0 {
          assert ([s[0]] + s')[..n] == [s[0]] + s'[..n - 1];
        }
      }
    }
  }
}

lemma lemma_RemoveExecutedRequestBatchRemovalFromFirstN(s:seq<Request>, batch:RequestBatch, r':Request, n:int) returns (req_idx:int)
  requires ObjectInFirstNOfSequence(r', s, n)
  requires !ObjectInFirstNOfSequence(r', RemoveExecutedRequestBatch(s, batch), n)
  ensures  0 <= req_idx < |batch|
  ensures  RequestSatisfiedBy(r', batch[req_idx])
  decreases |batch|
{
  if |batch| == 0
  {
  }
  else if RequestSatisfiedBy(r', batch[0])
  {
    req_idx := 0;
  }
  else
  {
    lemma_RemoveAllSatisfiedRequestsRemovalFromFirstN(s, batch[0], r', n);
    var s' := RemoveAllSatisfiedRequestsInSequence(s, batch[0]);
    assert ObjectInFirstNOfSequence(r', s', n);
    assert !ObjectInFirstNOfSequence(r', RemoveExecutedRequestBatch(s', batch[1..]), n);
    var req_idx_minus_1 := lemma_RemoveExecutedRequestBatchRemovalFromFirstN(s', batch[1..], r', n);
    req_idx := req_idx_minus_1 + 1;
  }
}

lemma lemma_NextOpToExecuteNeverExceedsSeqno(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int,
  req_idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  requires b[i].replicas[idx].replica.executor.next_op_to_execute.OutstandingOpKnown?
  requires 0 <= req_idx < |b[i].replicas[idx].replica.executor.next_op_to_execute.v|
  requires b[i].replicas[idx].replica.executor.next_op_to_execute.v[req_idx].client == asp.persistent_request.client
  ensures  b[i].replicas[idx].replica.executor.next_op_to_execute.v[req_idx].seqno <= asp.persistent_request.seqno
{
  var s := b[i].replicas[idx].replica;

  lemma_SequenceNumberStateInvHolds(b, asp, i);
  assert SequenceNumberReplicaInv(s, asp.persistent_request);
  assert SequenceNumberRequestInv(s.executor.next_op_to_execute.v[req_idx], asp.persistent_request);
}

lemma lemma_EventuallyPersistentRequestInRequestsReceivedThisOrPrevEpochs(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  idx:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires idx in asp.live_quorum
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  ensures  processing_sync_start <= step
  ensures  sat(step, RequestInRequestsReceivedThisOrPrevEpochsTemporal(b, asp.persistent_request, idx))
{
  var client_send := ClientSendsRequestToReplicaTemporal(b, asp.persistent_request, asp.c.config.replica_ids[idx]);
  assert PersistentClientSendsRequestPeriodically(b, asp, idx);
  assert sat(asp.synchrony_start, always(eventuallynextwithin(client_send, asp.persistent_period, PaxosTimeMap(b))));
  TemporalDeduceFromAlways(asp.synchrony_start, processing_sync_start, eventuallynextwithin(client_send, asp.persistent_period, PaxosTimeMap(b)));
  var send_step := TemporalDeduceFromEventual(processing_sync_start, nextbefore(client_send, b[processing_sync_start].environment.time + asp.persistent_period, PaxosTimeMap(b)));
  var p := LPacket(asp.c.config.replica_ids[idx], asp.persistent_request.client, RslMessage_Request(asp.persistent_request.seqno, asp.persistent_request.request));
  var processing_step, ios := lemma_PacketSentToIndexProcessedByIt(b, asp, processing_sync_start, processing_bound, send_step, idx, p);

  lemma_RequestNeverHitsInReplyCache(b, asp, processing_sync_start, processing_bound, processing_step, idx, ios, p);

  var es := b[processing_step].replicas[idx].replica.proposer.election_state;
  var es' := b[processing_step+1].replicas[idx].replica.proposer.election_state;
  assert ElectionStateReflectReceivedRequest(es, es', asp.persistent_request);

  if earlier_req :| && (earlier_req in es.requests_received_prev_epochs || earlier_req in es.requests_received_this_epoch)
                    && RequestsMatch(earlier_req, asp.persistent_request)
  {
    lemma_SequenceNumberStateInvHolds(b, asp, processing_step);
    assert SequenceNumberRequestInv(earlier_req, asp.persistent_request);
    assert RequestInRequestsReceivedThisOrPrevEpochs(b[processing_step], asp.persistent_request, idx);
    step := processing_step;
  }
  else
  {
    lemma_ConstantsAllConsistent(b, asp.c, processing_step);
    lemma_OverflowProtectionNotUsedForReplica(b, asp, processing_step, idx);
    assert RequestInRequestsReceivedThisOrPrevEpochs(b[processing_step+1], asp.persistent_request, idx);
    step := processing_step + 1;
  }
}

lemma lemma_IfStepRemovesRequestFromBothThisAndPrevEpochsThenItsMaybeExecute(
  ps:RslState,
  ps':RslState,
  asp:AssumptionParameters,
  idx:int,
  req:Request
  ) returns (
  ios:seq<RslIo>
  )
  requires RslNext(ps, ps')
  requires RequestInRequestsReceivedThisOrPrevEpochs(ps, req, idx)
  requires !RequestInRequestsReceivedThisOrPrevEpochs(ps', req, idx)
  requires ps.replicas[idx].replica.proposer.election_state.constants.all.params == asp.c.params
  requires OverflowProtectionNotUsedForReplica(ps, idx, asp.c.params, asp.max_clock_ambiguity)
  ensures  RslNextOneReplica(ps, ps', idx, ios)
  ensures  LReplicaNextSpontaneousMaybeExecute(ps.replicas[idx].replica, ps'.replicas[idx].replica, ExtractSentPacketsFromIos(ios))
{
  var s := ps.replicas[idx].replica;
  var s' := ps.replicas[idx].replica;
  var es := ps.replicas[idx].replica.proposer.election_state;
  ios :| RslNextOneReplica(ps, ps', idx, ios);
  if && |ios| >= 1
     && ios[0].LIoOpReceive?
     && ios[0].r.msg.RslMessage_Request?
     && LReplicaNextProcessRequest(s, s', ios[0].r, ExtractSentPacketsFromIos(ios))
     && LProposerProcessRequest(s.proposer, s'.proposer, ios[0].r)
  {
    var p := ios[0].r;
    var val := Request(p.src, p.msg.seqno_req, p.msg.val);
    assert req in BoundRequestSequence(es.requests_received_prev_epochs + [val], es.constants.all.params.max_integer_val);
    assert false;
  }
  assert req in BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val);
}

lemma lemma_EventuallyPersistentRequestAlwaysInRequestsReceivedThisOrPrevEpochs(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  idx:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires idx in asp.live_quorum
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  ensures  processing_sync_start <= step
  ensures  sat(step, always(RequestInRequestsReceivedThisOrPrevEpochsTemporal(b, asp.persistent_request, idx)))
{
  var client := asp.persistent_request.client;
  var seqno := asp.persistent_request.seqno;
  var t := RequestInRequestsReceivedThisOrPrevEpochsTemporal(b, asp.persistent_request, idx);
  step := lemma_EventuallyPersistentRequestInRequestsReceivedThisOrPrevEpochs(b, asp, processing_sync_start, processing_bound, idx);

  forall j {:trigger sat(j, imply(t, next(t)))} | step <= j
    ensures sat(j, imply(t, next(t)))
  {
    lemma_ConstantsAllConsistent(b, asp.c, j);
    lemma_ConstantsAllConsistent(b, asp.c, j+1);
    if sat(j, t) && !sat(j+1, t)
    {
      lemma_AssumptionsMakeValidTransition(b, asp.c, j);
      lemma_OverflowProtectionNotUsedForReplica(b, asp, j, idx);
      var ios := lemma_IfStepRemovesRequestFromBothThisAndPrevEpochsThenItsMaybeExecute(b[j], b[j+1], asp, idx, asp.persistent_request);
      var s := b[j].replicas[idx].replica;
      var s' := b[j+1].replicas[idx].replica;
      var es := s.proposer.election_state;
      var es' := s'.proposer.election_state;
      if asp.persistent_request in es.requests_received_prev_epochs
      {
        var req_idx := lemma_RemoveExecutedRequestBatchRemoval(es.requests_received_prev_epochs, s.executor.next_op_to_execute.v, asp.persistent_request);
        lemma_NextOpToExecuteNeverExceedsSeqno(b, asp, j, idx, req_idx);
        assert ReplySentToClientWithSeqno(b[j], b[j+1], client, seqno, idx, ios, req_idx);
      }
      else
      {
        var req_idx := lemma_RemoveExecutedRequestBatchRemoval(es.requests_received_this_epoch, s.executor.next_op_to_execute.v, asp.persistent_request);
        lemma_NextOpToExecuteNeverExceedsSeqno(b, asp, j, idx, req_idx);
        assert ReplySentToClientWithSeqno(b[j], b[j+1], client, seqno, idx, ios, req_idx);
      }
      lemma_PersistentRequestNeverExecuted(b, asp, idx);
      TemporalDeduceFromAlways(asp.synchrony_start, j, not(RequestWithSeqnoExecutedTemporal(b, client, seqno, idx)));
      assert false;
    }
    reveal next();
    reveal imply();
  }

  TemporalInductionNext(step, t);
  TemporalEventually(processing_sync_start, step, always(t));
}

predicate RequestInRequestsReceivedThisOrPrevEpochsWithSpecificEpochEnd(
  ps:RslState,
  req:Request,
  idx:int,
  epoch_end_time:int
  )
{
  && 0 <= idx < |ps.replicas|
  && var es := ps.replicas[idx].replica.proposer.election_state;
    && es.epoch_end_time == epoch_end_time
    && (req in es.requests_received_prev_epochs || req in es.requests_received_this_epoch)
}

function{:opaque} RequestInRequestsReceivedThisOrPrevEpochsWithSpecificEpochEndTemporal(
  b:Behavior<RslState>,
  req:Request,
  idx:int,
  epoch_end_time:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, RequestInRequestsReceivedThisOrPrevEpochsWithSpecificEpochEndTemporal(b, req, idx, epoch_end_time))} ::
             sat(i, RequestInRequestsReceivedThisOrPrevEpochsWithSpecificEpochEndTemporal(b, req, idx, epoch_end_time)) <==>
             RequestInRequestsReceivedThisOrPrevEpochsWithSpecificEpochEnd(b[i], req, idx, epoch_end_time)
{
  stepmap(imap i :: RequestInRequestsReceivedThisOrPrevEpochsWithSpecificEpochEnd(b[i], req, idx, epoch_end_time))
}

lemma lemma_RequestInRequestsReceivedThisOrPrevEpochsWithSpecificEpochEndLeadsToRequestInRequestsReceivedPrevEpochsWF1Req1(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  idx:int,
  epoch_end_time:int
  )
  requires LivenessAssumptions(b, asp)
  requires idx in asp.live_quorum
  ensures  sat(asp.synchrony_start, always(TemporalWF1Req1(
                 RequestInRequestsReceivedThisOrPrevEpochsWithSpecificEpochEndTemporal(b, asp.persistent_request, idx, epoch_end_time),
                 RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx))))
{
  var P := RequestInRequestsReceivedThisOrPrevEpochsWithSpecificEpochEndTemporal(b, asp.persistent_request, idx, epoch_end_time);
  var Q := RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx);

  forall i | asp.synchrony_start <= i
    ensures sat(i, TemporalWF1Req1(P, Q))
  {
    if sat(i, P) && !sat(i, Q) && !sat(i+1, P) && !sat(i+1, Q)
    {
      lemma_ConstantsAllConsistent(b, asp.c, i);
      lemma_ConstantsAllConsistent(b, asp.c, i+1);
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, idx);
      var nextActionIndex := b[i].replicas[idx].nextActionIndex;
      assert nextActionIndex == 0 || nextActionIndex == 1 || nextActionIndex == 2 || nextActionIndex == 3 ||
             nextActionIndex == 4 || nextActionIndex == 5 || nextActionIndex == 6 || nextActionIndex == 7 ||
             nextActionIndex == 8 || nextActionIndex == 9;
      lemma_OverflowProtectionNotUsedForReplica(b, asp, i, idx);
      var s := b[i].replicas[idx].replica;
      var s' := b[i+1].replicas[idx].replica;
      var es := s.proposer.election_state;
      var es' := s'.proposer.election_state;
      assert asp.persistent_request in es.requests_received_this_epoch;
      assert asp.persistent_request !in es.requests_received_prev_epochs;
      if LReplicaNextSpontaneousMaybeExecute(s, s', ExtractSentPacketsFromIos(ios))
      {
        var req_idx := lemma_RemoveExecutedRequestBatchRemoval(es.requests_received_this_epoch, s.executor.next_op_to_execute.v, asp.persistent_request);
        lemma_NextOpToExecuteNeverExceedsSeqno(b, asp, i, idx, req_idx);
        assert ReplySentToClientWithSeqno(b[i], b[i+1], asp.persistent_request.client, asp.persistent_request.seqno, idx, ios, req_idx);
        lemma_PersistentRequestNeverExecuted(b, asp, idx);
        TemporalDeduceFromAlways(asp.synchrony_start, i, not(RequestWithSeqnoExecutedTemporal(b, asp.persistent_request.client, asp.persistent_request.seqno, idx)));
        assert false;
      }
      else
      {
        if nextActionIndex == 0
        {
          assert false;
        }
        else if nextActionIndex == 1
        {
          assert false;
        }
        else if nextActionIndex == 2
        {
          assert false;
        }
        else if nextActionIndex == 3
        {
          assert false;
        }
        else if nextActionIndex == 4
        {
          assert false;
        }
        else if nextActionIndex == 5
        {
          assert false;
        }
        else if nextActionIndex == 6
        {
          assert false;
        }
        else if nextActionIndex == 7
        {
          assert false;
        }
        else if nextActionIndex == 8
        {
          assert false;
        }
        else if nextActionIndex == 9
        {
          assert false;
        }
        else {
          assert false;
        }
      }
    }
  }

  TemporalAlways(asp.synchrony_start, TemporalWF1Req1(P, Q));
}

lemma lemma_RequestInRequestsReceivedThisOrPrevEpochsWithSpecificEpochEndLeadsToRequestInRequestsReceivedPrevEpochsWF1Req2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  idx:int,
  epoch_end_time:int
  )
  requires LivenessAssumptions(b, asp)
  requires idx in asp.live_quorum
  ensures  sat(asp.synchrony_start, always(TemporalWF1RealTimeDelayedReq2(
                 RequestInRequestsReceivedThisOrPrevEpochsWithSpecificEpochEndTemporal(b, asp.persistent_request, idx, epoch_end_time),
                 RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx),
                 ReplicaSchedule(b, idx)[7],
                 epoch_end_time + asp.max_clock_ambiguity,
                 PaxosTimeMap(b))))
{
  var epochEndTimePlus := epoch_end_time + asp.max_clock_ambiguity;
  var P := RequestInRequestsReceivedThisOrPrevEpochsWithSpecificEpochEndTemporal(b, asp.persistent_request, idx, epoch_end_time);
  var Q := RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx);
  var Action := ReplicaSchedule(b, idx)[7];
  var f := PaxosTimeMap(b);

  forall i | asp.synchrony_start <= i
    ensures sat(i, TemporalWF1RealTimeDelayedReq2(P, Q, Action, epochEndTimePlus, f))
  {
    if sat(i, P) && sat(i, nextafter(Action, epochEndTimePlus, f)) && !sat(i, Q) && !sat(i+1, Q)
    {
      lemma_ConstantsAllConsistent(b, asp.c, i);
      lemma_ConstantsAllConsistent(b, asp.c, i+1);
      assert SpecificClockReadingRslActionOccurs(b[i], b[i+1], LReplicaNextReadClockCheckForViewTimeout, idx);
      var ios:seq<RslIo> :| && RslNextOneReplica(b[i], b[i+1], idx, ios)
                            && SpontaneousIos(ios, 1)
                            && LReplicaNextReadClockCheckForViewTimeout(b[i].replicas[idx].replica, b[i+1].replicas[idx].replica,
                                                                       SpontaneousClock(ios), ExtractSentPacketsFromIos(ios));
      lemma_ClockAmbiguityLimitApplies(b, asp, i, idx, ios[0]);
      lemma_OverflowProtectionNotUsedForReplica(b, asp, i, idx);
      var es := b[i].replicas[idx].replica.proposer.election_state;
      var es' := b[i+1].replicas[idx].replica.proposer.election_state;
      lemma_ClockAmbiguityLimitApplies(b, asp, i, idx, ios[0]);
      assert ElectionStateCheckForViewTimeout(es, es', ios[0].t);
      assert false;
    }
  }

  TemporalAlways(asp.synchrony_start, TemporalWF1RealTimeDelayedReq2(P, Q, Action, epochEndTimePlus, f));
}

lemma lemma_EventuallyPersistentRequestInRequestsReceivedPrevEpochs(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  idx:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires idx in asp.live_quorum
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  ensures  processing_sync_start <= step
  ensures  sat(step, RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx))
{
  var i := lemma_EventuallyPersistentRequestInRequestsReceivedThisOrPrevEpochs(b, asp, processing_sync_start, processing_bound, idx);
  lemma_ConstantsAllConsistent(b, asp.c, i);
  var epoch_end_time := b[i].replicas[idx].replica.proposer.election_state.epoch_end_time;
    
  var P := RequestInRequestsReceivedThisOrPrevEpochsWithSpecificEpochEndTemporal(b, asp.persistent_request, idx, epoch_end_time);
  var Q := RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx);
  var Action := ReplicaSchedule(b, idx)[7];

  Lemma_AlwaysImpliesLaterAlways(asp.synchrony_start, i, TemporalWF1Req1(P, Q));
  Lemma_AlwaysImpliesLaterAlways(asp.synchrony_start, i, TemporalWF1RealTimeDelayedReq2(P, Q, Action, epoch_end_time + asp.max_clock_ambiguity, PaxosTimeMap(b)));

  lemma_RequestInRequestsReceivedThisOrPrevEpochsWithSpecificEpochEndLeadsToRequestInRequestsReceivedPrevEpochsWF1Req1(b, asp, idx, epoch_end_time);
  lemma_RequestInRequestsReceivedThisOrPrevEpochsWithSpecificEpochEndLeadsToRequestInRequestsReceivedPrevEpochsWF1Req2(b, asp, idx, epoch_end_time);
  lemma_ReplicaNextPerformsSubactionPeriodically(b, asp, idx, 7);
  lemma_EstablishRequirementsForWF1RealTimeDelayed(b, asp, i, Action, TimeToPerformGenericAction(asp));
  step := TemporalWF1RealTimeDelayed(i, P, Q, Action, TimeToPerformGenericAction(asp), epoch_end_time + asp.max_clock_ambiguity, PaxosTimeMap(b));
}

lemma lemma_EventuallyPersistentRequestAlwaysInRequestsReceivedPrevEpochs(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  idx:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires idx in asp.live_quorum
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  ensures  processing_sync_start <= step
  ensures  sat(step, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx)))
{
  var client := asp.persistent_request.client;
  var seqno := asp.persistent_request.seqno;
  var t := RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx);
  step := lemma_EventuallyPersistentRequestInRequestsReceivedPrevEpochs(b, asp, processing_sync_start, processing_bound, idx);

  forall j {:trigger sat(j, imply(t, next(t)))} | step <= j
    ensures sat(j, imply(t, next(t)))
  {
    lemma_ConstantsAllConsistent(b, asp.c, j);
    lemma_ConstantsAllConsistent(b, asp.c, j+1);
    if sat(j, t) && !sat(j+1, t)
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, j, idx);
      lemma_OverflowProtectionNotUsedForReplica(b, asp, j, idx);
      var s := b[j].replicas[idx].replica;
      var s' := b[j+1].replicas[idx].replica;
      var es := s.proposer.election_state;
      var es' := s'.proposer.election_state;
      assert LReplicaNextSpontaneousMaybeExecute(s, s', ExtractSentPacketsFromIos(ios));
      var req_idx := lemma_RemoveExecutedRequestBatchRemoval(es.requests_received_prev_epochs, s.executor.next_op_to_execute.v, asp.persistent_request);
      lemma_NextOpToExecuteNeverExceedsSeqno(b, asp, j, idx, req_idx);
      assert ReplySentToClientWithSeqno(b[j], b[j+1], client, seqno, idx, ios, req_idx);
      lemma_PersistentRequestNeverExecuted(b, asp, idx);
      TemporalDeduceFromAlways(asp.synchrony_start, j, not(RequestWithSeqnoExecutedTemporal(b, client, seqno, idx)));
      assert false;
    }
    reveal imply();
    reveal next();
  }

  TemporalInductionNext(step, t);
  TemporalEventually(processing_sync_start, step, always(t));
}

lemma lemma_EventuallyForSomePersistentRequestAlwaysInRequestsReceivedPrevEpochs(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  indices:set<int>
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires indices <= asp.live_quorum
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  ensures  processing_sync_start <= step
  ensures  forall idx {:auto_trigger} :: idx in indices ==> sat(step, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx)))
{
  if |indices| == 0
  {
    step := processing_sync_start;
  }
  else
  {
    var some_index :| some_index in indices;
    var other_indices := indices - {some_index};
    var others_step := lemma_EventuallyForSomePersistentRequestAlwaysInRequestsReceivedPrevEpochs(b, asp, processing_sync_start, processing_bound, other_indices);
    var this_step := lemma_EventuallyPersistentRequestAlwaysInRequestsReceivedPrevEpochs(b, asp, processing_sync_start, processing_bound, some_index);
    step := if others_step > this_step then others_step else this_step;
    forall idx | idx in indices
      ensures sat(step, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx)))
    {
      if step > this_step
      {
        Lemma_AlwaysImpliesLaterAlways(this_step, step, RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx));
      }
      else
      {
        Lemma_AlwaysImpliesLaterAlways(others_step, step, RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx));
      }
    }
  }
}

lemma lemma_EventuallyForAllPersistentRequestAlwaysInRequestsReceivedPrevEpochs(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  ensures  processing_sync_start <= step
  ensures  forall idx :: idx in asp.live_quorum ==> sat(step, always(RequestInRequestsReceivedPrevEpochsTemporal(b, asp.persistent_request, idx)))
{
  step := lemma_EventuallyForSomePersistentRequestAlwaysInRequestsReceivedPrevEpochs(b, asp, processing_sync_start, processing_bound, asp.live_quorum);
}

lemma lemma_PersistentRequestDoesNotIncreasePositionInRequestsReceivedPrevEpochs(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  idx:int,
  step:int,
  n:int
  )
  requires LivenessAssumptions(b, asp)
  requires idx in asp.live_quorum
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires processing_sync_start <= step
  requires sat(step, RequestInFirstNTemporal(b, idx, asp.persistent_request, n))
  ensures  sat(step, always(RequestInFirstNTemporal(b, idx, asp.persistent_request, n)))
{
  var client := asp.persistent_request.client;
  var seqno := asp.persistent_request.seqno;
  var t := RequestInFirstNTemporal(b, idx, asp.persistent_request, n);

  forall j {:trigger sat(j, imply(t, next(t)))} | step <= j
    ensures sat(j, imply(t, next(t)))
  {
    lemma_ConstantsAllConsistent(b, asp.c, j);
    lemma_ConstantsAllConsistent(b, asp.c, j+1);
    if sat(j, t) && !sat(j+1, t)
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, j, idx);
      lemma_OverflowProtectionNotUsedForReplica(b, asp, j, idx);
      var s := b[j].replicas[idx].replica;
      var s' := b[j+1].replicas[idx].replica;
      var es := s.proposer.election_state;
      var es' := s'.proposer.election_state;
      assert RequestInFirstN(b[j], idx, asp.persistent_request, n);
      assert !RequestInFirstN(b[j + 1], idx, asp.persistent_request, n);
      assert s.proposer.election_state.requests_received_prev_epochs != s'.proposer.election_state.requests_received_prev_epochs;
      var nextActionIndex := b[j].replicas[idx].nextActionIndex;
      if (nextActionIndex == 0 || nextActionIndex == 7 || nextActionIndex == 8) {
        assert s.proposer.election_state.requests_received_prev_epochs <= s'.proposer.election_state.requests_received_prev_epochs;
        assert false;
      }
      assert nextActionIndex == 6;
      assert LReplicaNextSpontaneousMaybeExecute(s, s', ExtractSentPacketsFromIos(ios));
      var req_idx := lemma_RemoveExecutedRequestBatchRemovalFromFirstN(es.requests_received_prev_epochs, s.executor.next_op_to_execute.v, asp.persistent_request, n);
      lemma_NextOpToExecuteNeverExceedsSeqno(b, asp, j, idx, req_idx);
      assert ReplySentToClientWithSeqno(b[j], b[j+1], client, seqno, idx, ios, req_idx);
      lemma_PersistentRequestNeverExecuted(b, asp, idx);
      TemporalDeduceFromAlways(asp.synchrony_start, j, not(RequestWithSeqnoExecutedTemporal(b, client, seqno, idx)));
      assert false;
    }
    reveal imply();
    reveal next();
  }

  TemporalInductionNext(step, t);
  TemporalEventually(processing_sync_start, step, always(t));
}

}
