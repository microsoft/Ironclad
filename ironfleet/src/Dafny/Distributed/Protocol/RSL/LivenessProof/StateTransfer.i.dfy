include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "Phase2Invariants.i.dfy"
include "../CommonProof/Actions.i.dfy"
include "../CommonProof/PacketSending.i.dfy"
include "../CommonProof/MaxBallotISent1a.i.dfy"
include "../CommonProof/Environment.i.dfy"
include "../CommonProof/Chosen.i.dfy"
include "../CommonProof/Quorum.i.dfy"
include "../CommonProof/Received1b.i.dfy"

module LivenessProof__StateTransfer_i {

import opened LiveRSL__Configuration_i
import opened LiveRSL__Constants_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__MaxBallotISent1a_i
import opened LivenessProof__Phase2Invariants_i
import opened LivenessProof__StablePeriod_i
import opened CommonProof__Actions_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Chosen_i
import opened CommonProof__Constants_i
import opened CommonProof__Environment_i
import opened CommonProof__LogTruncationPoint_i
import opened CommonProof__MaxBallotISent1a_i
import opened CommonProof__Message1b_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Quorum_i
import opened CommonProof__Received1b_i
import opened Temporal__Temporal_s
import opened Temporal__Rules_i
import opened Environment_s
import opened Collections__Maps2_s

lemma lemma_AppStateSupplyImpliesAppStateRequest(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p_state_supply:RslPacket
  ) returns (
  p_state_req:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p_state_supply in b[i].environment.sentPackets
  requires p_state_supply.src in c.config.replica_ids
  requires p_state_supply.msg.RslMessage_AppStateSupply?
  ensures  p_state_req in b[i].environment.sentPackets
  ensures  p_state_req.src in c.config.replica_ids
  ensures  p_state_req.src == p_state_supply.dst
  ensures  p_state_req.msg.RslMessage_AppStateRequest?
  ensures  BalLeq(p_state_supply.msg.bal_state_supply, p_state_req.msg.bal_state_req)
{
  if i == 0 { return; }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);

  if p_state_supply in b[i-1].environment.sentPackets
  {
    p_state_req := lemma_AppStateSupplyImpliesAppStateRequest(b, c, i-1, p_state_supply);
    lemma_PacketStaysInSentPackets(b, c, i-1, i, p_state_req);
    return;
  }

  var idx, ios := lemma_ActionThatSendsAppStateSupplyIsProcessAppStateRequest(b[i-1], b[i], p_state_supply);
  p_state_req := ios[0].r;
  assert IsValidLIoOp(ios[0], c.config.replica_ids[idx], b[i-1].environment);
}

lemma{:timeLimitMultiplier 2} lemma_StateRequestFromKingPrecedesBallotDuringStableView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  i:int,
  p_state_req:RslPacket
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires 0 <= i
  requires p_state_req in b[i].environment.sentPackets
  requires p_state_req.src == asp.c.config.replica_ids[h.king_idx]
  requires p_state_req.msg.RslMessage_AppStateRequest?
  requires NoReplicaBeyondView(b[i], h.view)
  ensures  BalLt(p_state_req.msg.bal_state_req, h.view)
{
  if i == 0 { return; }

  lemma_ConstantsAllConsistent(b, asp.c, i-1);
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_AssumptionsMakeValidTransition(b, asp.c, i-1);

  if p_state_req in b[i-1].environment.sentPackets
  {
    lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, i-1, i, h.view);
    lemma_StateRequestFromKingPrecedesBallotDuringStableView(b, asp, h, i-1, p_state_req);
    return;
  }

  var king_idx, king_ios := lemma_ActionThatSendsAppStateRequestIsProcessStartingPhase2(b[i-1], b[i], p_state_req);
  var p_starting_phase2 := king_ios[0].r;
  assert ReplicasDistinct(asp.c.config.replica_ids, king_idx, h.king_idx);
  assert b[i].replicas[king_idx].replica.executor.ops_complete < p_starting_phase2.msg.logTruncationPoint_2;

  var x := stepmap(imap j :: p_starting_phase2 in b[j].environment.sentPackets);
  var next_step := earliestStepBetween(0, i, x);
  var step := next_step - 1;
  assert !sat(0, x);
  assert !sat(step, x);

  lemma_ConstantsAllConsistent(b, asp.c, step);
  lemma_ConstantsAllConsistent(b, asp.c, next_step);
  lemma_AssumptionsMakeValidTransition(b, asp.c, step);
    
  var primary_idx, primary_ios := lemma_ActionThatSendsStartingPhase2IsMaybeEnterPhase2(b[step], b[next_step], p_starting_phase2);
    
  var s := b[step].replicas[primary_idx].replica.proposer;
  var s' := b[next_step].replicas[primary_idx].replica.proposer;

  lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, step, i, h.view);
  lemma_NoReplicaBeyondViewImpliesNoMaxBallotISent1aBeyondView(b, asp, step, h.view);
  assert BalLeq(s.max_ballot_i_sent_1a, h.view);

  if BalLt(s.max_ballot_i_sent_1a, h.view)
  {
    return;
  }

  lemma_MaxBallotISent1aHasMeAsProposer(b, asp.c, step, primary_idx);

  if next_step <= h.start_step
  {
    lemma_MaxBallotISent1aMonotonic(b, asp.c, next_step, h.start_step, primary_idx);
    assert false;
  }

  if next_step > h.start_step + 1
  {
    lemma_MaxBallotISent1aMonotonic(b, asp.c, h.start_step + 1, step, primary_idx);
    assert false;
  }

  assert p_starting_phase2.msg.logTruncationPoint_2 == h.log_truncation_point;
  assert h.start_step + 1 <= i;
  lemma_OpsCompleteMonotonic(b, asp.c, h.start_step + 1, i, h.king_idx);
  assert false;
}

lemma lemma_StateSupplyToKingPrecedesBallotDuringStableView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  i:int,
  p:RslPacket
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in asp.c.config.replica_ids
  requires p.dst == asp.c.config.replica_ids[h.king_idx]
  requires p.msg.RslMessage_AppStateSupply?
  requires NoReplicaBeyondView(b[i], h.view)
  ensures  BalLt(p.msg.bal_state_supply, h.view)
{
  if i == 0 { return; }

  lemma_ConstantsAllConsistent(b, asp.c, i-1);
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_AssumptionsMakeValidTransition(b, asp.c, i-1);
  lemma_IfNoReplicaBeyondViewNowThenNoReplicaBeyondViewEarlier(b, asp, i-1, i, h.view);

  if p in b[i-1].environment.sentPackets
  {
    lemma_StateSupplyToKingPrecedesBallotDuringStableView(b, asp, h, i-1, p);
    return;
  }

  var idx, ios := lemma_ActionThatSendsAppStateSupplyIsProcessAppStateRequest(b[i-1], b[i], p);
  var p_state_req := ios[0].r;
  lemma_StateRequestFromKingPrecedesBallotDuringStableView(b, asp, h, i-1, p_state_req);
}

lemma lemma_QuorumOf1bsFromPhase2StartPrecludesQuorumOf2bsFromEarlierView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  i:int,
  q:QuorumOf2bs
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires 0 <= i
  requires LAllAcceptorsHadNoProposal(b[h.start_step + 1].replicas[h.view.proposer_id].replica.proposer.received_1b_packets, q.opn)
  requires LIsAfterLogTruncationPoint(q.opn, b[h.start_step + 1].replicas[h.view.proposer_id].replica.proposer.received_1b_packets)
  requires IsValidQuorumOf2bs(b[i], q)
  ensures  BalLeq(h.view, q.bal)
{
  lemma_ConstantsAllConsistent(b, asp.c, h.start_step + 1);
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_Received1bPacketsAreFromMaxBallotISent1a(b, asp.c, h.start_step + 1, h.view.proposer_id);

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, h.start_step, h.view.proposer_id);
    
  var received_1b_packets := b[h.start_step + 1].replicas[h.view.proposer_id].replica.proposer.received_1b_packets;
  var received1b_indices := lemma_GetIndicesFromPackets(received_1b_packets, asp.c.config);
  var overlap_idx := lemma_QuorumIndexOverlap(q.indices, received1b_indices, |asp.c.config.replica_ids|);
  var packet_1b :| packet_1b in received_1b_packets && packet_1b.src == asp.c.config.replica_ids[overlap_idx];
  var packet_2b := q.packets[overlap_idx];

  var later_step := if h.start_step + 1 <= i then i else h.start_step + 1;
  lemma_PacketStaysInSentPackets(b, asp.c, h.start_step + 1, later_step, packet_1b);
  lemma_PacketStaysInSentPackets(b, asp.c, i, later_step, packet_2b);
    
  lemma_1bMessageWithoutOpnImplicationsFor2b(b, asp.c, later_step, q.opn, packet_1b, packet_2b);
}

lemma lemma_StateSupplyToKingDoesNotIncludeOpn(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  h:Phase2Params,
  i:int,
  opn:OperationNumber,
  p:RslPacket
  )
  requires Phase2StableWithRequest(b, asp, h)
  requires 0 <= i
  requires 0 <= opn
  requires p in b[i].environment.sentPackets
  requires p.src in asp.c.config.replica_ids
  requires p.dst == asp.c.config.replica_ids[h.king_idx]
  requires p.msg.RslMessage_AppStateSupply?
  requires LIsAfterLogTruncationPoint(opn, b[h.start_step + 1].replicas[h.view.proposer_id].replica.proposer.received_1b_packets)
  requires LAllAcceptorsHadNoProposal(b[h.start_step + 1].replicas[h.view.proposer_id].replica.proposer.received_1b_packets, opn)
  requires NoReplicaBeyondView(b[i], h.view)
  ensures  p.msg.opn_state_supply <= opn
{
  lemma_StateSupplyToKingPrecedesBallotDuringStableView(b, asp, h, i, p);
  assert BalLt(p.msg.bal_state_supply, h.view);
  var qs := lemma_TransferredStateBasedOnChosenOperations(b, asp.c, i, p);

  if p.msg.opn_state_supply > opn
  {
    var q := qs[opn];
    assert BalLeq(q.bal, p.msg.bal_state_supply);
    assert BalLt(q.bal, h.view);

    lemma_QuorumOf1bsFromPhase2StartPrecludesQuorumOf2bsFromEarlierView(b, asp, h, i, q);
    assert false;
  }
}

}
