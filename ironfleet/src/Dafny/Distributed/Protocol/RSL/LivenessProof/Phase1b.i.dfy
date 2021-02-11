include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "StablePeriod.i.dfy"
include "ViewAdvance.i.dfy"
include "MaxBallotISent1a.i.dfy"
include "MaxBallot.i.dfy"
include "PacketHandling.i.dfy"
include "Phase1a.i.dfy"
include "../CommonProof/MaxBallotISent1a.i.dfy"
include "../CommonProof/MaxBallot.i.dfy"
include "../CommonProof/Constants.i.dfy"
include "../../../Common/Framework/EnvironmentSynchronyLemmas.i.dfy"

module LivenessProof__Phase1b_i {

import opened LiveRSL__Broadcast_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Message_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__MaxBallotISent1a_i
import opened LivenessProof__MaxBallot_i
import opened LivenessProof__PacketHandling_i
import opened LivenessProof__Phase1a_i
import opened LivenessProof__RealTime_i
import opened LivenessProof__RoundRobin_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__ViewAdvance_i
import opened LivenessProof__ViewChange_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened CommonProof__MaxBallotISent1a_i
import opened CommonProof__MaxBallot_i
import opened CommonProof__PacketSending_i
import opened Liveness__EnvironmentSynchronyLemmas_i
import opened Temporal__Induction_i
import opened Temporal__LeadsTo_i
import opened Temporal__Rules_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Environment_s
import opened Collections__Maps2_s

predicate PrimaryInState1or2(
  ps:RslState,
  view:Ballot
  )
{
  && 0 <= view.proposer_id < |ps.replicas|
  && ps.replicas[view.proposer_id].replica.proposer.max_ballot_i_sent_1a == view
  && (ps.replicas[view.proposer_id].replica.proposer.current_state == 1 || ps.replicas[view.proposer_id].replica.proposer.current_state == 2)
}

function{:opaque} PrimaryInState1or2Temporal(
  b:Behavior<RslState>,
  view:Ballot
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, PrimaryInState1or2Temporal(b, view))} ::
             sat(i, PrimaryInState1or2Temporal(b, view)) == PrimaryInState1or2(b[i], view)
{
  stepmap(imap i :: PrimaryInState1or2(b[i], view))
}

predicate PrimaryInState2(
  ps:RslState,
  view:Ballot
  )
{
  && 0 <= view.proposer_id < |ps.replicas|
  && ps.replicas[view.proposer_id].replica.proposer.max_ballot_i_sent_1a == view
  && ps.replicas[view.proposer_id].replica.proposer.current_state == 2
}

function{:opaque} PrimaryInState2Temporal(
  b:Behavior<RslState>,
  view:Ballot
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, PrimaryInState2Temporal(b, view))} ::
             sat(i, PrimaryInState2Temporal(b, view)) == PrimaryInState2(b[i], view)
{
  stepmap(imap i :: PrimaryInState2(b[i], view))
}

predicate AcceptorHasMaxBalInView(
  ps:RslState,
  view:Ballot,
  idx:int
  )
{
  && 0 <= idx < |ps.replicas|
  && ps.replicas[idx].replica.acceptor.max_bal == view
}

function{:opaque} AcceptorHasMaxBalInViewTemporal(
  b:Behavior<RslState>,
  view:Ballot,
  idx:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, AcceptorHasMaxBalInViewTemporal(b, view, idx))} ::
             sat(i, AcceptorHasMaxBalInViewTemporal(b, view, idx)) == AcceptorHasMaxBalInView(b[i], view, idx)
{
  stepmap(imap i :: AcceptorHasMaxBalInView(b[i], view, idx))
}

predicate PrimaryHasSpecific1bFromAcceptorInView(
  ps:RslState,
  view:Ballot,
  idx:int,
  p:RslPacket
  )
  requires 0 <= view.proposer_id < |ps.replicas|
  requires 0 <= idx < |ps.constants.config.replica_ids|
{
  && p in ps.replicas[view.proposer_id].replica.proposer.received_1b_packets
  && p.msg.RslMessage_1b?
  && p.msg.bal_1b == view
  && p.src == ps.constants.config.replica_ids[idx]
  && ps.replicas[view.proposer_id].replica.proposer.max_ballot_i_sent_1a == view
  && ps.replicas[view.proposer_id].replica.proposer.current_state == 1
}

predicate PrimaryHas1bFromAcceptorInView(
  ps:RslState,
  view:Ballot,
  idx:int
  )
{
  && 0 <= view.proposer_id < |ps.replicas|
  && 0 <= idx < |ps.constants.config.replica_ids|
  && exists p :: PrimaryHasSpecific1bFromAcceptorInView(ps, view, idx, p)
}

function{:opaque} PrimaryHas1bFromAcceptorInViewTemporal(
  b:Behavior<RslState>,
  view:Ballot,
  idx:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, PrimaryHas1bFromAcceptorInViewTemporal(b, view, idx))} ::
             sat(i, PrimaryHas1bFromAcceptorInViewTemporal(b, view, idx)) == PrimaryHas1bFromAcceptorInView(b[i], view, idx)
{
  stepmap(imap i :: PrimaryHas1bFromAcceptorInView(b[i], view, idx))
}

lemma{:timeLimitMultiplier 3} lemma_PrimarySending1aLeadsToAcceptorSettingMaxBal(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  start_step:int,
  processing_bound:int,
  view:Ballot,
  idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, start_step, processing_bound)
  requires view.proposer_id in asp.live_quorum
  requires idx in asp.live_quorum
  ensures  sat(start_step, always(imply(PrimarySent1aInViewTemporal(b, view),
                                        next(eventuallywithin(or(AcceptorHasMaxBalInViewTemporal(b, view, idx), not(NoReplicaBeyondViewTemporal(b, view))), processing_bound, PaxosTimeMap(b))))))
{
  var primary_idx := view.proposer_id;
  var x := PrimarySent1aInViewTemporal(b, view);
  var y := AcceptorHasMaxBalInViewTemporal(b, view, idx);
  var z := not(NoReplicaBeyondViewTemporal(b, view));
  var t := processing_bound;
  var f := PaxosTimeMap(b);

  forall j | start_step <= j
    ensures sat(j, imply(x, next(eventuallywithin(or(y, z), t, f))))
  {
    if sat(j, x)
    {
      lemma_ConstantsAllConsistent(b, asp.c, j);
      lemma_ConstantsAllConsistent(b, asp.c, j+1);
      var ps := b[j];
      var ps' := b[j+1];
      var s := ps.replicas[primary_idx].replica.proposer;
      var s' := ps'.replicas[primary_idx].replica.proposer;
      var ios :| && RslNextOneReplica(ps, ps', view.proposer_id, ios)
                 && LProposerMaybeEnterNewViewAndSend1a(s, s', ExtractSentPacketsFromIos(ios))
                 && s.election_state.current_view.proposer_id == s.constants.my_index
                 && BalLt(s.max_ballot_i_sent_1a, s.election_state.current_view)
                 && s.election_state.current_view == view;
      var sent_packets := ExtractSentPacketsFromIos(ios);
      assert LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, RslMessage_1a(s.election_state.current_view), sent_packets);
      var p := LPacket(s.constants.all.config.replica_ids[idx], s.constants.all.config.replica_ids[s.constants.my_index], RslMessage_1a(s.election_state.current_view));
      assert p in sent_packets;
      var k, ios' := lemma_PacketSentToIndexProcessedByIt(b, asp, start_step, t, j, idx, p);
      lemma_ConstantsAllConsistent(b, asp.c, k);
      lemma_ConstantsAllConsistent(b, asp.c, k+1);
      assert BalLeq(view, b[k+1].replicas[idx].replica.acceptor.max_bal);
      if !sat(k+1, or(y, z))
      {
        lemma_NoReplicaBeyondViewImpliesNoMaxBallotISent1aBeyondView(b, asp, k+1, view);
        lemma_DuringStablePeriodNoMaxBalBeyondView(b, asp, k+1, idx, view);
        assert BalLeq(b[k+1].replicas[idx].replica.acceptor.max_bal, view);
        assert false;
      }
      TemporalEventually(j+1, k+1, beforeabsolutetime(or(y, z), f[j+1] + t, f));
    }
  }
  TemporalAlways(start_step, imply(x, next(eventuallywithin(or(y, z), t, f))));
}

lemma lemma_StablePeriodStartedLeadsToAcceptorSettingMaxBal(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  start_step:int,
  processing_bound:int,
  view:Ballot,
  ahead_idx:int,
  idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, start_step, processing_bound)
  requires view.proposer_id in asp.live_quorum
  requires idx in asp.live_quorum
  ensures  var t := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp) + processing_bound;
           sat(start_step, always(imply(StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx),
                                        or(eventuallynextwithin(and(not(AcceptorHasMaxBalInViewTemporal(b, view, idx)),
                                                                    next(AcceptorHasMaxBalInViewTemporal(b, view, idx))),
                                                                t, PaxosTimeMap(b)),
                                           eventuallywithin(not(NoReplicaBeyondViewTemporal(b, view)), t, PaxosTimeMap(b))))))
{
  var w := StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx);
  var x := PrimarySent1aInViewTemporal(b, view);
  var y := AcceptorHasMaxBalInViewTemporal(b, view, idx);
  var z := not(NoReplicaBeyondViewTemporal(b, view));
  var t1 := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp);
  var t2 := processing_bound;
  var t := t1 + t2;
  var f := PaxosTimeMap(b);

  lemma_StablePeriodStartedLeadsToPrimarySending1a(b, asp, start_step, processing_bound, view, ahead_idx);
  assert sat(start_step, always(imply(w, or(eventuallynextwithin(x, t1, f), eventuallywithin(z, t1, f)))));
  lemma_PrimarySending1aLeadsToAcceptorSettingMaxBal(b, asp, start_step, processing_bound, view, idx);
  assert sat(start_step, always(imply(x, next(eventuallywithin(or(y, z), t2, f)))));
  Lemma_LeadsToTwoPossibilitiesWithinWithFirstStepAnAction(start_step, w, x, y, z, t1, t2, f);
  assert sat(start_step, leadstowithin(w, or(y, z), t1+t2, f));

  forall j | start_step <= j
    ensures sat(j, imply(w, not(y)))
  {
    if sat(j, w) && sat(j, y)
    {
      assert b[j].replicas[idx].replica.acceptor.max_bal == view;
      lemma_MaxBalLeqMaxBallotPrimarySent1a(b, asp.c, j, idx);
      assert BalLt(b[j].replicas[view.proposer_id].replica.proposer.max_ballot_i_sent_1a, view);
      assert false;
    }
  }
  TemporalAlways(start_step, imply(w, not(y)));

  lemma_TimeMonotonicFromInvariantHolds(b, asp, start_step);
  Lemma_LeadsToWithinOrSomethingLeadsToTransitionOrSomething(start_step, w, y, z, t1 + t2, f);
}

lemma lemma_IfPrimaryInState2ItsAlwaysAtLeastThere(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires var t := or(PrimaryInState2Temporal(b, view), not(NoReplicaBeyondViewTemporal(b, view)));
           sat(i, t)
  ensures  var t := or(PrimaryInState2Temporal(b, view), not(NoReplicaBeyondViewTemporal(b, view)));
           sat(i, always(t))
{
  var x := PrimaryInState2Temporal(b, view);
  var y := not(NoReplicaBeyondViewTemporal(b, view));
  var t := or(x, y);
    
  forall j | i <= j
    ensures sat(j, imply(t, next(t)))
  {
    lemma_ConstantsAllConsistent(b, asp.c, j);
    if sat(j, t)
    {
      if sat(j, y)
      {
        var idx :| 0 <= idx < |b[j].replicas| && !BalLeq(CurrentViewOfHost(b[j], idx), view);
        lemma_ViewOfHostMonotonic(b, asp, idx, j, j+1);
        assert sat(j, next(t));
      }
      else
      {
        assert sat(j, x);
        if !sat(j+1, t)
        {
          lemma_BalLtProperties();

          lemma_ConstantsAllConsistent(b, asp.c, j+1);
          var primary_idx := view.proposer_id;
          var s := b[j].replicas[primary_idx].replica;
          var s' := b[j+1].replicas[primary_idx].replica;

          lemma_MaxBallotISent1aMonotonicOneStep(b, asp.c, j, primary_idx);
          assert BalLeq(s.proposer.max_ballot_i_sent_1a, s'.proposer.max_ballot_i_sent_1a);
          assert BalLeq(view, s'.proposer.max_ballot_i_sent_1a);
          lemma_MaxBallotISent1aLeqView(b, asp, j+1, primary_idx);
          assert BalLeq(s'.proposer.max_ballot_i_sent_1a, CurrentViewOfHost(b[j+1], primary_idx));
          assert BalLeq(view, CurrentViewOfHost(b[j+1], primary_idx));
          lemma_ViewOfHostMonotonic(b, asp, primary_idx, j, j+1);
          assert BalLeq(CurrentViewOfHost(b[j+1], primary_idx), view);
          assert CurrentViewOfHost(b[j+1], primary_idx) == view;

          assert BalLeq(CurrentViewOfHost(b[j], primary_idx), view);
          lemma_MaxBallotISent1aLeqView(b, asp, j, primary_idx);
          assert BalLeq(view, CurrentViewOfHost(b[j], primary_idx));
          assert s'.proposer.election_state.current_view == s.proposer.election_state.current_view;

          var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, j, primary_idx);
          assert s.proposer.current_state == 2;
          assert s'.proposer.current_state != 2;
          assert false;
        }
      }
    }
    reveal imply();
    reveal next();
  }
  TemporalInductionNext(i, t);
}

lemma lemma_If2aMessageSentThenPrimaryInState2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  p:RslPacket,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires p.msg.RslMessage_2a?
  requires p.msg.bal_2a == view
  requires 0 <= view.proposer_id < |asp.c.config.replica_ids|
  requires p.src in asp.c.config.replica_ids
  requires p in b[i].environment.sentPackets
  ensures  p.src == asp.c.config.replica_ids[view.proposer_id]
  ensures  var t := or(PrimaryInState2Temporal(b, view), not(NoReplicaBeyondViewTemporal(b, view)));
           sat(i, always(t))
  decreases i
{
  var t := or(PrimaryInState2Temporal(b, view), not(NoReplicaBeyondViewTemporal(b, view)));

  if i == 0
  {
    assert |b[i].environment.sentPackets| == 0;
    assert false;
  }
  else if p in b[i-1].environment.sentPackets
  {
    lemma_If2aMessageSentThenPrimaryInState2(b, asp, i-1, p, view);
    Lemma_AlwaysImpliesLaterAlways(i-1, i, t);
  }
  else
  {
    lemma_AssumptionsMakeValidTransition(b, asp.c, i-1);
    lemma_ConstantsAllConsistent(b, asp.c, i-1);
    var idx, ios := lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i-1], b[i], p);
    assert asp.c.config.replica_ids[idx] == p.src;
    lemma_MaxBallotISent1aHasMeAsProposer(b, asp.c, i, idx);
    assert PrimaryInState2(b[i-1], view);
    assert sat(i-1, PrimaryInState2Temporal(b, view));
    lemma_IfPrimaryInState2ItsAlwaysAtLeastThere(b, asp, i-1, view);
    Lemma_AlwaysImpliesLaterAlways(i-1, i, t);
  }
}

lemma lemma_IfPrimaryInState1or2ItsAlwaysAtLeastThere(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires var t := or(PrimaryInState1or2Temporal(b, view), not(NoReplicaBeyondViewTemporal(b, view)));
           sat(i, t)
  ensures  var t := or(PrimaryInState1or2Temporal(b, view), not(NoReplicaBeyondViewTemporal(b, view)));
           sat(i, always(t))
{
  var x := PrimaryInState1or2Temporal(b, view);
  var y := not(NoReplicaBeyondViewTemporal(b, view));
  var t := or(x, y);
    
  forall j | i <= j
    ensures sat(j, imply(t, next(t)))
  {
    lemma_ConstantsAllConsistent(b, asp.c, j);
    if sat(j, t)
    {
      if sat(j, y)
      {
        var idx :| 0 <= idx < |b[j].replicas| && !BalLeq(CurrentViewOfHost(b[j], idx), view);
        lemma_ViewOfHostMonotonic(b, asp, idx, j, j+1);
        assert sat(j, next(t));
      }
      else
      {
        assert sat(j, x);
        if !sat(j+1, t)
        {
          lemma_BalLtProperties();

          lemma_ConstantsAllConsistent(b, asp.c, j+1);
          var primary_idx := view.proposer_id;
          var s := b[j].replicas[primary_idx].replica;
          var s' := b[j+1].replicas[primary_idx].replica;

          lemma_MaxBallotISent1aMonotonicOneStep(b, asp.c, j, primary_idx);
          assert BalLeq(s.proposer.max_ballot_i_sent_1a, s'.proposer.max_ballot_i_sent_1a);
          assert BalLeq(view, s'.proposer.max_ballot_i_sent_1a);
          lemma_MaxBallotISent1aLeqView(b, asp, j+1, primary_idx);
          assert BalLeq(s'.proposer.max_ballot_i_sent_1a, CurrentViewOfHost(b[j+1], primary_idx));
          assert BalLeq(view, CurrentViewOfHost(b[j+1], primary_idx));
          lemma_ViewOfHostMonotonic(b, asp, primary_idx, j, j+1);
          assert BalLeq(CurrentViewOfHost(b[j+1], primary_idx), view);
          assert CurrentViewOfHost(b[j+1], primary_idx) == view;

          assert BalLeq(CurrentViewOfHost(b[j], primary_idx), view);
          lemma_MaxBallotISent1aLeqView(b, asp, j, primary_idx);
          assert BalLeq(view, CurrentViewOfHost(b[j], primary_idx));
          assert s'.proposer.election_state.current_view == s.proposer.election_state.current_view;

          var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, j, primary_idx);
          assert s.proposer.current_state >= 2;
          assert s'.proposer.current_state == 0;
          assert false;
        }
      }
    }
    reveal imply();
    reveal next();
  }
  TemporalInductionNext(i, t);
}

lemma lemma_If1aMessageSentThenPrimaryInState1or2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  p:RslPacket,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires p.msg.RslMessage_1a?
  requires p.msg.bal_1a == view
  requires 0 <= view.proposer_id < |asp.c.config.replica_ids|
  requires p.src in asp.c.config.replica_ids
  requires p in b[i].environment.sentPackets
  ensures  p.src == asp.c.config.replica_ids[view.proposer_id]
  ensures  var t := or(PrimaryInState1or2Temporal(b, view), not(NoReplicaBeyondViewTemporal(b, view)));
           sat(i, always(t))
  decreases i
{
  var t := or(PrimaryInState1or2Temporal(b, view), not(NoReplicaBeyondViewTemporal(b, view)));

  if i == 0
  {
    assert |b[i].environment.sentPackets| == 0;
    assert false;
  }
  else if p in b[i-1].environment.sentPackets
  {
    lemma_If1aMessageSentThenPrimaryInState1or2(b, asp, i-1, p, view);
    Lemma_AlwaysImpliesLaterAlways(i-1, i, t);
  }
  else
  {
    lemma_AssumptionsMakeValidTransition(b, asp.c, i-1);
    lemma_ConstantsAllConsistent(b, asp.c, i-1);
    var idx, ios := lemma_ActionThatSends1aIsMaybeEnterNewViewAndSend1a(b[i-1], b[i], p);
    assert asp.c.config.replica_ids[idx] == p.src;
    lemma_MaxBallotISent1aHasMeAsProposer(b, asp.c, i, idx);
    assert sat(i, PrimaryInState1or2Temporal(b, view));
    lemma_IfPrimaryInState1or2ItsAlwaysAtLeastThere(b, asp, i, view);
  }
}

}
