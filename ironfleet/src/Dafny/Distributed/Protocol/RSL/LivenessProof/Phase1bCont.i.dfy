include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "StablePeriod.i.dfy"
include "ViewAdvance.i.dfy"
include "MaxBallotISent1a.i.dfy"
include "MaxBallot.i.dfy"
include "PacketHandling.i.dfy"
include "Phase1b.i.dfy"
include "../CommonProof/MaxBallotISent1a.i.dfy"
include "../CommonProof/MaxBallot.i.dfy"
include "../CommonProof/Constants.i.dfy"
include "../../../Common/Framework/EnvironmentSynchronyLemmas.i.dfy"
include "../../../Common/Logic/Temporal/Sets.i.dfy"
include "../../../Common/Collections/Sets.i.dfy"

module LivenessProof__Phase1bCont_i {

import opened LiveRSL__Acceptor_i
import opened LiveRSL__Configuration_i
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
import opened LivenessProof__Phase1b_i
import opened LivenessProof__RealTime_i
import opened LivenessProof__RoundRobin_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__ViewAdvance_i
import opened LivenessProof__ViewChange_i
import opened LivenessProof__WF1_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened CommonProof__MaxBallotISent1a_i
import opened CommonProof__MaxBallot_i
import opened Liveness__EnvironmentSynchronyLemmas_i
import opened Temporal__Heuristics_i
import opened Temporal__Induction_i
import opened Temporal__LeadsTo_i
import opened Temporal__Rules_i
import opened Temporal__Sets_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Temporal__Time_i
import opened Temporal__WF1_i
import opened Collections__Sets_i
import opened Collections__Maps2_s
import opened Collections__Maps2_i
import opened Environment_s

predicate AcceptorSent1bInView(
    ps:RslState,
    ps':RslState,
    view:Ballot,
    idx:int
    )
{
  && PrimaryInState1or2(ps, view)
  && 0 <= idx < |ps.replicas|
  && 0 <= idx < |ps'.replicas|
  && ps.environment.nextStep.LEnvStepHostIos?
  && var ios := ps.environment.nextStep.ios;
     var s := ps.replicas[idx].replica.acceptor;
     var s' := ps'.replicas[idx].replica.acceptor;
     && RslNextOneReplica(ps, ps', idx, ios)
     && |ios| > 0
     && ios[0].LIoOpReceive?
     && ios[0].r.msg.RslMessage_1a?
     && ios[0].r.msg.bal_1a == view
     && BalLt(s.max_bal, view)
     && s'.max_bal == view
     && LAcceptorProcess1a(s, s', ios[0].r, ExtractSentPacketsFromIos(ios))
}

function{:opaque} AcceptorSent1bInViewTemporal(
  b:Behavior<RslState>,
  view:Ballot,
  idx:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, AcceptorSent1bInViewTemporal(b, view, idx))} ::
             sat(i, AcceptorSent1bInViewTemporal(b, view, idx)) == AcceptorSent1bInView(b[i], b[nextstep(i)], view, idx)
{
  stepmap(imap i :: AcceptorSent1bInView(b[i], b[nextstep(i)], view, idx))
}

function PrimaryHas1bFromAcceptorOrIsPastPhase1Temporal(
  b:Behavior<RslState>,
  view:Ballot,
  idx:int
  ):temporal
  requires imaptotal(b)
{
  or(PrimaryHas1bFromAcceptorInViewTemporal(b, view, idx),
     or(PrimaryInState2Temporal(b, view), not(NoReplicaBeyondViewTemporal(b, view))))
}

lemma lemma_StablePeriodStartedLeadsToAcceptorSending1b(
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
           var f := PaxosTimeMap(b);
           sat(start_step, always(imply(StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx),
                                        or(eventuallynextwithin(AcceptorSent1bInViewTemporal(b, view, idx), t, f),
                                           eventuallywithin(or(PrimaryInState2Temporal(b, view),
                                                               not(NoReplicaBeyondViewTemporal(b, view))), t, f)))))
{
  var t := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp) + processing_bound;
  var f := PaxosTimeMap(b);
  var a := AcceptorHasMaxBalInViewTemporal(b, view, idx);
  var w := StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx);
  var x := AcceptorSent1bInViewTemporal(b, view, idx);
  var y := PrimaryInState2Temporal(b, view);
  var z := not(NoReplicaBeyondViewTemporal(b, view));

  lemma_StablePeriodStartedLeadsToAcceptorSettingMaxBal(b, asp, start_step, processing_bound, view, ahead_idx, idx);
  assert sat(start_step, always(imply(w, or(eventuallynextwithin(and(not(a), next(a)), t, f), eventuallywithin(z, t, f)))));

  forall j | start_step <= j
    ensures sat(j, imply(w, or(eventuallynextwithin(x, t, f), eventuallywithin(or(y, z), t, f))))
  {
    if sat(j, w)
    {
      if sat(j, eventuallywithin(z, t, f))
      {
        var k := TemporalDeduceFromEventuallyWithin(j, z, t, f);
        TemporalEventuallyWithin(j, k, or(y, z), t, f);
      }
      else
      {
        TemporalDeduceFromAlways(start_step, j, imply(w, or(eventuallynextwithin(and(not(a), next(a)), t, f), eventuallywithin(z, t, f))));
        var k := TemporalDeduceFromEventuallyNextWithin(j, and(not(a), next(a)), t, f);
        lemma_ConstantsAllConsistent(b, asp.c, k);
        lemma_ConstantsAllConsistent(b, asp.c, k+1);
        var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, k, idx);
        var s := b[k].replicas[idx].replica;
        assert b[k].replicas[idx].nextActionIndex == 0;
        assert |ios| > 0;
        assert ios[0].LIoOpReceive?;
        lemma_PacketProcessedImpliesPacketSent(b[k], b[k+1], idx, ios, ios[0].r);
        if ios[0].r.msg.RslMessage_1a?
        {
          lemma_If1aMessageSentThenPrimaryInState1or2(b, asp, k, ios[0].r, view);
          TemporalDeduceFromAlways(k, k, or(PrimaryInState1or2Temporal(b, view), not(NoReplicaBeyondViewTemporal(b, view))));
          if sat(k, z)
          {
            TemporalEventuallyWithin(j, k, or(y, z), t, f);
          }
          else
          {
            assert AcceptorSent1bInView(b[k], b[k+1], view, idx);
            assert sat(k, x);
            TemporalEventuallyNextWithin(j, k, x, t, f);
          }
        }
        else if ios[0].r.msg.RslMessage_2a?
        {
          lemma_If2aMessageSentThenPrimaryInState2(b, asp, k, ios[0].r, view);
          TemporalDeduceFromAlways(k, k, or(PrimaryInState2Temporal(b, view), not(NoReplicaBeyondViewTemporal(b, view))));
          assert sat(k, or(y, z));
          TemporalEventuallyWithin(j, k, or(y, z), t, f);
        }
        else
        {
          assert false;
        }
      }
    }
  }

  TemporalAlways(start_step, imply(w, or(eventuallynextwithin(x, t, f), eventuallywithin(or(y, z), t, f))));
}

lemma lemma_StablePeriodStartedLeadsToPrimaryGetting1bFromAcceptorHelper(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  start_step:int,
  processing_bound:int,
  view:Ballot,
  idx:int,
  i:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, start_step, processing_bound)
  requires view.proposer_id in asp.live_quorum
  requires idx in asp.live_quorum
  requires start_step <= i
  requires sat(i, AcceptorSent1bInViewTemporal(b, view, idx))
  ensures  TLe(i, step)
  ensures  sat(step, or(PrimaryHas1bFromAcceptorInViewTemporal(b, view, idx),
                     or(PrimaryInState2Temporal(b, view),
                     not(NoReplicaBeyondViewTemporal(b, view)))))
  ensures  b[step].environment.time <= b[i+1].environment.time + processing_bound
{
  var t := processing_bound;
  var f := PaxosTimeMap(b);

  assert sat(i, PrimaryInState1or2Temporal(b, view));
  assert AcceptorSent1bInView(b[i], b[i+1], view, idx);
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i+1);
  var primary_idx := view.proposer_id;
  var s := b[i].replicas[idx].replica.acceptor;
  var s' := b[i+1].replicas[idx].replica.acceptor;
  var ios:seq<RslIo> :| && RslNextOneReplica(b[i], b[i+1], idx, ios)
                        && |ios| > 0
                        && ios[0].LIoOpReceive?
                        && ios[0].r.msg.RslMessage_1a?
                        && ios[0].r.msg.bal_1a == view
                        && BalLt(s.max_bal, view)
                        && s'.max_bal == view
                        && LAcceptorProcess1a(s, s', ios[0].r, ExtractSentPacketsFromIos(ios));
  var sent_packets := ExtractSentPacketsFromIos(ios);
  var p := LPacket(ios[0].r.src, s.constants.all.config.replica_ids[s.constants.my_index], RslMessage_1b(view, s.log_truncation_point, s.votes));
  assert p in sent_packets;
  lemma_PacketProcessedImpliesPacketSent(b[i], b[i+1], idx, ios, ios[0].r);
  lemma_If1aMessageSentThenPrimaryInState1or2(b, asp, i, ios[0].r, view);
  assert p.dst == asp.c.config.replica_ids[primary_idx];
  var j, ios2 := lemma_PacketSentToIndexProcessedByIt(b, asp, start_step, t, i, primary_idx, p);
  lemma_ConstantsAllConsistent(b, asp.c, j);
  lemma_ConstantsAllConsistent(b, asp.c, j+1);
  step := j + 1;

  var s2 := b[j].replicas[primary_idx].replica;
  var s2' := b[j+1].replicas[primary_idx].replica;

  assert PacketProcessedViaIos(b[j], b[j+1], p, primary_idx, ios2);
  assert LReplicaNextProcess1b(s2, s2', p, ExtractSentPacketsFromIos(ios2));
  assert p.src in s2.proposer.constants.all.config.replica_ids;
  lemma_IfPrimaryInState1or2ItsAlwaysAtLeastThere(b, asp, i, view);
  TemporalDeduceFromAlways(i, j, or(PrimaryInState1or2Temporal(b, view), not(NoReplicaBeyondViewTemporal(b, view))));

  var x := PrimaryHas1bFromAcceptorInViewTemporal(b, view, idx);
  var y := PrimaryInState2Temporal(b, view);
  var z := not(NoReplicaBeyondViewTemporal(b, view));

  if sat(j, or(y, z))
  {
    step := j;
    lemma_TimeAdvancesBetween(b, asp, j, j+1);
  }
  else
  {
    assert s2.proposer.max_ballot_i_sent_1a == view;
    assert s2.proposer.current_state == 1;
    step := j + 1;
    if exists other_packet :: other_packet in s2.proposer.received_1b_packets && other_packet.src == p.src
    {
      var other_packet :| other_packet in s2.proposer.received_1b_packets && other_packet.src == p.src;
      lemma_Received1bPacketsAreFromMaxBallotISent1a(b, asp.c, step, primary_idx);
      assert other_packet.msg.RslMessage_1b? && other_packet.msg.bal_1b == s2.proposer.max_ballot_i_sent_1a;
      assert PrimaryHasSpecific1bFromAcceptorInView(b[step], view, idx, other_packet);
    }
    else
    {
      assert PrimaryHasSpecific1bFromAcceptorInView(b[step], view, idx, p);
    }
    assert sat(step, x);
  }
}

lemma lemma_StablePeriodStartedLeadsToPrimaryGetting1bFromAcceptor(
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
  ensures  var t := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp) + processing_bound * 2;
           var f := PaxosTimeMap(b);
           sat(start_step, leadstowithin(StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx),
                                         PrimaryHas1bFromAcceptorOrIsPastPhase1Temporal(b, view, idx), t, f))
{
  var t1 := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp) + processing_bound;
  var t2 := processing_bound;
  var t := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp) + processing_bound * 2;
  var f := PaxosTimeMap(b);
  var a := AcceptorSent1bInViewTemporal(b, view, idx);
  var w := StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx);
  var x := PrimaryHas1bFromAcceptorInViewTemporal(b, view, idx);
  var y := PrimaryInState2Temporal(b, view);
  var z := not(NoReplicaBeyondViewTemporal(b, view));

  assert t == t1 + t2;

  lemma_StablePeriodStartedLeadsToAcceptorSending1b(b, asp, start_step, processing_bound, view, ahead_idx, idx);
  assert sat(start_step, always(imply(w, or(eventuallynextwithin(a, t1, f), eventuallywithin(or(y, z), t1, f)))));

  TemporalAssist();

  forall j | start_step <= j
    ensures sat(j, imply(w, eventuallywithin(or(x, or(y, z)), t, f)))
  {
    if sat(j, w)
    {
      TemporalDeduceFromAlways(start_step, j, imply(w, or(eventuallynextwithin(a, t1, f), eventuallywithin(or(y, z), t1, f))));
      if sat(j, eventuallywithin(or(y, z), t1, f))
      {
        assert sat(j, eventuallywithin(or(x, or(y, z)), t1, f));
        assert sat(j, eventuallywithin(or(x, or(y, z)), t, f));
      }
      else
      {
        assert sat(j, eventuallynextwithin(a, t1, f));
        var k :| TLe(j, k) && sat(k, nextbefore(a, f[j] + t1, f));
        var m := lemma_StablePeriodStartedLeadsToPrimaryGetting1bFromAcceptorHelper(b, asp, start_step, processing_bound, view, idx, k);
        assert sat(m, beforeabsolutetime(or(x, or(y, z)), f[k+1] + t2, f));
        assert sat(m, beforeabsolutetime(or(x, or(y, z)), f[j] + t, f));
      }
    }
  }
}

lemma lemma_PrimaryHas1bFromAcceptorOrIsPastPhase1Stable(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  view:Ballot,
  idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires 0 <= view.proposer_id < |asp.c.config.replica_ids|
  ensures  sat(i, always(imply(PrimaryHas1bFromAcceptorOrIsPastPhase1Temporal(b, view, idx),
                               always(PrimaryHas1bFromAcceptorOrIsPastPhase1Temporal(b, view, idx)))))
{
  var x := PrimaryHas1bFromAcceptorInViewTemporal(b, view, idx);
  var y := PrimaryInState2Temporal(b, view);
  var z := not(NoReplicaBeyondViewTemporal(b, view));
  var t := PrimaryHas1bFromAcceptorOrIsPastPhase1Temporal(b, view, idx);
    
  forall j | i <= j && sat(j, t)
    ensures sat(j, always(t))
  {
    forall k | j <= k && sat(k, t) && !sat(k+1, t)
      ensures false
    {
      if sat(k, or(y, z))
      {
        lemma_IfPrimaryInState2ItsAlwaysAtLeastThere(b, asp, k, view);
        TemporalDeduceFromAlways(k, k+1, or(y, z));
        assert sat(k+1, t);
        assert false;
      }
      else
      {
        assert sat(k, x);
        var p :| PrimaryHasSpecific1bFromAcceptorInView(b[k], view, idx, p);

        lemma_ConstantsAllConsistent(b, asp.c, k);
        lemma_ConstantsAllConsistent(b, asp.c, k+1);
        var primary_idx := view.proposer_id;
        var s := b[k].replicas[primary_idx].replica;
        var s' := b[k+1].replicas[primary_idx].replica;
                
        lemma_NoReplicaBeyondViewImpliesNoMaxBallotISent1aBeyondView(b, asp, k, view);
        lemma_MaxBallotISent1aLeqView(b, asp, k, primary_idx);
        assert BalLeq(s.proposer.max_ballot_i_sent_1a, s.proposer.election_state.current_view);
        assert BalLeq(CurrentViewOfHost(b[k], primary_idx), view);
        assert s.proposer.election_state.current_view == view;

        lemma_ViewOfHostMonotonic(b, asp, primary_idx, k, k+1);
        assert BalLeq(s.proposer.election_state.current_view, s'.proposer.election_state.current_view);
        assert BalLeq(CurrentViewOfHost(b[k+1], primary_idx), view);
        assert s'.proposer.election_state.current_view == view;
    
        lemma_MaxBallotISent1aLeqView(b, asp, k+1, primary_idx);
        lemma_MaxBallotISent1aMonotonicOneStep(b, asp.c, k, primary_idx);
        assert s'.proposer.max_ballot_i_sent_1a == view;

        assert !PrimaryHasSpecific1bFromAcceptorInView(b[k+1], view, idx, p);
        var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, k, primary_idx);
        assert false;
      }
    }
    TemporalInductionNext(j, t);
  }
  TemporalAlways(i, imply(t, always(t)));
}

lemma lemma_StablePeriodStartedLeadsToPrimaryGetting1bFromAcceptorForever(
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
  ensures  var t := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp) + processing_bound * 2;
           var f := PaxosTimeMap(b);
           sat(start_step, leadstowithin(StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx),
                                         always(PrimaryHas1bFromAcceptorOrIsPastPhase1Temporal(b, view, idx)), t, f))
{
  var t := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp) + processing_bound * 2;
  var f := PaxosTimeMap(b);
  lemma_StablePeriodStartedLeadsToPrimaryGetting1bFromAcceptor(b, asp, start_step, processing_bound, view, ahead_idx, idx);
  lemma_PrimaryHas1bFromAcceptorOrIsPastPhase1Stable(b, asp, start_step, view, idx);
  Lemma_LeadsToWithinImpliesLeadsToConsequenceWithin(start_step,
                                                     StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx),
                                                     PrimaryHas1bFromAcceptorOrIsPastPhase1Temporal(b, view, idx),
                                                     always(PrimaryHas1bFromAcceptorOrIsPastPhase1Temporal(b, view, idx)),
                                                     t,
                                                     f);
}

function{:opaque} PrimaryHas1bFromAllLiveAcceptorsOrIsPastPhase1TemporalSet(
  b:Behavior<RslState>,
  live_quorum:set<int>,
  view:Ballot
  ):set<temporal>
  requires imaptotal(b)
  ensures  forall idx :: idx in live_quorum ==>
                 PrimaryHas1bFromAcceptorOrIsPastPhase1Temporal(b, view, idx) in PrimaryHas1bFromAllLiveAcceptorsOrIsPastPhase1TemporalSet(b, live_quorum, view)
  ensures  forall x :: x in PrimaryHas1bFromAllLiveAcceptorsOrIsPastPhase1TemporalSet(b, live_quorum, view) ==>
                 exists idx :: idx in live_quorum && x == PrimaryHas1bFromAcceptorOrIsPastPhase1Temporal(b, view, idx)
{
  set idx | idx in live_quorum :: PrimaryHas1bFromAcceptorOrIsPastPhase1Temporal(b, view, idx)
}

lemma lemma_StablePeriodStartedLeadsToPrimaryGetting1bFromEveryLiveAcceptorForever(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  start_step:int,
  processing_bound:int,
  view:Ballot,
  ahead_idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, start_step, processing_bound)
  requires view.proposer_id in asp.live_quorum
  ensures  var t := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp) + processing_bound * 2;
           var f := PaxosTimeMap(b);
           var xs := PrimaryHas1bFromAllLiveAcceptorsOrIsPastPhase1TemporalSet(b, asp.live_quorum, view);
           sat(start_step, leadstowithin(StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx), always(andset(xs)), t, f))
{
  var t := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp) + processing_bound * 2;
  var f := PaxosTimeMap(b);
  var w := StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx);
  var xs := PrimaryHas1bFromAllLiveAcceptorsOrIsPastPhase1TemporalSet(b, asp.live_quorum, view);
  forall x | x in xs
    ensures sat(start_step, leadstowithin(w, always(x), t, f))
  {
    var idx :| idx in asp.live_quorum && x == PrimaryHas1bFromAcceptorOrIsPastPhase1Temporal(b, view, idx);
    lemma_StablePeriodStartedLeadsToPrimaryGetting1bFromAcceptorForever(b, asp, start_step, processing_bound, view, ahead_idx, idx);
  }
  Lemma_LeadsToAlwaysEachWithinImpliesLeadsToAlwaysAllWithin(start_step, w, xs, t, f);
}

lemma lemma_PrimaryHas1bFromAllLiveAcceptorsLeadsToPrimaryEnteringPhase2WF1Req2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  start_step:int,
  i:int,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires view.proposer_id in asp.live_quorum
  requires 0 <= start_step <= i
  ensures  var primary_idx := view.proposer_id;
           var xs := PrimaryHas1bFromAllLiveAcceptorsOrIsPastPhase1TemporalSet(b, asp.live_quorum, view);
           var P := always(andset(xs));
           var Q := or(PrimaryInState2Temporal(b, view), not(NoReplicaBeyondViewTemporal(b, view)));
           var Action := MakeRslActionTemporalFromSpontaneousReplicaFunction(b, LReplicaNextSpontaneousMaybeEnterPhase2, primary_idx);
           sat(i, TemporalWF1Req2(P, Q, Action))
{
  var primary_idx := view.proposer_id;
  var xs := PrimaryHas1bFromAllLiveAcceptorsOrIsPastPhase1TemporalSet(b, asp.live_quorum, view);
  var y := PrimaryInState2Temporal(b, view);
  var z := not(NoReplicaBeyondViewTemporal(b, view));
  var P := always(andset(xs));
  var Q := or(y, z);
  var Action := MakeRslActionTemporalFromSpontaneousReplicaFunction(b, LReplicaNextSpontaneousMaybeEnterPhase2, primary_idx);

  if sat(i, P) && !sat(i, Q) && sat(i, Action)
  {
    lemma_ConstantsAllConsistent(b, asp.c, i);
    lemma_ConstantsAllConsistent(b, asp.c, i+1);
    assert BalLeq(CurrentViewOfHost(b[i], primary_idx), view);
        
    assert SpecificSpontaneousRslActionOccurs(b[i], b[i+1], LReplicaNextSpontaneousMaybeEnterPhase2, primary_idx);
    var ios:seq<RslIo> :| && RslNextOneReplica(b[i], b[i+1], primary_idx, ios)
                          && SpontaneousIos(ios, 0)
                          && LReplicaNextSpontaneousMaybeEnterPhase2(b[i].replicas[primary_idx].replica,
                                                                    b[i+1].replicas[primary_idx].replica,
                                                                    ExtractSentPacketsFromIos(ios));

    var s := b[i].replicas[primary_idx].replica.proposer;
    var s' := b[i+1].replicas[primary_idx].replica.proposer;

    TemporalDeduceFromAlways(i, i, andset(xs));

    lemma_Received1bPacketsAreFromMaxBallotISent1a(b, asp.c, i, primary_idx);
    var mapper := (p:RslPacket) requires p.src in asp.c.config.replica_ids => GetReplicaIndex(p.src, asp.c.config);
    var sources := MapSetToSetOver(s.received_1b_packets, mapper);

    forall idx | idx in asp.live_quorum
      ensures idx in sources
    {
      assert sat(i, PrimaryHas1bFromAcceptorInViewTemporal(b, view, idx));
      var p :| PrimaryHasSpecific1bFromAcceptorInView(b[i], view, idx, p);
      assert ReplicasDistinct(asp.c.config.replica_ids, mapper(p), idx);
      assert mapper(p) == idx;
    }
    lemma_SubsetCardinality(sources, asp.live_quorum, x=>true);
    assert |s.received_1b_packets| >= LMinQuorumSize(s.constants.all.config);
    assert LSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a);
    assert s.current_state == 1;
    assert s' == s.(current_state := 2,
                    next_operation_number_to_propose := b[i].replicas[primary_idx].replica.acceptor.log_truncation_point);
    assert PrimaryInState2(b[i+1], view);
    assert sat(i+1, y);
    assert sat(i+1, Q);
  }
}

lemma lemma_PrimaryHas1bFromAllLiveAcceptorsLeadsToPrimaryEnteringPhase2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  start_step:int,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires asp.synchrony_start <= start_step
  requires view.proposer_id in asp.live_quorum
  ensures  var t := TimeToPerformGenericAction(asp);
           var f := PaxosTimeMap(b);
           var xs := PrimaryHas1bFromAllLiveAcceptorsOrIsPastPhase1TemporalSet(b, asp.live_quorum, view);
           sat(start_step, leadstowithin(always(andset(xs)),
                                         or(PrimaryInState2Temporal(b, view), not(NoReplicaBeyondViewTemporal(b, view))),
                                         t, f))
{
  var t := TimeToPerformGenericAction(asp);
  var f := PaxosTimeMap(b);
  var primary_idx := view.proposer_id;
  var xs := PrimaryHas1bFromAllLiveAcceptorsOrIsPastPhase1TemporalSet(b, asp.live_quorum, view);
  var y := PrimaryInState2Temporal(b, view);
  var z := not(NoReplicaBeyondViewTemporal(b, view));
  var P := always(andset(xs));
  var Q := or(y, z);
  var Action := MakeRslActionTemporalFromSpontaneousReplicaFunction(b, LReplicaNextSpontaneousMaybeEnterPhase2, primary_idx);

  forall i | start_step <= i
    ensures sat(i, TemporalWF1Req1(P, Q))
    ensures sat(i, TemporalWF1Req2(P, Q, Action))
  {
    if sat(i, P)
    {
      Lemma_AlwaysImpliesLaterAlways(i, i+1, andset(xs));
    }
    lemma_PrimaryHas1bFromAllLiveAcceptorsLeadsToPrimaryEnteringPhase2WF1Req2(b, asp, start_step, i, view);
  }
  TemporalAlways(start_step, TemporalWF1Req1(P, Q));
  TemporalAlways(start_step, TemporalWF1Req2(P, Q, Action));
  lemma_ReplicaNextPerformsSubactionPeriodically(b, asp, primary_idx, 2);
  lemma_EstablishRequirementsForWF1RealTime(b, asp, start_step, Action, t);
  TemporalWF1RealTime(start_step, P, Q, Action, t, f);
}

lemma lemma_StablePeriodStartedLeadsToPrimaryInPhase2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  start_step:int,
  processing_bound:int,
  view:Ballot,
  ahead_idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, start_step, processing_bound)
  requires view.proposer_id in asp.live_quorum
  ensures  var t := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp) * 2 + processing_bound * 2;
           var f := PaxosTimeMap(b);
           sat(start_step, leadstowithin(StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx),
                                         or(PrimaryInState2Temporal(b, view), not(NoReplicaBeyondViewTemporal(b, view))),
                                         t, f))
{
  var t1 := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp) + processing_bound * 2;
  var t2 := TimeToPerformGenericAction(asp);
  var t := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp) * 2 + processing_bound * 2;
  var f := PaxosTimeMap(b);
  var xs := PrimaryHas1bFromAllLiveAcceptorsOrIsPastPhase1TemporalSet(b, asp.live_quorum, view);
    
  assert t == t1 + t2;
  lemma_StablePeriodStartedLeadsToPrimaryGetting1bFromEveryLiveAcceptorForever(b, asp, start_step, processing_bound, view, ahead_idx);
  lemma_PrimaryHas1bFromAllLiveAcceptorsLeadsToPrimaryEnteringPhase2(b, asp, start_step, view);
  TransitivityOfLeadsToWithin(start_step,
                              StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx),
                              always(andset(xs)),
                              or(PrimaryInState2Temporal(b, view), not(NoReplicaBeyondViewTemporal(b, view))),
                              t1, t2, f);
}

lemma lemma_StablePeriodStartedLeadsToPrimaryEnteringPhase2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  start_step:int,
  processing_bound:int,
  view:Ballot,
  ahead_idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, start_step, processing_bound)
  requires view.proposer_id in asp.live_quorum
  ensures  var t := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp) * 2 + processing_bound * 2;
           var f := PaxosTimeMap(b);
           var y := PrimaryInState2Temporal(b, view);
           sat(start_step, always(imply(StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx),
                                        or(eventuallynextwithin(and(not(y), next(y)), t, f),
                                           eventuallywithin(not(NoReplicaBeyondViewTemporal(b, view)), t, f)))))
{
  var t := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp) * 2 + processing_bound * 2;
  var f := PaxosTimeMap(b);
  var x := StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx);
  var y := PrimaryInState2Temporal(b, view);
  var z := not(NoReplicaBeyondViewTemporal(b, view));
    
  lemma_StablePeriodStartedLeadsToPrimaryInPhase2(b, asp, start_step, processing_bound, view, ahead_idx);
  TemporalAlways(start_step, imply(x, not(y)));
  lemma_TimeMonotonicFromInvariantHolds(b, asp, start_step);
  Lemma_LeadsToWithinOrSomethingLeadsToTransitionOrSomething(start_step, x, y, z, t, f);
}

}
