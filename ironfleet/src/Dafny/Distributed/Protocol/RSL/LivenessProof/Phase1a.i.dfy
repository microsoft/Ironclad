include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "StablePeriod.i.dfy"
include "ViewAdvance.i.dfy"
include "MaxBallotISent1a.i.dfy"
include "MaxBallot.i.dfy"
include "WF1.i.dfy"
include "../CommonProof/MaxBallotISent1a.i.dfy"
include "../CommonProof/MaxBallot.i.dfy"
include "../CommonProof/Constants.i.dfy"
include "../../../Common/Framework/EnvironmentSynchronyLemmas.i.dfy"

module LivenessProof__Phase1a_i {

import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__MaxBallotISent1a_i
import opened LivenessProof__MaxBallot_i
import opened LivenessProof__PacketHandling_i
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
import opened Temporal__LeadsTo_i
import opened Temporal__Rules_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Temporal__Time_i
import opened Temporal__WF1_i
import opened Environment_s
import opened Collections__Maps2_s

predicate PrimaryInView(
  ps:RslState,
  view:Ballot
  )
{
  && 0 <= view.proposer_id < |ps.replicas|
  && CurrentViewOfHost(ps, view.proposer_id) == view
}

function{:opaque} PrimaryInViewTemporal(
  b:Behavior<RslState>,
  view:Ballot
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, PrimaryInViewTemporal(b, view))} ::
             sat(i, PrimaryInViewTemporal(b, view)) == PrimaryInView(b[i], view)
{
  stepmap(imap i :: PrimaryInView(b[i], view))
}

predicate PrimaryMaxBallotISent1aInView(
  ps:RslState,
  view:Ballot
  )
{
  && 0 <= view.proposer_id < |ps.replicas|
  && ps.replicas[view.proposer_id].replica.proposer.max_ballot_i_sent_1a == view
}

function{:opaque} PrimaryMaxBallotISent1aInViewTemporal(
  b:Behavior<RslState>,
  view:Ballot
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, PrimaryMaxBallotISent1aInViewTemporal(b, view))} ::
             sat(i, PrimaryMaxBallotISent1aInViewTemporal(b, view)) == PrimaryMaxBallotISent1aInView(b[i], view)
{
  stepmap(imap i :: PrimaryMaxBallotISent1aInView(b[i], view))
}

predicate PrimarySent1aInView(
  ps:RslState,
  ps':RslState,
  view:Ballot
  )
{
  exists ios :: && 0 <= view.proposer_id < |ps.replicas|
          && 0 <= view.proposer_id < |ps'.replicas|
          && var idx := view.proposer_id;
            var s := ps.replicas[idx].replica.proposer;
            var s' := ps'.replicas[idx].replica.proposer;
            && RslNextOneReplica(ps, ps', view.proposer_id, ios)
            && LProposerMaybeEnterNewViewAndSend1a(s, s', ExtractSentPacketsFromIos(ios))
            && s.election_state.current_view.proposer_id == s.constants.my_index
            && BalLt(s.max_ballot_i_sent_1a, s.election_state.current_view)
            && s.election_state.current_view == view
}

function{:opaque} PrimarySent1aInViewTemporal(
  b:Behavior<RslState>,
  view:Ballot
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, PrimarySent1aInViewTemporal(b, view))} ::
             sat(i, PrimarySent1aInViewTemporal(b, view)) == PrimarySent1aInView(b[i], b[nextstep(i)], view)
{
  stepmap(imap i :: PrimarySent1aInView(b[i], b[nextstep(i)], view))
}

lemma lemma_StablePeriodStartedLeadsToPrimaryInView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  start_step:int,
  processing_bound:int,
  view:Ballot,
  ahead_idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, start_step, processing_bound)
  ensures  sat(start_step, leadstowithin(StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx),
                                         or(PrimaryInViewTemporal(b, view), not(NoReplicaBeyondViewTemporal(b, view))),
                                         TimeForOneReplicaToAdvanceAnother(asp, processing_bound),
                                         PaxosTimeMap(b)))
{
  var x := StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx);
  var y := or(PrimaryInViewTemporal(b, view), not(NoReplicaBeyondViewTemporal(b, view)));
  var t := TimeForOneReplicaToAdvanceAnother(asp, processing_bound);
  var timefun := PaxosTimeMap(b);
  var primary_idx := view.proposer_id;
  forall i | start_step <= i
    ensures sat(i, imply(x, eventuallywithin(y, t, timefun)))
  {
    if sat(i, x)
    {
      lemma_IfPacketProcessingSynchronousThenAlways(b, asp, start_step, i, processing_bound);
      var j := lemma_OneLiveReplicaSoonAdvancesAnother(b, asp, i, processing_bound, i, ahead_idx, primary_idx);
      assert timefun[j] <= timefun[i] + t;
      assert BalLeq(view, CurrentViewOfHost(b[j], primary_idx));
      if CurrentViewOfHost(b[j], primary_idx) == view
      {
        assert sat(j, PrimaryInViewTemporal(b, view));
      }
      else
      {
        assert !BalLeq(CurrentViewOfHost(b[j], primary_idx), view);
        assert sat(j, not(NoReplicaBeyondViewTemporal(b, view)));
      }
      assert sat(j, y);
      assert sat(j, beforeabsolutetime(y, timefun[i] + t, timefun));
      TemporalEventually(i, j, beforeabsolutetime(y, timefun[i] + t, timefun));
    }
  }
  TemporalAlways(start_step, imply(x, eventuallywithin(y, t, timefun)));
}

lemma lemma_StablePeriodStartedLeadsToPrimaryInViewAlt(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  start_step:int,
  processing_bound:int,
  view:Ballot,
  ahead_idx:int
  ) returns (
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, start_step, processing_bound)
  requires sat(start_step, StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx))
  ensures  start_step <= step
  ensures  sat(step, or(PrimaryInViewTemporal(b, view), not(NoReplicaBeyondViewTemporal(b, view))))
  ensures  b[step].environment.time <= b[start_step].environment.time + TimeForOneReplicaToAdvanceAnother(asp, processing_bound)
{
  var primary_idx := view.proposer_id;
  step := lemma_OneLiveReplicaSoonAdvancesAnother(b, asp, start_step, processing_bound, start_step, ahead_idx, primary_idx);

  assert BalLeq(view, CurrentViewOfHost(b[step], primary_idx));
  if CurrentViewOfHost(b[step], primary_idx) == view
  {
    assert sat(step, PrimaryInViewTemporal(b, view));
  }
  else
  {
    assert !BalLeq(CurrentViewOfHost(b[step], primary_idx), view);
    assert sat(step, not(NoReplicaBeyondViewTemporal(b, view)));
  }
}

lemma lemma_PrimaryInViewLeadsToPrimaryMaxBallotISent1aInViewWF1Req1(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  start_step:int,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= start_step
  ensures  var P := PrimaryInViewTemporal(b, view);
           var Q := or(PrimaryMaxBallotISent1aInViewTemporal(b, view), not(NoReplicaBeyondViewTemporal(b, view)));
           sat(start_step, always(TemporalWF1Req1(P, Q)))
{
  var primary_idx := view.proposer_id;
  var P := PrimaryInViewTemporal(b, view);
  var Q := or(PrimaryMaxBallotISent1aInViewTemporal(b, view), not(NoReplicaBeyondViewTemporal(b, view)));

  forall i | start_step <= i
    ensures sat(i, TemporalWF1Req1(P, Q))
  {
    if sat(i, P) && !sat(i, Q) && !sat(i+1, P) && !sat(i+1, Q)
    {
      lemma_ConstantsAllConsistent(b, asp.c, i);
      lemma_ConstantsAllConsistent(b, asp.c, i+1);
      assert BalLeq(CurrentViewOfHost(b[i+1], primary_idx), view);
      lemma_ViewOfHostMonotonic(b, asp, primary_idx, i, i+1);
      assert !NoReplicaBeyondView(b[i+1], view);
    }
  }

  TemporalAlways(start_step, TemporalWF1Req1(P, Q));
}

lemma lemma_PrimaryInViewLeadsToPrimaryMaxBallotISent1aInViewWF1Req2(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  start_step:int,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= start_step
  ensures  var P := PrimaryInViewTemporal(b, view);
           var Q := or(PrimaryMaxBallotISent1aInViewTemporal(b, view), not(NoReplicaBeyondViewTemporal(b, view)));
           var Action := MakeRslActionTemporalFromSpontaneousReplicaFunction(b, LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a, view.proposer_id);
           sat(start_step, always(TemporalWF1Req2(P, Q, Action)))
{
  var primary_idx := view.proposer_id;
  var P := PrimaryInViewTemporal(b, view);
  var Q := or(PrimaryMaxBallotISent1aInViewTemporal(b, view), not(NoReplicaBeyondViewTemporal(b, view)));
  var Action := MakeRslActionTemporalFromSpontaneousReplicaFunction(b, LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a, primary_idx);

  forall i | start_step <= i
    ensures sat(i, TemporalWF1Req2(P, Q, Action))
  {
    if sat(i, P) && sat(i, Action) && !sat(i, Q) && !sat(i+1, Q)
    {
      lemma_ConstantsAllConsistent(b, asp.c, i);
      lemma_ConstantsAllConsistent(b, asp.c, i+1);
      assert SpecificSpontaneousRslActionOccurs(b[i], b[i+1], LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a, primary_idx);
      var ios :| && RslNextOneReplica(b[i], b[i+1], primary_idx, ios)
                 && SpontaneousIos(ios, 0)
                 && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(b[i].replicas[primary_idx].replica,
                                                                     b[i+1].replicas[primary_idx].replica,
                                                                     ExtractSentPacketsFromIos(ios));
      lemma_NoReplicaBeyondViewImpliesNoMaxBallotISent1aBeyondView(b, asp, i, view);
      assert BalLeq(b[i].replicas[primary_idx].replica.proposer.max_ballot_i_sent_1a, view);
      assert false;
    }
  }

  TemporalAlways(start_step, TemporalWF1Req2(P, Q, Action));
}

lemma lemma_PrimaryInViewLeadsToPrimaryMaxBallotISent1aInView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  start_step:int,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires asp.synchrony_start <= start_step
  requires view.proposer_id in asp.live_quorum
  ensures  sat(start_step, leadstowithin(PrimaryInViewTemporal(b, view),
                                         or(PrimaryMaxBallotISent1aInViewTemporal(b, view), not(NoReplicaBeyondViewTemporal(b, view))),
                                         TimeToPerformGenericAction(asp),
                                         PaxosTimeMap(b)))
{
  var timefun := PaxosTimeMap(b);
  var primary_idx := view.proposer_id;
  var P := PrimaryInViewTemporal(b, view);
  var Q := or(PrimaryMaxBallotISent1aInViewTemporal(b, view), not(NoReplicaBeyondViewTemporal(b, view)));
  var Action := MakeRslActionTemporalFromSpontaneousReplicaFunction(b, LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a, primary_idx);
  var t := TimeToPerformGenericAction(asp);

  lemma_PrimaryInViewLeadsToPrimaryMaxBallotISent1aInViewWF1Req1(b, asp, start_step, view);
  lemma_PrimaryInViewLeadsToPrimaryMaxBallotISent1aInViewWF1Req2(b, asp, start_step, view);
  lemma_ReplicaNextPerformsSubactionPeriodically(b, asp, primary_idx, 1);
  lemma_EstablishRequirementsForWF1RealTime(b, asp, start_step, Action, t);
  TemporalWF1RealTime(start_step, P, Q, Action, t, timefun);
}

lemma lemma_StablePeriodStartedLeadsToPrimaryMaxBallotISent1aInView(
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
  ensures  sat(start_step, leadstowithin(StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx),
                                         or(PrimaryMaxBallotISent1aInViewTemporal(b, view), not(NoReplicaBeyondViewTemporal(b, view))),
                                         TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp),
                                         PaxosTimeMap(b)))
{
  var w := StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx);
  var x := PrimaryInViewTemporal(b, view);
  var y := PrimaryMaxBallotISent1aInViewTemporal(b, view);
  var z := not(NoReplicaBeyondViewTemporal(b, view));
  var t1 := TimeForOneReplicaToAdvanceAnother(asp, processing_bound);
  var t2 := TimeToPerformGenericAction(asp);
    
  lemma_StablePeriodStartedLeadsToPrimaryInView(b, asp, start_step, processing_bound, view, ahead_idx);
  lemma_PrimaryInViewLeadsToPrimaryMaxBallotISent1aInView(b, asp, start_step, view);
  Lemma_LeadsToTwoPossibilitiesWithin(start_step, w, x, y, z, t1, t2, PaxosTimeMap(b));

  assert sat(start_step, leadstowithin(w, or(y, z), t1 + t2, PaxosTimeMap(b)));
}

lemma lemma_IfPrimaryTransitionsToMaxBallotISent1aInViewThenPrimarySent1a(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires !sat(i, PrimaryMaxBallotISent1aInViewTemporal(b, view))
  requires sat(i+1, PrimaryMaxBallotISent1aInViewTemporal(b, view))
  ensures  sat(i, PrimarySent1aInViewTemporal(b, view))
{
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i+1);
  var idx := view.proposer_id;
  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, idx);
  assert PrimarySent1aInView(b[i], b[i+1], view);
}

lemma lemma_StablePeriodStartedLeadsToPrimarySending1a(
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
  ensures  var t := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp);
           var f := PaxosTimeMap(b);
           sat(start_step, always(imply(StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx),
                                        or(eventuallynextwithin(PrimarySent1aInViewTemporal(b, view), t, f),
                                           eventuallywithin(not(NoReplicaBeyondViewTemporal(b, view)), t, f)))))
{
  var t := TimeForOneReplicaToAdvanceAnother(asp, processing_bound) + TimeToPerformGenericAction(asp);
  var f := PaxosTimeMap(b);
  var x := StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx);
  var y := PrimaryMaxBallotISent1aInViewTemporal(b, view);
  var z := not(NoReplicaBeyondViewTemporal(b, view));
  var w := PrimarySent1aInViewTemporal(b, view);
  lemma_StablePeriodStartedLeadsToPrimaryMaxBallotISent1aInView(b, asp, start_step, processing_bound, view, ahead_idx);
  lemma_TimeMonotonicFromInvariantHolds(b, asp, start_step);

  TemporalAlways(start_step, imply(x, not(y)));
  Lemma_LeadsToWithinOrSomethingLeadsToTransitionOrSomething(start_step, x, y, z, t, f);

  forall j | start_step <= j
    ensures sat(j, imply(x, or(eventuallynextwithin(w, t, f), eventuallywithin(z, t, f))))
  {
    TemporalDeduceFromAlways(start_step, j, imply(x, or(eventuallynextwithin(and(not(y), next(y)), t, f), eventuallywithin(z, t, f))));
    if sat(j, x) && !sat(j, eventuallywithin(z, t, f))
    {
      assert sat(j, eventuallynextwithin(and(not(y), next(y)), t, f));
      var k := TemporalDeduceFromEventual(j, nextbefore(and(not(y), next(y)), f[j] + t, f));
      lemma_IfPrimaryTransitionsToMaxBallotISent1aInViewThenPrimarySent1a(b, asp, k, view);
      TemporalEventually(j, k, nextbefore(w, f[j] + t, f));
    }
  }
    
  TemporalAlways(start_step, imply(x, or(eventuallynextwithin(w, t, f), eventuallywithin(z, t, f))));
}

}
