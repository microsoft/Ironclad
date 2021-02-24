include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "EpochLength.i.dfy"
include "ViewChange.i.dfy"
include "ViewPropagation.i.dfy"
include "ViewPropagation2.i.dfy"
include "ViewSuspicion.i.dfy"
include "MaxBallotISent1a.i.dfy"
include "StablePeriod.i.dfy"
include "../CommonProof/CanonicalizeBallot.i.dfy"
include "../CommonProof/MaxBallotISent1a.i.dfy"
include "../CommonProof/Actions.i.dfy"
include "../../../Common/Framework/EnvironmentSynchronyLemmas.i.dfy"
include "../../../../Libraries/Math/mul.i.dfy"

module LivenessProof__ViewPersistence_i {

import opened LiveRSL__Configuration_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Election_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Environment_i
import opened LivenessProof__EpochLength_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__PacketHandling_i
import opened LivenessProof__RealTime_i
import opened LivenessProof__ViewChange_i
import opened LivenessProof__ViewPropagation_i
import opened LivenessProof__ViewPropagation2_i
import opened LivenessProof__ViewSuspicion_i
import opened LivenessProof__MaxBallotISent1a_i
import opened LivenessProof__RequestsReceived_i
import opened LivenessProof__StablePeriod_i
import opened CommonProof__Actions_i
import opened CommonProof__CanonicalizeBallot_i
import opened CommonProof__Constants_i
import opened CommonProof__MaxBallotISent1a_i
import opened CommonProof__Quorum_i
import opened Common__UpperBound_s
import opened Liveness__EnvironmentSynchronyLemmas_i
import opened Math__mul_i
import opened Temporal__Induction_i
import opened Temporal__Rules_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Temporal__Time_i
import opened Collections__Maps2_s
import opened Collections__Sets_i
import opened Environment_s
import opened EnvironmentSynchrony_s

predicate NoLiveReplicaSuspectsViewBefore(
  ps:RslState,
  live_quorum:set<int>,
  view:Ballot,
  endTime:int,
  max_clock_ambiguity:int
  )
{
  ps.environment.time < endTime - max_clock_ambiguity ==>
    forall idx :: idx in live_quorum ==>
      && 0 <= idx < |ps.replicas|
      && var es := ps.replicas[idx].replica.proposer.election_state;
        (|| BalLt(es.current_view, view)
         || (&& es.current_view == view
            && es.constants.my_index !in es.current_view_suspectors
            && es.epoch_end_time >= endTime))
}

function{:opaque} NoLiveReplicaSuspectsViewBeforeTemporal(
  b:Behavior<RslState>,
  live_quorum:set<int>,
  view:Ballot,
  endTime:int,
  max_clock_ambiguity:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, NoLiveReplicaSuspectsViewBeforeTemporal(b, live_quorum, view, endTime, max_clock_ambiguity))} ::
             sat(i, NoLiveReplicaSuspectsViewBeforeTemporal(b, live_quorum, view, endTime, max_clock_ambiguity)) <==>
             NoLiveReplicaSuspectsViewBefore(b[i], live_quorum, view, endTime, max_clock_ambiguity)
{
  stepmap(imap i :: NoLiveReplicaSuspectsViewBefore(b[i], live_quorum, view, endTime, max_clock_ambiguity))
}

lemma {:timeLimitMultiplier 2} lemma_NoLiveReplicaSuspectsViewBeforeStableOneStep(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  view:Ballot,
  minEpochLength:int,
  endTime:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires IsValidBallot(view, asp.c)
  requires minEpochLength >= 0
  requires b[i].environment.time >= endTime - minEpochLength - asp.max_clock_ambiguity
  requires NoLiveReplicaSuspectsViewBefore(b[i], asp.live_quorum, view, endTime, asp.max_clock_ambiguity)
  requires forall idx :: idx in asp.live_quorum ==> EpochLengthEqualOrGreater(b[i], idx, minEpochLength + asp.max_clock_ambiguity * 2)
  ensures  NoLiveReplicaSuspectsViewBefore(b[i+1], asp.live_quorum, view, endTime, asp.max_clock_ambiguity)
{
  lemma_AssumptionsMakeValidTransition(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i+1);

  var ps := b[i];
  var ps' := b[i+1];

  if !NoLiveReplicaSuspectsViewBefore(b[i+1], asp.live_quorum, view, endTime, asp.max_clock_ambiguity)
  {
    lemma_NoOneCanExceedViewUntilAQuorumMemberSuspectsIt(b, asp, i, view);
    assert AllQuorumMembersViewPlusLe(ps, asp.live_quorum, ViewPlus(view, false));
    assert AllReplicasViewPlusLe(ps, ViewPlus(view, true));
    
    assert ps.environment.time < endTime - asp.max_clock_ambiguity;
    forall idx | idx in asp.live_quorum
      ensures var es' := ps'.replicas[idx].replica.proposer.election_state;
              || BalLt(es'.current_view, view)
              || (&& es'.current_view == view
                 && es'.constants.my_index !in es'.current_view_suspectors
                 && es'.epoch_end_time >= endTime)
    {
      var s := ps.replicas[idx].replica;
      var s' := ps'.replicas[idx].replica;
      var es := s.proposer.election_state;
      var es' := s'.proposer.election_state;

      if es' != es && !BalLt(es'.current_view, view)
      {
        lemma_ViewOfHostMonotonic(b, asp, idx, i, i+1);
        lemma_IsValidBallot(b, asp, i, idx);
        lemma_IsValidBallot(b, asp, i+1, idx);
        lemma_ViewInfoStateInvHolds(b, asp, i);
        assert EpochLengthEqualOrGreater(ps, idx, minEpochLength);
        lemma_OverflowProtectionNotUsedForReplica(b, asp, i, idx);
            
        var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, idx);
        var sent_packets := ExtractSentPacketsFromIos(ios);
        if |ios| > 1 && ios[1].LIoOpReadClock? && LReplicaNextProcessHeartbeat(s, s', ios[0].r, ios[1].t, sent_packets) && ios[0].r.src in asp.c.config.replica_ids
        {
          var p := ios[0].r;
          var oid := p.src;
          var sender_index := GetReplicaIndex(oid, es.constants.all.config);
          lemma_PacketProcessedImpliesPacketSent(ps, ps', idx, ios, p);
          lemma_ClockAmbiguityLimitApplies(b, asp, i, idx, ios[1]);
          assert p in ps.environment.sentPackets;
          assert ViewInfoConsistent(ps, sender_index);
          assert ViewInfoInPacketConsistent(ps, sender_index, p);
          assert ViewPlusLe(CurrentViewPlusOfHost(ps, sender_index), ViewPlus(view, true));
          assert es'.current_view == view;
          assert es'.constants.my_index !in es'.current_view_suspectors;
          assert es'.epoch_end_time >= endTime;
        }
        else if LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, s', SpontaneousClock(ios), sent_packets)
        {
          assert es'.current_view == ComputeSuccessorView(es.current_view, asp.c);
          lemma_NothingBetweenViewAndSuccessor(es.current_view, view, asp.c);
          if es.current_view == view
          {
            assert |es.current_view_suspectors| >= LMinQuorumSize(es.constants.all.config);
            lemma_AllSuspectorsValidStateInvHolds(b, asp, i);
            var live_suspector_idx := lemma_QuorumIndexOverlap(es.current_view_suspectors, asp.live_quorum, |asp.c.config.replica_ids|);
            assert 0 <= live_suspector_idx < |ps.replicas|;
            assert ViewInfoConsistent(ps, live_suspector_idx);
            assert ViewInfoInObserverConsistent(ps, live_suspector_idx, idx);
            lemma_ViewPlusLeTransitiveDefinite(ViewPlus(view, true), CurrentViewPlusOfHost(ps, live_suspector_idx), ViewPlus(view, false));
            assert false;
          }
          lemma_ClockAmbiguityLimitApplies(b, asp, i, idx, ios[0]);
        }
        else if SpontaneousIos(ios, 1)
        {
          lemma_ClockAmbiguityLimitApplies(b, asp, i, idx, ios[0]);
          assert es'.current_view == view;
          assert es'.constants.my_index !in es'.current_view_suspectors;
          assert es'.epoch_end_time >= endTime;
        }
      }
    }
  }
}

lemma lemma_NoLiveReplicaSuspectsViewBeforeStable(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  view:Ballot,
  minEpochLength:int,
  endTime:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires IsValidBallot(view, asp.c)
  requires minEpochLength >= 0
  requires b[i].environment.time >= endTime - minEpochLength - asp.max_clock_ambiguity
  requires NoLiveReplicaSuspectsViewBefore(b[i], asp.live_quorum, view, endTime, asp.max_clock_ambiguity)
  requires forall idx :: idx in asp.live_quorum ==> sat(i, always(EpochLengthEqualOrGreaterTemporal(b, idx, minEpochLength + asp.max_clock_ambiguity * 2)))
  ensures  sat(i, always(NoLiveReplicaSuspectsViewBeforeTemporal(b, asp.live_quorum, view, endTime, asp.max_clock_ambiguity)))
{
  var x := NoLiveReplicaSuspectsViewBeforeTemporal(b, asp.live_quorum, view, endTime, asp.max_clock_ambiguity);
    
  forall j | i <= j
    ensures sat(j, imply(x, next(x)))
  {
    if sat(j, x)
    {
      forall idx | idx in asp.live_quorum
        ensures EpochLengthEqualOrGreater(b[j], idx, minEpochLength + asp.max_clock_ambiguity * 2)
      {
        TemporalDeduceFromAlways(i, j, EpochLengthEqualOrGreaterTemporal(b, idx, minEpochLength + asp.max_clock_ambiguity * 2));
      }
      lemma_TimeAdvancesBetween(b, asp, i, j);
      lemma_NoLiveReplicaSuspectsViewBeforeStableOneStep(b, asp, j, view, minEpochLength, endTime);
    }
    reveal imply();
    reveal next();
  }

  TemporalInductionNext(i, x);
}

lemma lemma_LaterViewWithPrimaryExists(
  ps:RslState,
  primary_idx:int,
  max_integer_val:UpperBound
  ) returns (
  view:Ballot
  )
  requires ConstantsAllConsistentInv(ps)
  requires 0 <= primary_idx < |ps.replicas|
  requires forall idx :: 0 <= idx < |ps.replicas| ==> LtUpperBound(CurrentViewOfHost(ps, idx).seqno, max_integer_val)
  ensures  view.proposer_id == primary_idx
  ensures  LeqUpperBound(view.seqno, max_integer_val)
  ensures  forall idx :: 0 <= idx < |ps.replicas| ==> BalLt(CurrentViewOfHost(ps, idx), view)
{
  var ballot_seqnos := set idx | 0 <= idx < |ps.constants.config.replica_ids| :: CurrentViewOfHost(ps, idx).seqno;
  assert CurrentViewOfHost(ps, primary_idx).seqno in ballot_seqnos;
  var highest_seqno := intsetmax(ballot_seqnos);
  var highest_idx :| 0 <= highest_idx < |ps.constants.config.replica_ids| && CurrentViewOfHost(ps, highest_idx).seqno == highest_seqno;
  assert LtUpperBound(highest_seqno, max_integer_val);

  var next_seqno := highest_seqno + 1;
  view := Ballot(next_seqno, primary_idx);
  assert IsValidBallot(view, ps.constants);
  forall idx | 0 <= idx < |ps.constants.config.replica_ids|
    ensures BalLt(CurrentViewOfHost(ps, idx), view)
  {
    assert CurrentViewOfHost(ps, idx).seqno in ballot_seqnos;
  }
}

predicate SomeReplicaInLiveQuorumReachedView(
  ps:RslState,
  live_quorum:set<int>,
  view:Ballot
  )
{
  exists idx :: idx in live_quorum && 0 <= idx < |ps.replicas| && BalLeq(view, CurrentViewOfHost(ps, idx))
}

function{:opaque} SomeReplicaInLiveQuorumReachedViewTemporal(
  b:Behavior<RslState>,
  live_quorum:set<int>,
  view:Ballot
  ):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, SomeReplicaInLiveQuorumReachedViewTemporal(b, live_quorum, view))} ::
             sat(i, SomeReplicaInLiveQuorumReachedViewTemporal(b, live_quorum, view)) <==>
             SomeReplicaInLiveQuorumReachedView(b[i], live_quorum, view)
{
  stepmap(imap i :: SomeReplicaInLiveQuorumReachedView(b[i], live_quorum, view))
}

lemma lemma_FirstStepWithLiveReplicaInQuorumHasNoLiveReplicaSuspectingBeforeIfHeartbeat(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  view:Ballot,
  duration:int,
  step:int,
  ios:seq<RslIo>,
  ahead_idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires duration > 0
  requires 1 <= step
  requires view.proposer_id in asp.live_quorum
  requires forall idx :: idx in asp.live_quorum ==> sat(step-1, EpochLengthEqualOrGreaterTemporal(b, idx, duration + asp.max_clock_ambiguity * 2))
  requires ahead_idx in asp.live_quorum
  requires 0 <= ahead_idx < |b[step].replicas|
  requires BalLeq(view, CurrentViewOfHost(b[step], ahead_idx))
  requires !SomeReplicaInLiveQuorumReachedView(b[step-1], asp.live_quorum, view)
  requires |ios| > 1
  requires ios[0].LIoOpReceive?
  requires ios[0].r.msg.RslMessage_Heartbeat?
  requires ios[1].LIoOpReadClock?
  requires RslNextOneReplica(b[step-1], b[step], ahead_idx, ios)
  requires LReplicaNextProcessHeartbeat(b[step-1].replicas[ahead_idx].replica, b[step].replicas[ahead_idx].replica,
                                        ios[0].r, ios[1].t, ExtractSentPacketsFromIos(ios))
  ensures  var es' := b[step].replicas[ahead_idx].replica.proposer.election_state;
           && es'.current_view == view
           && es'.constants.my_index !in es'.current_view_suspectors
           && es'.epoch_end_time >= b[step].environment.time + duration + asp.max_clock_ambiguity
{
  var ps := b[step-1];
  var ps' := b[step];
  var s := ps.replicas[ahead_idx].replica;
  var s' := ps'.replicas[ahead_idx].replica;
  var es := s.proposer.election_state;
  var es' := s'.proposer.election_state;

  lemma_ViewOfHostMonotonic(b, asp, ahead_idx, step-1, step);
  lemma_IsValidBallot(b, asp, step-1, ahead_idx);
  lemma_IsValidBallot(b, asp, step, ahead_idx);
  lemma_OverflowProtectionNotUsedForReplica(b, asp, step-1, ahead_idx);
  lemma_OverflowProtectionNotUsedForReplica(b, asp, step, ahead_idx);
  assert EpochLengthEqualOrGreater(ps, ahead_idx, duration);

  lemma_ConstantsAllConsistent(b, asp.c, step-1);
  lemma_ConstantsAllConsistent(b, asp.c, step);
  lemma_AssumptionsMakeValidTransition(b, asp.c, step-1);

  var p := ios[0].r;
  var oid := p.src;
  var sender_index := GetReplicaIndex(oid, es.constants.all.config);
  lemma_PacketProcessedImpliesPacketSent(ps, ps', ahead_idx, ios, p);
  assert p in ps.environment.sentPackets;
  lemma_ViewInfoStateInvHolds(b, asp, step-1);
  assert ViewInfoConsistent(ps, sender_index);
  assert ViewInfoInPacketConsistent(ps, sender_index, p);
  assert ViewPlusLe(ViewPlus(p.msg.bal_heartbeat, p.msg.suspicious), CurrentViewPlusOfHost(ps, sender_index));

  lemma_NoOneCanExceedViewUntilAQuorumMemberSuspectsIt(b, asp, step-1, view);
  assert AllQuorumMembersViewPlusLe(ps, asp.live_quorum, ViewPlus(view, false));
  assert AllReplicasViewPlusLe(ps, ViewPlus(view, true));
  assert ViewPlusLe(CurrentViewPlusOfHost(ps, sender_index), ViewPlus(view, true));
  lemma_BalLtProperties();
  lemma_ViewPlusLeTransitiveDefinite(ViewPlus(p.msg.bal_heartbeat, p.msg.suspicious), CurrentViewPlusOfHost(ps, sender_index), ViewPlus(view, true));
  assert BalLeq(p.msg.bal_heartbeat, view);
  lemma_ClockAmbiguityLimitApplies(b, asp, step-1, ahead_idx, ios[1]);
}

lemma{:timeLimitMultiplier 2} lemma_FirstStepWithLiveReplicaInQuorumHasNoLiveReplicaSuspectingBefore(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  view:Ballot,
  duration:int,
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires duration > 0
  requires 1 <= step
  requires view.proposer_id in asp.live_quorum
  requires forall idx :: idx in asp.live_quorum ==> sat(step-1, EpochLengthEqualOrGreaterTemporal(b, idx, duration + asp.max_clock_ambiguity * 2))
  requires !SomeReplicaInLiveQuorumReachedView(b[step-1], asp.live_quorum, view)
  requires SomeReplicaInLiveQuorumReachedView(b[step], asp.live_quorum, view)
  ensures  NoLiveReplicaSuspectsViewBefore(b[step], asp.live_quorum, view, b[step].environment.time + duration + asp.max_clock_ambiguity, asp.max_clock_ambiguity)
{
  var ps := b[step-1];
  var ps' := b[step];
  var ahead_idx :| ahead_idx in asp.live_quorum && 0 <= ahead_idx < |ps'.replicas| && BalLeq(view, CurrentViewOfHost(ps', ahead_idx));
  lemma_ConstantsAllConsistent(b, asp.c, step-1);
  lemma_ConstantsAllConsistent(b, asp.c, step);
  lemma_AssumptionsMakeValidTransition(b, asp.c, step-1);
  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, step-1, ahead_idx);

  forall idx | idx in asp.live_quorum
    ensures var es' := ps'.replicas[idx].replica.proposer.election_state;
            || BalLt(es'.current_view, view)
            || (&& es'.current_view == view
               && es'.constants.my_index !in es'.current_view_suspectors
               && es'.epoch_end_time >= ps'.environment.time + duration + asp.max_clock_ambiguity)
  {
    var s := ps.replicas[idx].replica;
    var s' := ps'.replicas[idx].replica;
    var es := s.proposer.election_state;
    var es' := s'.proposer.election_state;

    lemma_ViewOfHostMonotonic(b, asp, idx, step-1, step);

    if idx != ahead_idx
    {
      assert BalLt(es'.current_view, view);
    }
    else
    {
      lemma_IsValidBallot(b, asp, step-1, idx);
      lemma_IsValidBallot(b, asp, step, idx);
      lemma_OverflowProtectionNotUsedForReplica(b, asp, step-1, idx);
      lemma_OverflowProtectionNotUsedForReplica(b, asp, step, idx);
      assert EpochLengthEqualOrGreater(ps, idx, duration);
        
      var ios2 := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, step-1, idx);
      var sent_packets := ExtractSentPacketsFromIos(ios2);
      if |ios2| > 1 && ios2[1].LIoOpReadClock? && LReplicaNextProcessHeartbeat(s, s', ios2[0].r, ios2[1].t, sent_packets) && ios2[0].r.src in asp.c.config.replica_ids
      {
        lemma_FirstStepWithLiveReplicaInQuorumHasNoLiveReplicaSuspectingBeforeIfHeartbeat(b, asp, view, duration, step, ios2, ahead_idx);
        lemma_ClockAmbiguityLimitApplies(b, asp, step-1, idx, ios2[1]);
      }
      else if LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, s', SpontaneousClock(ios2), sent_packets)
      {
        assert es'.current_view == ComputeSuccessorView(es.current_view, asp.c);
        lemma_NothingBetweenViewAndSuccessor(es.current_view, view, asp.c);
        lemma_ClockAmbiguityLimitApplies(b, asp, step-1, idx, ios2[0]);
      }
    }
  }
}

lemma lemma_FirstStepWithLiveReplicaInQuorumHasAllMaxBallot1aBeforeView(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  view:Ballot,
  duration:int,
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires duration > 0
  requires 1 <= step
  requires view.proposer_id in asp.live_quorum
  requires !SomeReplicaInLiveQuorumReachedView(b[step-1], asp.live_quorum, view)
  requires SomeReplicaInLiveQuorumReachedView(b[step], asp.live_quorum, view)
  ensures  forall idx :: 0 <= idx < |b[step].replicas| ==> BalLt(b[step].replicas[idx].replica.proposer.max_ballot_i_sent_1a, view)
{
  var ps := b[step-1];
  var ps' := b[step];
  var ahead_idx :| ahead_idx in asp.live_quorum && 0 <= ahead_idx < |ps'.replicas| && BalLeq(view, CurrentViewOfHost(ps', ahead_idx));
  lemma_ConstantsAllConsistent(b, asp.c, step-1);
  lemma_ConstantsAllConsistent(b, asp.c, step);
  lemma_AssumptionsMakeValidTransition(b, asp.c, step-1);
  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, step-1, ahead_idx);

  forall idx | 0 <= idx < |b[step].replicas|
    ensures BalLt(b[step].replicas[idx].replica.proposer.max_ballot_i_sent_1a, view)
  {
    var s := b[step-1].replicas[idx].replica.proposer;
    var s' := b[step].replicas[idx].replica.proposer;
        
    lemma_BalLtProperties();
    lemma_MaxBallotISent1aLeqView(b, asp, step-1, idx);
    assert BalLeq(s.max_ballot_i_sent_1a, s.election_state.current_view);

    if idx == ahead_idx || idx in asp.live_quorum
    {
      assert BalLt(s.election_state.current_view, view);
      assert BalLt(s.max_ballot_i_sent_1a, view);
      assert s'.max_ballot_i_sent_1a == s.max_ballot_i_sent_1a;
    }
    else
    {
      lemma_NoOneCanExceedViewUntilAQuorumMemberSuspectsIt(b, asp, step-1, view);
      assert AllQuorumMembersViewPlusLe(b[step-1], asp.live_quorum, ViewPlus(view, false));
      assert AllReplicasViewPlusLe(b[step-1], ViewPlus(view, true));
      assert ViewPlusLe(CurrentViewPlusOfHost(b[step-1], idx), ViewPlus(view, true));
      assert BalLeq(s.election_state.current_view, view);
      lemma_MaxBallotISent1aHasMeAsProposer(b, asp.c, step-1, idx);
      assert s.max_ballot_i_sent_1a.proposer_id != view.proposer_id;
      assert BalLt(s.max_ballot_i_sent_1a, view);
    }
  }
}

lemma lemma_EventuallyViewStable(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  primary_idx:int,
  duration:int
  ) returns (
  view:Ballot,
  step:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires primary_idx in asp.live_quorum
  requires duration > 0
  ensures  processing_sync_start <= step
  ensures  view.proposer_id == primary_idx
  ensures  LeqUpperBound(view.seqno, asp.c.params.max_integer_val)
  ensures  SomeReplicaInLiveQuorumReachedView(b[step], asp.live_quorum, view)
  ensures  forall idx :: 0 <= idx < |b[step].replicas| ==> BalLt(b[step].replicas[idx].replica.proposer.max_ballot_i_sent_1a, view)
  ensures  sat(step, always(NoLiveReplicaSuspectsViewBeforeTemporal(b, asp.live_quorum, view, b[step].environment.time + duration + asp.max_clock_ambiguity, asp.max_clock_ambiguity)))
{
  var first_step := lemma_EpochLengthForAllEventuallyReaches(b, asp, processing_sync_start, processing_bound, duration + asp.max_clock_ambiguity * 2);
  lemma_ConstantsAllConsistent(b, asp.c, first_step);

  forall idx | 0 <= idx < |b[first_step].replicas|
    ensures LtUpperBound(CurrentViewOfHost(b[first_step], idx).seqno, asp.c.params.max_integer_val)
  {
    lemma_OverflowProtectionNotUsedForReplica(b, asp, first_step, idx);
  }
    
  view := lemma_LaterViewWithPrimaryExists(b[first_step], primary_idx, asp.c.params.max_integer_val);
  assert !sat(first_step, SomeReplicaInLiveQuorumReachedViewTemporal(b, asp.live_quorum, view));

  lemma_IfPacketProcessingSynchronousThenAlways(b, asp, processing_sync_start, first_step, processing_bound);
  var second_step, replica_index := lemma_SomeReplicaInLiveQuorumReachesView(b, asp, first_step, processing_bound, view);
  assert sat(second_step, SomeReplicaInLiveQuorumReachedViewTemporal(b, asp.live_quorum, view));
  TemporalEventually(first_step, second_step, SomeReplicaInLiveQuorumReachedViewTemporal(b, asp.live_quorum, view));
  step := earliestStep(first_step, SomeReplicaInLiveQuorumReachedViewTemporal(b, asp.live_quorum, view));
  assert first_step <= step - 1 < step;
  assert !sat(step-1, SomeReplicaInLiveQuorumReachedViewTemporal(b, asp.live_quorum, view));
  var endTime := b[step].environment.time + duration + asp.max_clock_ambiguity;

  forall idx | idx in asp.live_quorum
    ensures sat(step, always(EpochLengthEqualOrGreaterTemporal(b, idx, duration + asp.max_clock_ambiguity * 2)))
    ensures sat(step-1, EpochLengthEqualOrGreaterTemporal(b, idx, duration + asp.max_clock_ambiguity * 2))
  {
    TemporalDeduceFromAlways(first_step, step-1, EpochLengthEqualOrGreaterTemporal(b, idx, duration + asp.max_clock_ambiguity * 2));
    Lemma_AlwaysImpliesLaterAlways(first_step, step, EpochLengthEqualOrGreaterTemporal(b, idx, duration + asp.max_clock_ambiguity * 2));
  }

  lemma_FirstStepWithLiveReplicaInQuorumHasNoLiveReplicaSuspectingBefore(b, asp, view, duration, step);
  lemma_FirstStepWithLiveReplicaInQuorumHasAllMaxBallot1aBeforeView(b, asp, view, duration, step);
  lemma_NoLiveReplicaSuspectsViewBeforeStable(b, asp, step, view, duration, endTime);
}

lemma lemma_EventuallyBallotStable(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  primary_idx:int,
  duration:int
  ) returns (
  view:Ballot,
  step:int,
  ahead_idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires primary_idx in asp.live_quorum
  requires duration >= 0
  ensures  processing_sync_start <= step
  ensures  view.proposer_id == primary_idx
  ensures  LeqUpperBound(view.seqno, asp.c.params.max_integer_val)
  ensures  sat(step, StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx))
  ensures  sat(step, always(untilabsolutetime(NoReplicaBeyondViewTemporal(b, view), b[step].environment.time + duration, PaxosTimeMap(b))))
{
  view, step := lemma_EventuallyViewStable(b, asp, processing_sync_start, processing_bound, primary_idx, duration+1);
  ahead_idx :| ahead_idx in asp.live_quorum && 0 <= ahead_idx < |b[step].replicas| && BalLeq(view, CurrentViewOfHost(b[step], ahead_idx));
  assert StablePeriodStarted(b[step], asp.live_quorum, view, ahead_idx);

  var time_plus_duration := b[step].environment.time + duration;
  forall i | step <= i
    ensures sat(i, untilabsolutetime(NoReplicaBeyondViewTemporal(b, view), time_plus_duration, PaxosTimeMap(b)))
  {
    TemporalDeduceFromAlways(step, i, NoLiveReplicaSuspectsViewBeforeTemporal(b, asp.live_quorum, view, time_plus_duration + asp.max_clock_ambiguity + 1, asp.max_clock_ambiguity));
    if b[i].environment.time <= time_plus_duration
    {
      assert b[i].environment.time < time_plus_duration + 1;
      lemma_ConstantsAllConsistent(b, asp.c, i);
      forall idx | idx in asp.live_quorum
        ensures ViewPlusLe(CurrentViewPlusOfHost(b[i], idx), ViewPlus(view, false))
      {
        var es := b[i].replicas[idx].replica.proposer.election_state;
        assert || BalLt(es.current_view, view)
               || (&& es.current_view == view
                  && es.constants.my_index !in es.current_view_suspectors
                  && es.epoch_end_time >= time_plus_duration + asp.max_clock_ambiguity + 1);
      }
      lemma_NoOneCanExceedViewUntilAQuorumMemberSuspectsIt(b, asp, i, view);
      assert AllQuorumMembersViewPlusLe(b[i], asp.live_quorum, ViewPlus(view, false));
      assert AllReplicasViewPlusLe(b[i], ViewPlus(view, true));
      forall idx | 0 <= idx < |b[i].replicas|
        ensures BalLeq(CurrentViewOfHost(b[i], idx), view)
      {
        assert ViewPlusLe(CurrentViewPlusOfHost(b[i], idx), ViewPlus(view, true));
        lemma_BalLtProperties();
      }
      assert NoReplicaBeyondView(b[i], view);
    }
  }

  TemporalAlways(step, untilabsolutetime(NoReplicaBeyondViewTemporal(b, view), time_plus_duration, PaxosTimeMap(b)));
}

lemma lemma_EventuallyBallotStableWithRequest(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  processing_sync_start:int,
  processing_bound:int,
  primary_idx:int,
  base_duration:int,
  per_request_duration:int
  ) returns (
  view:Ballot,
  step:int,
  ahead_idx:int,
  num_requests:int,
  duration:int
  )
  requires LivenessAssumptions(b, asp)
  requires PacketProcessingSynchronous(b, asp, processing_sync_start, processing_bound)
  requires primary_idx in asp.live_quorum
  requires base_duration >= 0
  requires per_request_duration >= 0
  ensures  processing_sync_start <= step
  ensures  num_requests > 0
  ensures  view.proposer_id == primary_idx
  ensures  LeqUpperBound(view.seqno, asp.c.params.max_integer_val)
  ensures  duration == base_duration + num_requests * per_request_duration
  ensures  sat(step, StablePeriodStartedTemporal(b, asp.live_quorum, view, ahead_idx))
  ensures  sat(step, always(untilabsolutetime(NoReplicaBeyondViewTemporal(b, view), b[step].environment.time + duration, PaxosTimeMap(b))))
  ensures  sat(step, always(RequestInFirstNTemporal(b, primary_idx, asp.persistent_request, num_requests)))
{
  var first_step := lemma_EventuallyPersistentRequestInRequestsReceivedPrevEpochs(b, asp, processing_sync_start, processing_bound, primary_idx);
  num_requests := |b[first_step].replicas[primary_idx].replica.proposer.election_state.requests_received_prev_epochs|;
  duration := base_duration + num_requests * per_request_duration;
  lemma_mul_nonnegative(num_requests, per_request_duration);
  lemma_PersistentRequestDoesNotIncreasePositionInRequestsReceivedPrevEpochs(b, asp, processing_sync_start, processing_bound, primary_idx, first_step, num_requests);
  lemma_IfPacketProcessingSynchronousThenAlways(b, asp, processing_sync_start, first_step, processing_bound);
  lemma_ConstantsAllConsistent(b, asp.c, first_step);
  view, step, ahead_idx := lemma_EventuallyBallotStable(b, asp, first_step, processing_bound, primary_idx, duration);
  Lemma_AlwaysImpliesLaterAlways(first_step, step, RequestInFirstNTemporal(b, primary_idx, asp.persistent_request, num_requests));
}

}
