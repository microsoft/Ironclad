include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Invariants.i.dfy"
include "ViewChange.i.dfy"
include "WF1.i.dfy"
include "../CommonProof/Actions.i.dfy"
include "../CommonProof/CanonicalizeBallot.i.dfy"
include "../CommonProof/PacketSending.i.dfy"
include "../CommonProof/Quorum.i.dfy"

module LivenessProof__ViewPropagation_i {

import opened LiveRSL__Configuration_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Election_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__StablePeriod_i
import opened LivenessProof__ViewChange_i
import opened LivenessProof__WF1_i
import opened CommonProof__Actions_i
import opened CommonProof__CanonicalizeBallot_i
import opened CommonProof__Constants_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Quorum_i
import opened Concrete_NodeIdentity_i
import opened Temporal__Temporal_s
import opened Collections__Maps2_s
import opened Environment_s

predicate ViewInfoInObserverConsistent(ps:RslState, idx:int, observer_idx:int)
  requires 0 <= idx < |ps.replicas|
  requires 0 <= observer_idx < |ps.replicas|
{
  idx in ps.replicas[observer_idx].replica.proposer.election_state.current_view_suspectors
    ==> ViewPlusLe(ViewPlus(CurrentViewOfHost(ps, observer_idx), true), CurrentViewPlusOfHost(ps, idx))
}

predicate ViewInfoInPacketConsistent(ps:RslState, idx:int, p:RslPacket)
  requires 0 <= idx < |ps.replicas|
{
  0 <= idx < |ps.constants.config.replica_ids| && p.src == ps.constants.config.replica_ids[idx] && p.msg.RslMessage_Heartbeat?
  ==> && IsValidBallot(p.msg.bal_heartbeat, ps.constants)
      && ViewPlusLe(ViewPlus(p.msg.bal_heartbeat, p.msg.suspicious), CurrentViewPlusOfHost(ps, idx))
}

predicate ViewInfoConsistent(ps:RslState, idx:int)
  requires 0 <= idx < |ps.replicas|
{
  && IsValidBallot(CurrentViewOfHost(ps, idx), ps.constants)
  && (forall observer_idx :: 0 <= observer_idx < |ps.replicas| ==> ViewInfoInObserverConsistent(ps, idx, observer_idx))
  && (forall p :: p in ps.environment.sentPackets ==> ViewInfoInPacketConsistent(ps, idx, p))
}

predicate ViewInfoStateInv(ps:RslState)
{
  forall idx :: 0 <= idx < |ps.replicas| ==> ViewInfoConsistent(ps, idx)
}

predicate AllSuspectorsValidStateInv(ps:RslState)
{
  forall idx, suspector_idx
    :: 0 <= idx < |ps.replicas| && suspector_idx in ps.replicas[idx].replica.proposer.election_state.current_view_suspectors
    ==> 0 <= suspector_idx < |ps.replicas|
}

predicate AllQuorumMembersViewPlusLe(ps:RslState, quorum:set<int>, v:ViewPlus)
{
  forall idx :: idx in quorum && 0 <= idx < |ps.replicas| ==> ViewPlusLe(CurrentViewPlusOfHost(ps, idx), v)
}

predicate AllReplicasViewPlusLe(ps:RslState, v:ViewPlus)
{
  forall idx :: 0 <= idx < |ps.replicas| ==> ViewPlusLe(CurrentViewPlusOfHost(ps, idx), v)
}

predicate NoMemberBeyondViewUntilAQuorumMemberSuspectsIt(ps:RslState, quorum:set<int>, v:Ballot)
{
  AllQuorumMembersViewPlusLe(ps, quorum, ViewPlus(v, false)) ==> AllReplicasViewPlusLe(ps, ViewPlus(v, true))
}

predicate HostSuspectsOrInLaterViewWithSpecificNextHeartbeatTime(
  ps:RslState,
  replica_index:int,
  view:Ballot,
  nextHeartbeatTime:int
  )
{
  && 0 <= replica_index < |ps.replicas|
  && ViewPlusLe(ViewPlus(view, true), CurrentViewPlusOfHost(ps, replica_index))
  && ps.replicas[replica_index].replica.nextHeartbeatTime == nextHeartbeatTime
}

function{:opaque} HostSuspectsOrInLaterViewWithSpecificNextHeartbeatTimeTemporal(
  b:Behavior<RslState>,
  replica_index:int,
  view:Ballot,
  nextHeartbeatTime:int
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, HostSuspectsOrInLaterViewWithSpecificNextHeartbeatTimeTemporal(b, replica_index, view, nextHeartbeatTime))} ::
             sat(i, HostSuspectsOrInLaterViewWithSpecificNextHeartbeatTimeTemporal(b, replica_index, view, nextHeartbeatTime)) <==>
             HostSuspectsOrInLaterViewWithSpecificNextHeartbeatTime(b[i], replica_index, view, nextHeartbeatTime)
{
  stepmap(imap i :: HostSuspectsOrInLaterViewWithSpecificNextHeartbeatTime(b[i], replica_index, view, nextHeartbeatTime))
}

predicate HostSentSuspicion(
  ps:RslState,
  sid:NodeIdentity,
  oid:NodeIdentity,
  view:Ballot,
  p:RslPacket
  )
{
  && p.dst == oid
  && p.src == sid
  && p.msg.RslMessage_Heartbeat?
  && p.msg.bal_heartbeat == view
  && p.msg.suspicious
  && ps.environment.nextStep.LEnvStepHostIos?
  && LIoOpSend(p) in ps.environment.nextStep.ios
}

predicate HostSentSuspicionOrInLaterView(
  ps:RslState,
  suspector_idx:int,
  observer_idx:int,
  view:Ballot
  )
{
  && |ps.replicas| == |ps.constants.config.replica_ids|
  && 0 <= suspector_idx < |ps.replicas|
  && 0 <= observer_idx < |ps.replicas|
  && (|| BalLt(view, CurrentViewOfHost(ps, suspector_idx))
     || exists p :: HostSentSuspicion(ps, ps.constants.config.replica_ids[suspector_idx], ps.constants.config.replica_ids[observer_idx], view, p))
}

function{:opaque} HostSentSuspicionOrInLaterViewTemporal(
  b:Behavior<RslState>,
  suspector_idx:int,
  observer_idx:int,
  view:Ballot
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, HostSentSuspicionOrInLaterViewTemporal(b, suspector_idx, observer_idx, view))} ::
             sat(i, HostSentSuspicionOrInLaterViewTemporal(b, suspector_idx, observer_idx, view)) ==
             HostSentSuspicionOrInLaterView(b[i], suspector_idx, observer_idx, view)
{
  stepmap(imap i :: HostSentSuspicionOrInLaterView(b[i], suspector_idx, observer_idx, view))
}

predicate SuspicionPropagatedToObserver(
  ps:RslState,
  suspector_idx:int,
  observer_idx:int,
  view:Ballot
  )
{
  && |ps.replicas| == |ps.constants.config.replica_ids|
  && 0 <= suspector_idx < |ps.replicas|
  && 0 <= observer_idx < |ps.replicas|
  && (|| BalLt(view, CurrentViewOfHost(ps, suspector_idx))
     || BalLt(view, CurrentViewOfHost(ps, observer_idx))
     || (&& CurrentViewOfHost(ps, observer_idx) == view
        && suspector_idx in ps.replicas[observer_idx].replica.proposer.election_state.current_view_suspectors))
}

function{:opaque} SuspicionPropagatedToObserverTemporal(
  b:Behavior<RslState>,
  suspector_idx:int,
  observer_idx:int,
  view:Ballot
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, SuspicionPropagatedToObserverTemporal(b, suspector_idx, observer_idx, view))} ::
             sat(i, SuspicionPropagatedToObserverTemporal(b, suspector_idx, observer_idx, view)) ==
             SuspicionPropagatedToObserver(b[i], suspector_idx, observer_idx, view)
{
  stepmap(imap i :: SuspicionPropagatedToObserver(b[i], suspector_idx, observer_idx, view))
}

lemma lemma_PaxosNextPreservesViewInfoInObserverConsistent(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int,
  observer_idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires ViewInfoStateInv(b[i])
  requires 0 <= idx < |b[i+1].replicas|
  requires 0 <= observer_idx < |b[i+1].replicas|
  ensures  ViewInfoInObserverConsistent(b[i+1], idx, observer_idx)
{
  lemma_AssumptionsMakeValidTransition(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i+1);

  var ps := b[i];
  var ps' := b[i+1];
  var s := ps.replicas[observer_idx].replica;
  var s' := ps'.replicas[observer_idx].replica;
  var es := s.proposer.election_state;
  var es' := s'.proposer.election_state;
  assert RslNext(ps, ps');

  lemma_ViewPlusOfHostMonotonic(b, asp, idx, i, i+1);
  assert ViewInfoConsistent(ps, idx);
  assert ViewInfoInObserverConsistent(ps, idx, observer_idx);
//  lemma_LEnvironmentInvariantHolds(b, asp, i);

  if idx in es'.current_view_suspectors
  {
    if idx in es.current_view_suspectors
    {
      if es.current_view != es'.current_view
      {
        var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, observer_idx);
        assert LReplicaNextProcessHeartbeat(s, s', ios[0].r, ios[1].t, ExtractSentPacketsFromIos(ios));
        lemma_PacketProcessedImpliesPacketSent(ps, ps', observer_idx, ios, ios[0].r);
        assert ViewInfoInPacketConsistent(ps, idx, ios[0].r);
      }
    }
    else
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, observer_idx);
      if |ios| >= 2 && ios[0].LIoOpReceive? && ios[1].LIoOpReadClock? &&
         LReplicaNextProcessHeartbeat(s, s', ios[0].r, ios[1].t, ExtractSentPacketsFromIos(ios))
      {
        lemma_PacketProcessedImpliesPacketSent(ps, ps', observer_idx, ios, ios[0].r);
        assert ViewInfoInPacketConsistent(ps, idx, ios[0].r);
      }
      else if LReplicaNextReadClockCheckForViewTimeout(s, s', SpontaneousClock(ios), ExtractSentPacketsFromIos(ios))
      {
        assert idx == observer_idx;
      }
    }
  }
}

lemma{:timeLimitMultiplier 2} lemma_PaxosNextPreservesViewInfoInPacketConsistent(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int,
  p:RslPacket
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires ViewInfoStateInv(b[i])
  requires 0 <= idx < |b[i+1].replicas|
  requires p in b[i+1].environment.sentPackets
  ensures  ViewInfoInPacketConsistent(b[i+1], idx, p)
{
  lemma_AssumptionsMakeValidTransition(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i+1);

  var ps := b[i];
  var ps' := b[i+1];
  var s := ps.replicas[idx].replica;
  var s' := ps'.replicas[idx].replica;
  var es := s.proposer.election_state;
  var es' := s'.proposer.election_state;
  assert RslNext(ps, ps');

  assert ViewInfoConsistent(ps, idx);

  if p.src == ps.constants.config.replica_ids[idx] && p.msg.RslMessage_Heartbeat?
  {
    if p in ps.environment.sentPackets
    {
      assert ViewInfoInPacketConsistent(ps, idx, p);
      lemma_ViewPlusOfHostMonotonic(b, asp, idx, i, i+1);
      lemma_ViewPlusLeTransitive(ViewPlus(p.msg.bal_heartbeat, p.msg.suspicious), CurrentViewPlusOfHost(ps, idx), CurrentViewPlusOfHost(ps', idx));
    }
    else
    {
      var observer_idx, ios := lemma_ActionThatSendsHeartbeatIsMaybeSendHeartbeat(ps, ps', p);
      assert ReplicasDistinct(ps.constants.config.replica_ids, idx, observer_idx);
      assert idx == observer_idx;
    }
  }
}

lemma lemma_PaxosNextPreservesIsValidBallot(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires ViewInfoStateInv(b[i])
  requires 0 <= idx < |b[i+1].replicas|
  ensures  IsValidBallot(CurrentViewOfHost(b[i+1], idx), b[i+1].constants)
{
  lemma_AssumptionsMakeValidTransition(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i+1);

  var ps := b[i];
  var ps' := b[i+1];
  var s := ps.replicas[idx].replica;
  var s' := ps'.replicas[idx].replica;
  var es := s.proposer.election_state;
  var es' := s'.proposer.election_state;
  assert RslNext(ps, ps');

//  lemma_LEnvironmentInvariantHolds(b, asp, i);
  assert ViewInfoConsistent(b[i], idx);

  if es'.current_view != es.current_view
  {
    var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, idx);
    var sent_packets := ExtractSentPacketsFromIos(ios);
    if && |ios| > 1
       && ios[1].LIoOpReadClock?
       && LReplicaNextProcessHeartbeat(s, s', ios[0].r, ios[1].t, sent_packets)
       && ios[0].r.src in asp.c.config.replica_ids
    {
      var p := ios[0].r;
      var sender_idx := GetReplicaIndex(p.src, ps.constants.config);
      lemma_PacketProcessedImpliesPacketSent(ps, ps', idx, ios, p);
      assert ViewInfoConsistent(ps, sender_idx);
      assert ViewInfoInPacketConsistent(ps, sender_idx, p);
      assert IsValidBallot(p.msg.bal_heartbeat, ps.constants);
      assert IsValidBallot(es'.current_view, ps'.constants);
    }
    else if LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, s', SpontaneousClock(ios), sent_packets)
    {
      assert es'.current_view == ComputeSuccessorView(es.current_view, es.constants.all);
      lemma_ComputeSuccessorViewProducesValidBallot(es.current_view, es.constants.all);
      assert IsValidBallot(es'.current_view, ps'.constants);
    }
    else
    {
      assert false;
    }
  }
}

lemma lemma_ViewInfoStateInvHolds(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  ensures  ViewInfoStateInv(b[i])
{
  if i > 0
  {
    lemma_ViewInfoStateInvHolds(b, asp, i-1);
    forall idx, observer_idx | 0 <= idx < |b[i].replicas| && 0 <= observer_idx < |b[i].replicas|
      ensures ViewInfoInObserverConsistent(b[i], idx, observer_idx)
    {
      lemma_PaxosNextPreservesViewInfoInObserverConsistent(b, asp, i-1, idx, observer_idx);
    }

    forall idx, p | 0 <= idx < |b[i].replicas| && p in b[i].environment.sentPackets
      ensures ViewInfoInPacketConsistent(b[i], idx, p)
    {
      lemma_PaxosNextPreservesViewInfoInPacketConsistent(b, asp, i-1, idx, p);
    }

    forall idx | 0 <= idx < |b[i].replicas|
      ensures IsValidBallot(CurrentViewOfHost(b[i], idx), b[i].constants)
    {
      lemma_PaxosNextPreservesIsValidBallot(b, asp, i-1, idx);
    }
  }
}

lemma{:timeLimitMultiplier 2} lemma_AllSuspectorsValidStateInvHolds(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  ensures  AllSuspectorsValidStateInv(b[i])
{
  if i > 0
  {
    lemma_AssumptionsMakeValidTransition(b, asp.c, i-1);
    lemma_AllSuspectorsValidStateInvHolds(b, asp, i-1);
    lemma_ConstantsAllConsistent(b, asp.c, i-1);
    lemma_ConstantsAllConsistent(b, asp.c, i);

    var ps := b[i-1];
    var ps' := b[i];
    if !AllSuspectorsValidStateInv(b[i])
    {
      var idx, suspector_idx :| && 0 <= idx < |ps'.replicas|
                                && suspector_idx in ps'.replicas[idx].replica.proposer.election_state.current_view_suspectors
                                && !(0 <= suspector_idx < |ps'.replicas|);
      var s := ps.replicas[idx].replica;
      var s' := ps'.replicas[idx].replica;
      var es := s.proposer.election_state;
      var es' := s'.proposer.election_state;
      assert suspector_idx in es'.current_view_suspectors - es.current_view_suspectors;
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i-1, idx);
      var sent_packets := ExtractSentPacketsFromIos(ios);
      if |ios| > 1 && ios[1].LIoOpReadClock? && LReplicaNextProcessHeartbeat(s, s', ios[0].r, ios[1].t, sent_packets) && ios[0].r.src in asp.c.config.replica_ids
      {
        assert suspector_idx == GetReplicaIndex(ios[0].r.src, es.constants.all.config);
        assert false;
      }
      else if LReplicaNextReadClockCheckForViewTimeout(s, s', SpontaneousClock(ios), sent_packets)
      {
        assert suspector_idx == es.constants.my_index;
        assert false;
      }
      else
      {
        assert false;
      }
    }
  }
}

lemma lemma_IsValidBallot(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  ensures  IsValidBallot(CurrentViewOfHost(b[i], idx), asp.c)
{
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ViewInfoStateInvHolds(b, asp, i);
  assert ViewInfoConsistent(b[i], idx);
}

lemma lemma_CantChangeViewIfNoOneInQuorumSuspects(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  idx:int,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires 0 <= view.proposer_id < |asp.c.config.replica_ids|
  requires AllQuorumMembersViewPlusLe(b[i], asp.live_quorum, ViewPlus(view, false))
  requires 0 <= idx < |b[i].replicas|
  requires 0 <= idx < |b[i+1].replicas|
  requires ViewPlusLe(CurrentViewPlusOfHost(b[i], idx), ViewPlus(view, true))
  requires ViewPlusLt(ViewPlus(view, true), CurrentViewPlusOfHost(b[i+1], idx))
  requires AllReplicasViewPlusLe(b[i], ViewPlus(view, true))
  ensures  false
{
  lemma_AssumptionsMakeValidTransition(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i+1);

  var ps := b[i];
  var ps' := b[i+1];
  var s := ps.replicas[idx].replica;
  var s' := ps'.replicas[idx].replica;
  var es := s.proposer.election_state;

  lemma_BalLtProperties();
  assert BalLt(CurrentViewOfHost(ps, idx), CurrentViewOfHost(ps', idx));
  assert BalLt(view, CurrentViewOfHost(ps', idx));

//  lemma_LEnvironmentInvariantHolds(b, asp, i);
  lemma_ViewInfoStateInvHolds(b, asp, i);

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, asp.c, i, idx);
  var sent_packets := ExtractSentPacketsFromIos(ios);
  
  if |ios| > 1 && ios[1].LIoOpReadClock? && LReplicaNextProcessHeartbeat(s, s', ios[0].r, ios[1].t, sent_packets) && ios[0].r.src in asp.c.config.replica_ids
  {
    var p := ios[0].r;
    var oid := p.src;
    var sender_index := GetReplicaIndex(oid, es.constants.all.config);
    lemma_PacketProcessedImpliesPacketSent(ps, ps', idx, ios, p);
    assert p in ps.environment.sentPackets;
    assert ViewInfoConsistent(ps, sender_index);
    assert ViewInfoInPacketConsistent(ps, sender_index, p);
    assert ViewPlusLe(CurrentViewPlusOfHost(ps, sender_index), ViewPlus(view, true));
    assert false;
  }
  else if LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, s', SpontaneousClock(ios), sent_packets)
  {
    assert |es.current_view_suspectors| >= LMinQuorumSize(es.constants.all.config);
    lemma_AllSuspectorsValidStateInvHolds(b, asp, i);
    var common_index := lemma_QuorumIndexOverlap(es.current_view_suspectors, asp.live_quorum, |asp.c.config.replica_ids|);
    assert ViewPlusLe(CurrentViewPlusOfHost(ps, common_index), ViewPlus(view, false));
    assert ViewInfoConsistent(ps, common_index);
    assert ViewInfoInObserverConsistent(ps, common_index, idx);
    assert ViewPlusLe(ViewPlus(CurrentViewOfHost(ps, idx), true), CurrentViewPlusOfHost(ps, common_index));
    lemma_ViewPlusLeTransitiveDefinite(ViewPlus(CurrentViewOfHost(ps, idx), true), CurrentViewPlusOfHost(ps, common_index), ViewPlus(view, false));
    assert BalLt(CurrentViewOfHost(ps, idx), view);
    assert BalLt(view, CurrentViewOfHost(ps', idx));
    lemma_OverflowProtectionNotUsedForReplica(b, asp, i, idx);
    lemma_NothingBetweenViewAndSuccessor(CurrentViewOfHost(ps, idx), view, es.constants.all);
    assert false;
  }
  else
  {
    assert false;
  }
}

lemma lemma_NoOneCanExceedViewUntilAQuorumMemberSuspectsItOneStep(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires 0 <= view.proposer_id < |asp.c.config.replica_ids|
  requires NoMemberBeyondViewUntilAQuorumMemberSuspectsIt(b[i], asp.live_quorum, view)
  ensures  NoMemberBeyondViewUntilAQuorumMemberSuspectsIt(b[i+1], asp.live_quorum, view)
{
  lemma_AssumptionsMakeValidTransition(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i);
  lemma_ConstantsAllConsistent(b, asp.c, i+1);

  var ps := b[i];
  var ps' := b[i+1];
  assert RslNext(ps, ps');
  if !NoMemberBeyondViewUntilAQuorumMemberSuspectsIt(ps', asp.live_quorum, view)
  {
    forall live_idx | live_idx in asp.live_quorum
      ensures ViewPlusLe(CurrentViewPlusOfHost(ps, live_idx), ViewPlus(view, false))
    {
      lemma_ViewPlusOfHostMonotonic(b, asp, live_idx, i, i+1);
      lemma_ViewPlusLeTransitiveDefinite(CurrentViewPlusOfHost(ps, live_idx), CurrentViewPlusOfHost(ps', live_idx), ViewPlus(view, false));
    }
    assert AllQuorumMembersViewPlusLe(ps, asp.live_quorum, ViewPlus(view, false));
    assert AllReplicasViewPlusLe(ps, ViewPlus(view, true));

    var idx :| 0 <= idx < |ps.replicas| && !ViewPlusLe(CurrentViewPlusOfHost(ps', idx), ViewPlus(view, true));
    assert ViewPlusLe(CurrentViewPlusOfHost(ps, idx), ViewPlus(view, true));
    lemma_CantChangeViewIfNoOneInQuorumSuspects(b, asp, i, idx, view);
  }
}

lemma lemma_NoOneCanExceedViewUntilAQuorumMemberSuspectsIt(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  view:Ballot
  )
  requires LivenessAssumptions(b, asp)
  requires 0 <= i
  requires 0 <= view.proposer_id < |asp.c.config.replica_ids|
  ensures  NoMemberBeyondViewUntilAQuorumMemberSuspectsIt(b[i], asp.live_quorum, view)
{
  lemma_BalLtProperties();

  lemma_ConstantsAllConsistent(b, asp.c, i);

  if i == 0
  {
    assert forall idx :: 0 <= idx < |b[i].replicas| ==> CurrentViewPlusOfHost(b[i], idx) == ViewPlus(Ballot(1, 0), false);
    if BalLt(view, Ballot(1, 0))
    {
      var idx :| idx in asp.live_quorum;
      assert CurrentViewPlusOfHost(b[i], idx) == ViewPlus(Ballot(1, 0), false);
      assert !ViewPlusLe(CurrentViewPlusOfHost(b[i], idx), ViewPlus(view, false));
      assert !AllQuorumMembersViewPlusLe(b[i], asp.live_quorum, ViewPlus(view, false));
    }
    else
    {
      forall idx | 0 <= idx < |b[i].replicas|
        ensures ViewPlusLe(CurrentViewPlusOfHost(b[i], idx), ViewPlus(view, true))
      {
        assert CurrentViewPlusOfHost(b[i], idx) == ViewPlus(Ballot(1, 0), false);
      }
      assert AllReplicasViewPlusLe(b[i], ViewPlus(view, true));
    }
  }
  else
  {
    lemma_NoOneCanExceedViewUntilAQuorumMemberSuspectsIt(b, asp, i-1, view);
    lemma_NoOneCanExceedViewUntilAQuorumMemberSuspectsItOneStep(b, asp, i-1, view);
  }
}

}
