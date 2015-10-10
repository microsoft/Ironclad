include "AppInterface.i.dfy"
include "ProposerState.i.dfy"
include "ElectionModel.i.dfy"
include "Broadcast.i.dfy"
include "MinCQuorumSize.i.dfy"
include "ProposerLemmas.i.dfy"
include "../Common/Util.i.dfy"
include "../../Common/Collections/Sets.i.dfy"

module LiveRSL__ProposerModel_i {
import opened LiveRSL__AppInterface_i
import opened LiveRSL__ProposerState_i
import opened LiveRSL__ElectionModel_i
import opened Impl__LiveRSL__Broadcast_i
import opened LiveRSL__MinCQuorumSize_i
import opened LiveRSL__ProposerLemmas_i
import opened Collections__Sets_i

// Same as x == y, but triggers extensional equality on fields and provides better error diagnostics
predicate Eq_LProposer(x:LProposer, y:LProposer)
{
       x.constants == y.constants
    && x.current_state == y.current_state
    && x.request_queue == y.request_queue
    && x.max_ballot_i_sent_1a == y.max_ballot_i_sent_1a
    && x.next_operation_number_to_propose == y.next_operation_number_to_propose 
    && x.received_1b_packets == y.received_1b_packets
    && x.highest_seqno_requested_by_client_this_view == y.highest_seqno_requested_by_client_this_view
    && x.election_state == y.election_state 
}

method InitProposerState(constants:ReplicaConstantsState) returns (proposer:ProposerState, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>)
    requires ReplicaConstantsState_IsValid(constants);
    ensures  ProposerIsAbstractable(proposer);
    ensures  WellFormedLConfiguration(AbstractifyReplicaConstantsStateToLReplicaConstants(constants).all.config);
    ensures  ProposerIsValid(proposer);
    ensures  LProposerInit(AbstractifyProposerStateToLProposer(proposer), AbstractifyReplicaConstantsStateToLReplicaConstants(constants));
    ensures  proposer.constants == constants;
    ensures  fresh(cur_req_set) && fresh(prev_req_set) && cur_req_set != prev_req_set;
    ensures  MutableSet.SetOf(cur_req_set) == proposer.election_state.cur_req_set;
    ensures  MutableSet.SetOf(prev_req_set) == proposer.election_state.prev_req_set;
{
    var election;
    election, cur_req_set, prev_req_set := InitElectionState(constants);
    proposer := ProposerState(constants,
                              0,
                              [],
                              CBallot(0, constants.my_index),
                              0,
                              {},
                              map [],
                              CIncompleteBatchTimerOff(),
                              election,
                              COperationNumber(0),
                              COperationNumber(0));
    ghost var ref_proposer := AbstractifyProposerStateToLProposer(proposer);
    ghost var ref_constants := AbstractifyReplicaConstantsStateToLReplicaConstants(constants);

    calc ==> {
        true;
            { reveal_SeqIsUnique(); }
        SeqIsUnique(proposer.request_queue);
    }

    calc ==> {
        true;
            { reveal_Received1bProperties(); }
        Received1bProperties(proposer.received_1b_packets, proposer.constants);
    }

    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(proposer.received_1b_packets);

    // Some subset of below is an OBSERVE?
    assert ref_proposer.constants == ref_constants;
    assert ref_proposer.current_state == 0;
    assert ref_proposer.request_queue == [];
    assert ref_proposer.max_ballot_i_sent_1a == Ballot(0, ref_constants.my_index);
    assert ref_proposer.next_operation_number_to_propose == 0;
    assert ref_proposer.received_1b_packets == {};
    lemma_AbstractifyMapOfSeqNums_properties(proposer.highest_seqno_requested_by_client_this_view); 
    assert ElectionStateInit(ref_proposer.election_state, ref_constants);
}

//function method maprange_impl<KT,VT>(m:map<KT,VT>) : set<VT>
//{
//    set k | k in m :: m[k]
//}

method {:timeLimitMultiplier 2} ProposerProcessRequest(proposer:ProposerState, packet:CPacket, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (proposer':ProposerState)
    requires ProposerIsValid(proposer);
    requires CPacketIsAbstractable(packet);
    requires packet.msg.CMessage_Request?;
    requires ValidAppMessage(packet.msg.val);
    requires cur_req_set != null && prev_req_set != null && cur_req_set != prev_req_set;
    requires MutableSet.SetOf(cur_req_set) == proposer.election_state.cur_req_set;
    requires MutableSet.SetOf(prev_req_set) == proposer.election_state.prev_req_set;
    modifies cur_req_set;
    ensures  ProposerIsValid(proposer');
    ensures  LProposerProcessRequest(AbstractifyProposerStateToLProposer(proposer), AbstractifyProposerStateToLProposer(proposer'), AbstractifyCPacketToRslPacket(packet));
    ensures proposer.constants == proposer'.constants;
    ensures  MutableSet.SetOf(cur_req_set) == proposer'.election_state.cur_req_set;
    ensures  MutableSet.SetOf(prev_req_set) == proposer'.election_state.prev_req_set;
{
    ghost var ref_proposer  := AbstractifyProposerStateToLProposer(proposer);
    ghost var r_proposer;
    ghost var r_packet := AbstractifyCPacketToRslPacket(packet);
    var val := CRequest(packet.src, packet.msg.seqno, packet.msg.val);
    //var election_start_time := Time.GetDebugTimeTicks();
    var newElectionState := ElectionReflectReceivedRequest(proposer.election_state, val, cur_req_set, prev_req_set);
    //var election_end_time := Time.GetDebugTimeTicks();
    //RecordTimingSeq("ProposerProcessRequest_Election", election_start_time, election_end_time);

    ghost var ref_val := AbstractifyCRequestToRequest(val);
    ghost var ref_myOutstandingProposedValues := AbstractifyMapOfSeqNums(proposer.highest_seqno_requested_by_client_this_view);
    lemma_AbstractifyMapOfSeqNums_properties(proposer.highest_seqno_requested_by_client_this_view);
    assert forall e :: (e !in proposer.highest_seqno_requested_by_client_this_view && EndPointIsValidIPV4(e) ==> AbstractifyEndPointToNodeIdentity(e) !in AbstractifyMapOfSeqNums(proposer.highest_seqno_requested_by_client_this_view));
    assert EndPointIsValidIPV4(packet.src);
    assert packet.src !in proposer.highest_seqno_requested_by_client_this_view ==> AbstractifyEndPointToNodeIdentity(packet.src) !in AbstractifyMapOfSeqNums(proposer.highest_seqno_requested_by_client_this_view);
    assert packet.src in proposer.highest_seqno_requested_by_client_this_view ==> 
           (packet.msg.seqno > proposer.highest_seqno_requested_by_client_this_view[packet.src] <==>
            r_packet.msg.seqno_req > ref_proposer.highest_seqno_requested_by_client_this_view[r_packet.src]);
    
    //var lookup_start_time := Time.GetDebugTimeTicks();
    if proposer.current_state != 0 && 
       (packet.src !in proposer.highest_seqno_requested_by_client_this_view ||
        packet.msg.seqno > proposer.highest_seqno_requested_by_client_this_view[packet.src]) {
//        var lookup_end_time := Time.GetDebugTimeTicks();
//        RecordTimingSeq("ProposerProcessRequest_Lookup", lookup_start_time, lookup_end_time);
        //print("Processing request with seqno ", packet.msg.seqno, ". Inside if .\n");
        assert r_packet.src !in ref_proposer.highest_seqno_requested_by_client_this_view ||
               r_packet.msg.seqno_req > ref_proposer.highest_seqno_requested_by_client_this_view[r_packet.src];

        //var map_update_start_time := Time.GetDebugTimeTicks();
        var new_seqno_map := proposer.highest_seqno_requested_by_client_this_view[packet.src := packet.msg.seqno];
        //var map_update_end_time := Time.GetDebugTimeTicks();
        //RecordTimingSeq("ProposerProcessRequest_MapUpdate", map_update_start_time, map_update_end_time);

        //var proposer_update_start_time := Time.GetDebugTimeTicks();
        proposer' := proposer[election_state := newElectionState]
                             [request_queue := proposer.request_queue + [val]]
                             [highest_seqno_requested_by_client_this_view := new_seqno_map];
        //var proposer_update_end_time := Time.GetDebugTimeTicks();
        lemma_AbstractifyMapOfSeqNums_properties(new_seqno_map);
        r_proposer := ref_proposer[election_state := AbstractifyCElectionStateToElectionState(newElectionState)]
                                  [request_queue := ref_proposer.request_queue + [ref_val]]
                                  [highest_seqno_requested_by_client_this_view := 
                                   ref_proposer.highest_seqno_requested_by_client_this_view
                                      [r_packet.src := r_packet.msg.seqno_req]];
        ghost var ref_proposer' := AbstractifyProposerStateToLProposer(proposer');
        assert Eq_LProposer(r_proposer, ref_proposer');
        assert LProposerProcessRequest(ref_proposer, r_proposer, r_packet);
        //RecordTimingSeq("ProposerProcessRequest_ProposerUpdate", proposer_update_start_time, proposer_update_end_time);
    } else {
        //var lookup_end_time := Time.GetDebugTimeTicks();
        //RecordTimingSeq("ProposerProcessRequest_Lookup", lookup_start_time, lookup_end_time);
        //print("Processing request with seqno ", packet.msg.seqno, ". Inside else.\n");
        proposer' := proposer[election_state := newElectionState];
        r_proposer := ref_proposer[election_state := AbstractifyCElectionStateToElectionState(newElectionState)];
        ghost var ref_proposer' := AbstractifyProposerStateToLProposer(proposer');
        assert Eq_LProposer(r_proposer, ref_proposer');
        assert LProposerProcessRequest(ref_proposer, r_proposer, r_packet);
    }
}

method ProposerMaybeEnterNewViewAndSend1a(proposer:ProposerState) returns (proposer':ProposerState, sent_packets:CBroadcast)
    requires ProposerIsValid(proposer);
    ensures  ProposerIsValid(proposer');
    ensures  CBroadcastIsValid(sent_packets);
    ensures  OutboundPacketsHasCorrectSrc(Broadcast(sent_packets), proposer.constants.all.config.replica_ids[proposer.constants.my_index]);

    ensures  LProposerMaybeEnterNewViewAndSend1a(AbstractifyProposerStateToLProposer(proposer), AbstractifyProposerStateToLProposer(proposer'), AbstractifyCBroadcastToRlsPacketSeq(sent_packets));
    ensures proposer.constants == proposer'.constants;
    ensures proposer'.election_state.cur_req_set == proposer.election_state.cur_req_set;
    ensures proposer'.election_state.prev_req_set == proposer.election_state.prev_req_set;
{
    var start_time := Time.GetDebugTimeTicks();
    ghost var ref_proposer  := AbstractifyProposerStateToLProposer(proposer);
    //lemma_ProposerId(proposer);
    var lt := CBalLt(proposer.max_ballot_i_sent_1a, proposer.election_state.current_view);
    if proposer.election_state.current_view.proposer_id == proposer.constants.my_index && lt {
        //print "Proposer becoming leader of ballot ", proposer.election_state.current_view, "\n";
        lemma_AbstractifyCRequestsSeqToRequestsSeq_concat(proposer.election_state.requests_received_prev_epochs, 
                                         proposer.election_state.requests_received_this_epoch);
        assert RequestQueueValid(proposer.election_state.requests_received_prev_epochs);
        assert RequestQueueValid(proposer.election_state.requests_received_this_epoch);
        var new_requestQueue := proposer.election_state.requests_received_prev_epochs 
                              + proposer.election_state.requests_received_this_epoch;

        assert |new_requestQueue| == |proposer.election_state.requests_received_prev_epochs| + |proposer.election_state.requests_received_this_epoch|;
        proposer' := proposer[current_state := 1]
                             [max_ballot_i_sent_1a := proposer.election_state.current_view]
                             [received_1b_packets := {}]
                             [highest_seqno_requested_by_client_this_view := map[]]
                             [request_queue := new_requestQueue];
        calc ==> {
            true;
                { reveal_Received1bProperties(); }
            Received1bProperties(proposer'.received_1b_packets, proposer.constants);
        }
        var msg := CMessage_1a(proposer.election_state.current_view);
        assert Marshallable(msg);
        assert CPaxosConfigurationIsValid(proposer.constants.all.config);
        sent_packets := BuildBroadcastToEveryone(proposer.constants.all.config, proposer.constants.my_index, msg);

        lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(proposer.received_1b_packets);

        // Some subset of the below is an OBSERVE
        ghost var ref_proposer' := AbstractifyProposerStateToLProposer(proposer');
        assert ref_proposer'.current_state == 1;
        assert ref_proposer'.max_ballot_i_sent_1a == ref_proposer.election_state.current_view;
        assert ref_proposer'.received_1b_packets  == {};
        lemma_AbstractifyMapOfSeqNums_properties(proposer'.highest_seqno_requested_by_client_this_view); 
        assert LBroadcastToEveryone(ref_proposer.constants.all.config, ref_proposer.constants.my_index, RslMessage_1a(ref_proposer.election_state.current_view), AbstractifyCBroadcastToRlsPacketSeq(sent_packets));
        var end_time := Time.GetDebugTimeTicks();
        RecordTimingSeq("ProposerMaybeEnterNewViewAndSend1a_work", start_time, end_time);
    } else {
        proposer' := proposer;
        sent_packets := CBroadcastNop;
        var end_time := Time.GetDebugTimeTicks();
        RecordTimingSeq("ProposerMaybeEnterNewViewAndSend1a_nada", start_time, end_time);
    }
}

method ProposerProcess1b(proposer:ProposerState, packet:CPacket) returns (proposer':ProposerState)
    requires ProposerIsValid(proposer);
    requires proposer.current_state == 1;
    requires EndPointIsValidIPV4(packet.src);
    requires packet.src in proposer.constants.all.config.replica_ids;
    requires packet.msg.CMessage_1b?;
    requires packet.msg.bal_1b == proposer.max_ballot_i_sent_1a;
    requires ValidVotes(packet.msg.votes);
    requires CPacketIsAbstractable(packet);
    requires forall other_packet :: other_packet in proposer.received_1b_packets ==> other_packet.src != packet.src;
    ensures  ProposerIsValid(proposer');
    ensures  forall other_packet :: other_packet in AbstractifyProposerStateToLProposer(proposer).received_1b_packets ==> other_packet.src != AbstractifyCPacketToRslPacket(packet).src;
    ensures  LProposerProcess1b(AbstractifyProposerStateToLProposer(proposer), AbstractifyProposerStateToLProposer(proposer'), AbstractifyCPacketToRslPacket(packet));
    ensures proposer.constants == proposer'.constants;
    ensures proposer'.election_state.cur_req_set == proposer.election_state.cur_req_set;
    ensures proposer'.election_state.prev_req_set == proposer.election_state.prev_req_set;
{
    //print("Proposer processing a 1b message about ballot", packet.msg.bal_1b, "\n");
    proposer' := proposer[received_1b_packets := proposer.received_1b_packets + { packet }];

    // Prove Received1bProperties
    reveal_Received1bProperties();
    forall p | p in proposer'.received_1b_packets
        ensures p.src in proposer.constants.all.config.replica_ids;
    {
        if p in proposer.received_1b_packets {
            assert p.src in proposer.constants.all.config.replica_ids;
        } else {
            assert p == packet && packet.src in proposer.constants.all.config.replica_ids;
        }
    }

    forall p1,p2 | p1 in proposer'.received_1b_packets && p2 in proposer'.received_1b_packets && p1.src == p2.src
        ensures p1 == p2;
    {
        if p1 in proposer.received_1b_packets && p2 in proposer.received_1b_packets {
            assert p1 == p2;
        } else if p1 in proposer.received_1b_packets {
            assert p2 == packet;
            assert p2.src != p1.src;
            assert false;
        } else if p2 in proposer.received_1b_packets {
            assert p1 == packet;
            assert p2.src != p1.src;
            assert false;
        } else {
            assert p1 == packet == p2;
        }
    }

    ghost var ref_proposer  := AbstractifyProposerStateToLProposer(proposer);
    ghost var ref_proposer' := AbstractifyProposerStateToLProposer(proposer');
    ghost var ref_packet := AbstractifyCPacketToRslPacket(packet);
    calc {
        ref_proposer'.received_1b_packets;
            { reveal_AbstractifySetOfCPacketsToSetOfRslPackets(); }
        ref_proposer.received_1b_packets + { ref_packet };
    }
    //assert ref_proposer'.received_1b_packets == ref_proposer.received_1b_packets + { ref_packet };
    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_srcMembership(proposer.received_1b_packets, packet.src);
}

lemma lemma_MapSingleton<T,S>(m:map<T,S>, elm:T)
    requires |m| == 1;
    requires elm in m;
    ensures forall x :: x in m ==> x == elm;
{
    var empty := RemoveElt(m, elm);
}

method getMaxOpnWithProposalFromSingleton(m:map<COperationNumber,CVote>) returns (maxOpn:COperationNumber)
    requires |m| > 0;
    ensures forall opn :: opn in m ==> opn.n <= maxOpn.n;
{
    if |m| == 1 
    {
        var opn :| opn in m;
        lemma_MapSingleton(m, opn);
        assert forall op :: op in m ==> op == opn;
        maxOpn := opn;
    } else {
        var opn :| opn in m;
        var rest := RemoveElt(m, opn);
        var restMax:COperationNumber;
        
        restMax := getMaxOpnWithProposalFromSingleton(rest);
        if (restMax.n > opn.n) {
            maxOpn := restMax;
        } else {
            maxOpn := opn;
        }
    }
}

method getMaxOpnWithProposalFromSet(s:set<CPacket>) returns (maxOpn:COperationNumber, foundNonEmpty:bool)
    requires forall p :: p in s ==> p.msg.CMessage_1b? && ValidVotes(p.msg.votes);
    requires |s| > 0;
    ensures forall p :: p in s ==> 
        (forall opn :: opn in p.msg.votes.v ==> opn.n <= maxOpn.n);
    ensures foundNonEmpty <==> exists p :: p in s && |p.msg.votes.v| > 0;
{
    if |s| == 1 
    {
        var p :| p in s;
        assert p.msg.CMessage_1b?;
            
        forall q | q in s 
            ensures q == p;
        {
            ThingsIKnowAboutASingletonSet(s, q, p);
        }
        if (|p.msg.votes.v| > 0) {
            maxOpn := getMaxOpnWithProposalFromSingleton(p.msg.votes.v);
            foundNonEmpty := true;
        } else {
            maxOpn := COperationNumber(0);
            foundNonEmpty := false;
        }
    } else {
        var p :| p in s;
        var rest := s - {p};
        var candidateOpn;
        var foundLocal:bool;
        if (|p.msg.votes.v| > 0) {
            candidateOpn := getMaxOpnWithProposalFromSingleton(p.msg.votes.v);
            foundLocal := true;
            assert forall opn :: opn in p.msg.votes.v ==> opn.n <= candidateOpn.n;
        } else {
            candidateOpn := COperationNumber(0);
            foundLocal := false;
        }
        forall x | x in rest 
            ensures x.msg.CMessage_1b? && ValidVotes(x.msg.votes);
        {
            assert x in s;
            assert forall p :: p in s ==> p.msg.CMessage_1b? && ValidVotes(p.msg.votes);
        }
        
        var restMaxOpn, foundTemp  := getMaxOpnWithProposalFromSet(rest);
        if (foundTemp || foundLocal) {
            foundNonEmpty := true;
        } else {
            foundNonEmpty := false;
        }
        if candidateOpn.n > restMaxOpn.n {
            maxOpn := candidateOpn;
        } else {
            maxOpn := restMaxOpn;
        }
    }
}

method getMaxLogTruncationPoint(s:set<CPacket>) returns (maxLogTruncationPoint:COperationNumber)
    requires forall p :: p in s ==> p.msg.CMessage_1b?;
    requires |s| > 0;
    ensures forall p :: p in s ==> p.msg.log_truncation_point.n <= maxLogTruncationPoint.n;
{
    if |s| == 1 
    {
        var p :| p in s;
        assert p.msg.CMessage_1b?;
            
        forall q | q in s 
            ensures q == p;
        {
            ThingsIKnowAboutASingletonSet(s, q, p);
        }
        maxLogTruncationPoint := p.msg.log_truncation_point;
    } else {
        var p :| p in s;
        var rest := s - {p};
        var candidateOpn := p.msg.log_truncation_point;
        forall x | x in rest 
            ensures x.msg.CMessage_1b?;
        {
            assert x in s;
            assert forall p :: p in s ==> p.msg.CMessage_1b?;
        }

        var restMaxOpn := getMaxLogTruncationPoint(rest);
        if candidateOpn.n > restMaxOpn.n {
            maxLogTruncationPoint := candidateOpn;
        } else {
            maxLogTruncationPoint := restMaxOpn;
        }
    }
}

method {:timeLimitMultiplier 8} ProposerMaybeEnterPhase2(proposer:ProposerState,log_truncation_point:COperationNumber) returns (proposer':ProposerState, sent_packets:CBroadcast)
    requires ProposerIsValid(proposer);
    requires COperationNumberIsAbstractable(log_truncation_point);
    ensures  ProposerIsValid(proposer');
    ensures  CBroadcastIsValid(sent_packets);
    ensures  OutboundPacketsHasCorrectSrc(Broadcast(sent_packets), proposer.constants.all.config.replica_ids[proposer.constants.my_index]);
    ensures  LProposerMaybeEnterPhase2(AbstractifyProposerStateToLProposer(proposer), AbstractifyProposerStateToLProposer(proposer'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCBroadcastToRlsPacketSeq(sent_packets));
    ensures proposer.constants == proposer'.constants;
    ensures proposer'.election_state.cur_req_set  == proposer.election_state.cur_req_set;
    ensures proposer'.election_state.prev_req_set == proposer.election_state.prev_req_set;
{
    var start_time := Time.GetDebugTimeTicks();
    assert SetOfInjectiveTypeCPackets(proposer.received_1b_packets);
    ghost var ref_proposer  := AbstractifyProposerStateToLProposer(proposer);
    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(proposer.received_1b_packets);
    assert |proposer.received_1b_packets| == |AbstractifySetOfCPacketsToSetOfRslPackets(proposer.received_1b_packets)|;
    var quorum_size := MinCQuorumSize(proposer.constants.all.config);
    // The following is already true thanks to our IsValid invariant:
    //    assert LSet(ref_proposer.received_1b_packets, ref_proposer.max_ballot_i_sent_1a);
    lemma_Received1bBound(proposer);
    if uint64(|proposer.received_1b_packets|) >= quorum_size && proposer.current_state == 1 {
        assert |ref_proposer.received_1b_packets| >= LMinQuorumSize(ref_proposer.constants.all.config);
        assert LSetOfMessage1bAboutBallot(ref_proposer.received_1b_packets, ref_proposer.max_ballot_i_sent_1a);
        assert ref_proposer.current_state == 1;

        var maxOpn, foundNonEmpty := getMaxOpnWithProposalFromSet(proposer.received_1b_packets);
        if !foundNonEmpty {
            maxOpn := COperationNumber(0);
        } else if (maxOpn.n < 0xffff_ffff_ffff_ffff) {
            maxOpn := COperationNumber(maxOpn.n + 1);
        }
        
        var maxLogTP := getMaxLogTruncationPoint(proposer.received_1b_packets);
        //print("Proposer starting phase 2 for ballot", proposer.max_ballot_i_sent_1a, ". Setting maxOpnWithProposal to ", maxOpn, " and maxLogTruncationPoint to", maxLogTP, "\n");
        proposer' := proposer[current_state := 2][next_operation_number_to_propose := log_truncation_point.n][maxOpnWithProposal := maxOpn][maxLogTruncationPoint := maxLogTP];
        var msg := CMessage_StartingPhase2(proposer.max_ballot_i_sent_1a, log_truncation_point);
        assert Marshallable(msg);
        sent_packets := BuildBroadcastToEveryone(proposer.constants.all.config, proposer.constants.my_index, msg);
        var end_time := Time.GetDebugTimeTicks();
        RecordTimingSeq("ProposerMaybeEnterPhase2_work", start_time, end_time);
    } else {
        proposer' := proposer;
        sent_packets := CBroadcastNop;
        lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer({});
        var end_time := Time.GetDebugTimeTicks();
        RecordTimingSeq("ProposerMaybeEnterPhase2_nada", start_time, end_time);
    }

    ghost var ref_proposer' := AbstractifyProposerStateToLProposer(proposer');
    ghost var ref_logTruncationPoint := AbstractifyCOperationNumberToOperationNumber(log_truncation_point);
}

predicate Proposer_CanNominateUsingOperationNumber(s:ProposerState, log_truncation_point:COperationNumber, opn:COperationNumber)
    requires ConstantsStateIsAbstractable(s.constants.all);
{
       s.election_state.current_view == s.max_ballot_i_sent_1a
    && s.current_state == 2
    && |s.received_1b_packets| >= LMinQuorumSize(AbstractifyCPaxosConfigurationToConfiguration(s.constants.all.config))
    && SetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a)
    // Don't try to nominate for an operation that's already been truncated into history:
    && IsAfterLogTruncationPoint(opn, s.received_1b_packets)
    // Don't try to nominate in an operation that's too far in the future; that would grow the log too much.
    && int(opn.n) < UpperBoundedAddition(int(log_truncation_point.n), int(s.constants.all.params.max_log_length), UpperBoundFinite(int(s.constants.all.params.max_integer_val)))
    // Disallow negative operations
    && opn.n >= 0
}

lemma lemma_ProposerCanNominateUsingOperationNumberAbstractifies(s:ProposerState, log_truncation_point:COperationNumber, opn:COperationNumber)
    requires ProposerIsValid(s);
    requires COperationNumberIsAbstractable(log_truncation_point);
    requires Proposer_CanNominateUsingOperationNumber(s, log_truncation_point, opn);
    ensures  LProposerCanNominateUsingOperationNumber(AbstractifyProposerStateToLProposer(s),
                                                       AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
                                                       AbstractifyCOperationNumberToOperationNumber(opn));
{
    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(s.received_1b_packets);
    reveal_AbstractifyCVotesToVotes();
}

lemma {:timeLimitMultiplier 4} lemma_NotProposerCanNominateUsingOperationNumberAbstractifies(s:ProposerState, log_truncation_point:COperationNumber, opn:COperationNumber)
    requires ProposerIsValid(s);
    requires COperationNumberIsAbstractable(log_truncation_point);
    requires !Proposer_CanNominateUsingOperationNumber(s, log_truncation_point, opn);
    ensures  !LProposerCanNominateUsingOperationNumber(AbstractifyProposerStateToLProposer(s),
                                                        AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
                                                        AbstractifyCOperationNumberToOperationNumber(opn));
{
    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(s.received_1b_packets);

    if !(s.election_state.current_view == s.max_ballot_i_sent_1a) {
    } else if !(s.current_state == 2) {
    } else if !(|s.received_1b_packets| >= LMinQuorumSize(AbstractifyCPaxosConfigurationToConfiguration(s.constants.all.config))) {
    } else if !(SetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a)) {
    } else if !(IsAfterLogTruncationPoint(opn, s.received_1b_packets)) {
        lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(s.received_1b_packets);
    } else if !(int(opn.n) < UpperBoundedAddition(int(log_truncation_point.n), int(s.constants.all.params.max_log_length), UpperBoundFinite(int(s.constants.all.params.max_integer_val)))) {
        //assume false;
    } else if (!(opn.n >= 0)) {
    } else {
        assert false;
    }
    
}

lemma lemma_AllAcceptorsHadNoProposalAbstractifies(S:set<CPacket>, opn:COperationNumber)
    requires CPacketsIsAbstractable(S);
    requires COperationNumberIsAbstractable(opn);
    requires SetOfMessage1b(S);
    requires AllAcceptorsHadNoProposal(S, opn);
    ensures  LSetOfMessage1b(AbstractifySetOfCPacketsToSetOfRslPackets(S));
    ensures  LAllAcceptorsHadNoProposal(AbstractifySetOfCPacketsToSetOfRslPackets(S),
                                        AbstractifyCOperationNumberToOperationNumber(opn));
{
    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(S);
}

lemma lemma_NotAllAcceptorsHadNoProposalAbstractifies(S:set<CPacket>, opn:COperationNumber)
    requires CPacketsIsAbstractable(S);
    requires SetOfMessage1b(S);
    requires COperationNumberIsAbstractable(opn);
    requires !AllAcceptorsHadNoProposal(S, opn);
    ensures  LSetOfMessage1b(AbstractifySetOfCPacketsToSetOfRslPackets(S));
    ensures  !LAllAcceptorsHadNoProposal(AbstractifySetOfCPacketsToSetOfRslPackets(S),
                                         AbstractifyCOperationNumberToOperationNumber(opn));
{
    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(S);
    reveal_AbstractifySetOfCPacketsToSetOfRslPackets();

    var p :| p in S && opn in p.msg.votes.v;
    assert AbstractifyCPacketToRslPacket(p) in AbstractifySetOfCPacketsToSetOfRslPackets(S);
    //assert !(AbstractifyCOperationNumberToOperationNumber(opn) in AbstractifyCPacketToRslPacket(p).msg.votes);
    reveal_AbstractifyCVotesToVotes();
}

//lemma lemma_SequenceSuffix<T>(s:seq<T>, t:seq<T>, n:int)
//    requires s == t;
method {:timeLimitMultiplier 7} ProposerNominateNewValueAndSend2a(proposer:ProposerState, clock:uint64, log_truncation_point:COperationNumber) returns (proposer':ProposerState, sent_packets:CBroadcast)
    requires ProposerIsValid(proposer);
    requires COperationNumberIsAbstractable(log_truncation_point);
    requires Proposer_CanNominateUsingOperationNumber(proposer, log_truncation_point, COperationNumber(proposer.next_operation_number_to_propose));
    requires AllAcceptorsHadNoProposal(proposer.received_1b_packets, COperationNumber(proposer.next_operation_number_to_propose));
    //requires |proposer.request_queue| > 0;
    ensures  ProposerIsValid(proposer');
    ensures  CBroadcastIsValid(sent_packets);
    ensures  LProposerCanNominateUsingOperationNumber(AbstractifyProposerStateToLProposer(proposer), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), int(proposer.next_operation_number_to_propose));
    ensures  LAllAcceptorsHadNoProposal(AbstractifyProposerStateToLProposer(proposer).received_1b_packets, AbstractifyProposerStateToLProposer(proposer).next_operation_number_to_propose);
    ensures  LProposerNominateNewValueAndSend2a(AbstractifyProposerStateToLProposer(proposer), AbstractifyProposerStateToLProposer(proposer'), int(clock), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCBroadcastToRlsPacketSeq(sent_packets));
    ensures proposer.constants == proposer'.constants;
    ensures  OutboundPacketsHasCorrectSrc(Broadcast(sent_packets), proposer.constants.all.config.replica_ids[proposer.constants.my_index]);
    ensures proposer'.election_state.cur_req_set  == proposer.election_state.cur_req_set;
    ensures proposer'.election_state.prev_req_set == proposer.election_state.prev_req_set;
{
    var batchSize := if |proposer.request_queue| <= int(proposer.constants.all.params.max_batch_size) || proposer.constants.all.params.max_batch_size < 0 then |proposer.request_queue| else int(proposer.constants.all.params.max_batch_size);
    var v := proposer.request_queue[..batchSize];
    var opn := proposer.next_operation_number_to_propose;
    var opn_op := COperationNumber(proposer.next_operation_number_to_propose);
    //var sum := LCappedAdditionImpl(opn, 1, proposer.constants.all.params);
    var clock_sum := UpperBoundedAdditionImpl(clock, proposer.constants.all.params.max_batch_delay, proposer.constants.all.params.max_integer_val);
    var newTimer:CIncompleteBatchTimer := if |proposer.request_queue| > int(batchSize) then CIncompleteBatchTimerOn(clock_sum) else CIncompleteBatchTimerOff();
    //print("Proposer sending 2a about new value in ballot", proposer.max_ballot_i_sent_1a, "operation", opn_op, "value", v, "\n");

    proposer' := proposer[request_queue := proposer.request_queue[batchSize..]]
                         [next_operation_number_to_propose := opn + 1]
                         [incomplete_batch_timer := newTimer];
    var msg := CMessage_2a(proposer.max_ballot_i_sent_1a, opn_op, v);
    assert Marshallable(msg);
    sent_packets := BuildBroadcastToEveryone(proposer.constants.all.config, proposer.constants.my_index, msg);
    
    lemma_ProposerCanNominateUsingOperationNumberAbstractifies(proposer, log_truncation_point, COperationNumber(proposer.next_operation_number_to_propose));
    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(proposer.received_1b_packets);

    ghost var ref_proposer  := AbstractifyProposerStateToLProposer(proposer);
    ghost var ref_proposer' := AbstractifyProposerStateToLProposer(proposer');
    ghost var ref_logTruncationPoint := AbstractifyCOperationNumberToOperationNumber(log_truncation_point);
    ghost var batchSizeGhost := 
        if |ref_proposer.request_queue| <= ref_proposer.constants.all.params.max_batch_size || ref_proposer.constants.all.params.max_batch_size < 0 
        then |ref_proposer.request_queue|
        else ref_proposer.constants.all.params.max_batch_size;
    assert batchSizeGhost == batchSize;
    assert {:split_here} true;
    ghost var vGhost := ref_proposer.request_queue[..batchSizeGhost];
    ghost var opnGhost := ref_proposer.next_operation_number_to_propose;
    ghost var s' := ref_proposer';
    ghost var s := ref_proposer;
    assert vGhost == AbstractifyCRequestBatchToRequestBatch(v);
    assert s'.request_queue == s.request_queue[batchSize..];
    assert s'.next_operation_number_to_propose == s.next_operation_number_to_propose + 1;
    assert s'.incomplete_batch_timer == if |s.request_queue| > batchSize then IncompleteBatchTimerOn(UpperBoundedAddition(int(clock), s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val)) else IncompleteBatchTimerOff();

    assert LBroadcastToEveryone(AbstractifyCPaxosConfigurationToConfiguration(proposer.constants.all.config), int(proposer.constants.my_index), AbstractifyCMessageToRslMessage(msg), AbstractifyCBroadcastToRlsPacketSeq(sent_packets));
    assert AbstractifyCMessageToRslMessage(msg) == RslMessage_2a(AbstractifyProposerStateToLProposer(proposer).max_ballot_i_sent_1a, AbstractifyCOperationNumberToOperationNumber(opn_op), AbstractifyCRequestBatchToRequestBatch(v));
    assert vGhost == AbstractifyCRequestBatchToRequestBatch(v); 
    assert LBroadcastToEveryone(ref_proposer.constants.all.config, 
                                ref_proposer.constants.my_index, 
                                RslMessage_2a(ref_proposer.max_ballot_i_sent_1a, opnGhost, vGhost), 
                                AbstractifyCBroadcastToRlsPacketSeq(sent_packets));
    
    assert {:split_here} true;
    assert 0 <= batchSize <= |proposer.request_queue|;
    lemma_AbstractifyCRequestsSeqToRequestsSeq_suffix(proposer.request_queue, batchSize);
    assert AbstractifyCRequestsSeqToRequestsSeq(proposer.request_queue[batchSize..]) == AbstractifyCRequestsSeqToRequestsSeq(proposer.request_queue)[batchSize..];
    assert AbstractifyCRequestsSeqToRequestsSeq(proposer.request_queue[..batchSize]) == AbstractifyCRequestsSeqToRequestsSeq(proposer.request_queue)[..batchSize];
    
    assert proposer'.request_queue == proposer.request_queue[batchSize..];
    assert ref_proposer'.request_queue == ref_proposer.request_queue[batchSize..];
    assert ref_proposer'.next_operation_number_to_propose == UpperBoundedAddition(ref_proposer.next_operation_number_to_propose, 1, ref_proposer.constants.all.params.max_integer_val);
    assert ref_proposer'.incomplete_batch_timer == AbstractifyCIncompleteBatchTimerToIncompleteBatchTimer(newTimer);
    assert  ProposerIsValid(proposer');
    assert  CBroadcastIsValid(sent_packets);
    assert  LProposerCanNominateUsingOperationNumber(AbstractifyProposerStateToLProposer(proposer), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), int(proposer.next_operation_number_to_propose));
    assert  LAllAcceptorsHadNoProposal(AbstractifyProposerStateToLProposer(proposer).received_1b_packets, AbstractifyProposerStateToLProposer(proposer).next_operation_number_to_propose);
    assert {:split_here} true;
    
    assert  LProposerNominateNewValueAndSend2a(AbstractifyProposerStateToLProposer(proposer), AbstractifyProposerStateToLProposer(proposer'), int(clock), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCBroadcastToRlsPacketSeq(sent_packets));
    assert proposer.constants == proposer'.constants;
    assert  OutboundPacketsHasCorrectSrc(Broadcast(sent_packets), proposer.constants.all.config.replica_ids[proposer.constants.my_index]);
}

predicate ExistsCBallotInS(v:CRequestBatch, c:CBallot, S:set<CPacket>, opn:COperationNumber)
//    requires CRequestIsAbstractable(v) && COperationNumberIsAbstractable(opn) && CBallotIsAbstractable(c);
//    requires CPacketsIsAbstractable(S);
    requires SetOfMessage1b(S);
{
    exists p :: p in S
        && opn in p.msg.votes.v
        && p.msg.votes.v[opn].max_value_bal==c
        && p.msg.votes.v[opn].max_val==v
}

predicate CValIsHighestNumberedProposalAtBallot(v:CRequestBatch, c:CBallot, S:set<CPacket>, opn:COperationNumber)
    requires CBallotIsAbstractable(c) && CPacketsIsAbstractable(S) && COperationNumberIsAbstractable(opn);
    requires SetOfMessage1b(S);
{
    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(S);
    LMaxBallotInS(AbstractifyCBallotToBallot(c), AbstractifySetOfCPacketsToSetOfRslPackets(S), AbstractifyCOperationNumberToOperationNumber(opn))
    && ExistsCBallotInS(v, c, S, opn)
}

predicate CValIsHighestNumberedProposal(v:CRequestBatch, S:set<CPacket>, opn:COperationNumber)
    requires CRequestBatchIsAbstractable(v) && COperationNumberIsAbstractable(opn);
    requires CPacketsIsAbstractable(S);
    requires SetOfMessage1b(S);
{
    exists c :: CBallotIsAbstractable(c) && CValIsHighestNumberedProposalAtBallot(v, c, S, opn)
}

lemma {:timeLimitMultiplier 3} lemma_CValIsHighestNumberedProposalAbstractifies(v:CRequestBatch, bal:CBallot, S:set<CPacket>, opn:COperationNumber)
    requires CRequestBatchIsAbstractable(v) && CBallotIsAbstractable(bal) && CPacketsIsAbstractable(S) && COperationNumberIsAbstractable(opn);
    requires SetOfMessage1b(S);
    requires CValIsHighestNumberedProposal(v, S, opn);
    requires CValIsHighestNumberedProposalAtBallot(v, bal, S, opn);
    ensures LSetOfMessage1b(AbstractifySetOfCPacketsToSetOfRslPackets(S));
    ensures LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(v), AbstractifySetOfCPacketsToSetOfRslPackets(S), AbstractifyCOperationNumberToOperationNumber(opn));
    ensures LValIsHighestNumberedProposalAtBallot(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(bal), AbstractifySetOfCPacketsToSetOfRslPackets(S), AbstractifyCOperationNumberToOperationNumber(opn));
{
    reveal_AbstractifyCVotesToVotes();
    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(S);

    var c :| CBallotIsAbstractable(c) && CValIsHighestNumberedProposalAtBallot(v, c, S, opn);
    var ref_c := AbstractifyCBallotToBallot(c);
    var ref_v := AbstractifyCRequestBatchToRequestBatch(v);
    var ref_S := AbstractifySetOfCPacketsToSetOfRslPackets(S);
    var ref_opn := AbstractifyCOperationNumberToOperationNumber(opn);
    assert LMaxBallotInS(ref_c, ref_S, ref_opn);
    assert ExistsCBallotInS(v, c, S, opn);
    var p :| p in S && opn in p.msg.votes.v
        && p.msg.votes.v[opn].max_value_bal==c
        && p.msg.votes.v[opn].max_val==v;
    var ref_p := AbstractifyCPacketToRslPacket(p);

    calc ==> {
        true;
        { reveal_AbstractifySetOfCPacketsToSetOfRslPackets(); }
        ref_p in ref_S;
    }
    assert ref_opn in ref_p.msg.votes;
    assert ref_p.msg.votes[ref_opn].max_value_bal == ref_c;
    assert ref_p.msg.votes[ref_opn].max_val == ref_v;

    assert LExistsBallotInS(ref_v, ref_c, ref_S, ref_opn);
    assert LValIsHighestNumberedProposalAtBallot(ref_v, ref_c, ref_S, ref_opn);
    assert LValIsHighestNumberedProposal(ref_v, ref_S, ref_opn);

    var ref_bal := AbstractifyCBallotToBallot(bal);
    assert ExistsCBallotInS(v, bal, S, opn);

    var p' :| p' in S && opn in p'.msg.votes.v
        && p'.msg.votes.v[opn].max_value_bal==bal
        && p'.msg.votes.v[opn].max_val==v;
    var ref_p' := AbstractifyCPacketToRslPacket(p');

    calc ==> {
        true;
        { reveal_AbstractifySetOfCPacketsToSetOfRslPackets(); }
        ref_p' in ref_S;
    }
    assert ref_opn in ref_p'.msg.votes;
    assert ref_p'.msg.votes[ref_opn].max_value_bal == ref_bal;
    assert ref_p'.msg.votes[ref_opn].max_val == ref_v;
    assert LExistsBallotInS(ref_v, ref_bal, ref_S, ref_opn);

    assert LValIsHighestNumberedProposalAtBallot(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(bal), AbstractifySetOfCPacketsToSetOfRslPackets(S), AbstractifyCOperationNumberToOperationNumber(opn));
}


method {:timeLimitMultiplier 5} FindValWithHighestNumberedProposal(received_1b_packets:set<CPacket>, opn:COperationNumber) returns (v:CRequestBatch)
    requires received_1b_packets != {};
    requires COperationNumberIsAbstractable(opn);
    requires SetOfMessage1b(received_1b_packets);
    requires CPacketsIsAbstractable(received_1b_packets);
    requires !AllAcceptorsHadNoProposal(received_1b_packets, opn);
    requires forall p :: p in received_1b_packets ==> ValidVotes(p.msg.votes);
    ensures CRequestBatchIsAbstractable(v);
    ensures ValidRequestBatch(v);
    ensures LSetOfMessage1b(AbstractifySetOfCPacketsToSetOfRslPackets(received_1b_packets));
    ensures LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(v), AbstractifySetOfCPacketsToSetOfRslPackets(received_1b_packets), AbstractifyCOperationNumberToOperationNumber(opn));
{
    var packets:set<CPacket>;
    ghost var processedPackets:set<CPacket>;

    packets := received_1b_packets;
    var pkt :| pkt in packets && opn in pkt.msg.votes.v;
    v := pkt.msg.votes.v[opn].max_val;
    var bal := pkt.msg.votes.v[opn].max_value_bal;
    var p_bal := pkt;
    packets := packets - {pkt};
    processedPackets := {pkt};
    reveal_AbstractifySetOfCPacketsToSetOfRslPackets();
    reveal_AbstractifyCVotesToVotes();
    ghost var p := AbstractifyCPacketToRslPacket(pkt);
    ghost var S := AbstractifySetOfCPacketsToSetOfRslPackets(processedPackets);
    ghost var opn_s := AbstractifyCOperationNumberToOperationNumber(opn);

    while (packets != {})
        decreases packets;
        invariant packets + processedPackets == received_1b_packets;
        invariant processedPackets == received_1b_packets - packets;
        invariant CRequestBatchIsAbstractable(v) && CBallotIsAbstractable(bal) && CPacketIsAbstractable(p_bal) && p_bal in processedPackets && opn in p_bal.msg.votes.v && v == p_bal.msg.votes.v[opn].max_val && bal == p_bal.msg.votes.v[opn].max_value_bal;
        invariant forall p :: p in processedPackets && opn in p.msg.votes.v ==> CCBalLeq(p.msg.votes.v[opn].max_value_bal, p_bal.msg.votes.v[opn].max_value_bal);
        invariant p_bal in processedPackets
                && opn in p_bal.msg.votes.v
                && p_bal.msg.votes.v[opn].max_value_bal==bal
                && p_bal.msg.votes.v[opn].max_val==v;
        invariant ExistsCBallotInS(v, bal, processedPackets, opn)
        invariant CValIsHighestNumberedProposalAtBallot(v, bal, processedPackets, opn);
        invariant CValIsHighestNumberedProposal(v, processedPackets, opn);
        invariant ValidRequestBatch(v);
    {
        pkt :| pkt in packets;
        if (opn in pkt.msg.votes.v) {
            var foundHigherBallot := CBalLeq(bal, pkt.msg.votes.v[opn].max_value_bal);

            if (foundHigherBallot) {
                p_bal := pkt;
                v := pkt.msg.votes.v[opn].max_val;
                bal := pkt.msg.votes.v[opn].max_value_bal;
            }
        }
        packets := packets - {pkt};
        processedPackets := processedPackets + {pkt};
        reveal_AbstractifyCVotesToVotes();
    }

    assert processedPackets == received_1b_packets;
    p := AbstractifyCPacketToRslPacket(p_bal);
    assert CValIsHighestNumberedProposal(v, received_1b_packets, opn);
    lemma_CValIsHighestNumberedProposalAbstractifies(v, bal, received_1b_packets, opn);
    assert LValIsHighestNumberedProposalAtBallot(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(bal), AbstractifySetOfCPacketsToSetOfRslPackets(received_1b_packets), AbstractifyCOperationNumberToOperationNumber(opn));
}


method ProposerNominateOldValueAndSend2a(proposer:ProposerState,log_truncation_point:COperationNumber) returns (proposer':ProposerState, sent_packets:CBroadcast)
    requires ProposerIsValid(proposer);
    requires COperationNumberIsAbstractable(log_truncation_point);
    requires Proposer_CanNominateUsingOperationNumber(proposer, log_truncation_point, COperationNumber(proposer.next_operation_number_to_propose));
    requires !AllAcceptorsHadNoProposal(proposer.received_1b_packets, COperationNumber(proposer.next_operation_number_to_propose));
    ensures  ProposerIsValid(proposer');
    ensures  CBroadcastIsValid(sent_packets);
    ensures  LProposerCanNominateUsingOperationNumber(AbstractifyProposerStateToLProposer(proposer), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), int(proposer.next_operation_number_to_propose));
    ensures  LSetOfMessage1b(AbstractifySetOfCPacketsToSetOfRslPackets(proposer.received_1b_packets));
    ensures  !LAllAcceptorsHadNoProposal(AbstractifyProposerStateToLProposer(proposer).received_1b_packets, AbstractifyProposerStateToLProposer(proposer).next_operation_number_to_propose);
    ensures  LProposerNominateOldValueAndSend2a(AbstractifyProposerStateToLProposer(proposer), AbstractifyProposerStateToLProposer(proposer'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCBroadcastToRlsPacketSeq(sent_packets));
    ensures proposer.constants == proposer'.constants;
    ensures  OutboundPacketsHasCorrectSrc(Broadcast(sent_packets), proposer.constants.all.config.replica_ids[proposer.constants.my_index]);
    ensures proposer'.election_state.cur_req_set  == proposer.election_state.cur_req_set;
    ensures proposer'.election_state.prev_req_set == proposer.election_state.prev_req_set;
{
    ghost var r_proposer := AbstractifyProposerStateToLProposer(proposer);
    var opn := proposer.next_operation_number_to_propose;
    var opn_op := COperationNumber(proposer.next_operation_number_to_propose);
    var val := FindValWithHighestNumberedProposal(proposer.received_1b_packets, opn_op);
    assert LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(val), AbstractifySetOfCPacketsToSetOfRslPackets(proposer.received_1b_packets), AbstractifyCOperationNumberToOperationNumber(opn_op));
    var sum := opn + 1;
    //print("Proposer sending 2a about old value in ballot", proposer.max_ballot_i_sent_1a, "operation", opn_op, "value", val, "\n");
    
    proposer' := proposer[next_operation_number_to_propose := sum];

    // Update the protocol version too
    ghost var L_opn := r_proposer.next_operation_number_to_propose;
    ghost var r_proposer' := r_proposer
        [next_operation_number_to_propose := UpperBoundedAddition(r_proposer.next_operation_number_to_propose, 1, r_proposer.constants.all.params.max_integer_val)];

    var msg := CMessage_2a(proposer.max_ballot_i_sent_1a, opn_op, val);
    assert Marshallable(msg);
    sent_packets := BuildBroadcastToEveryone(proposer.constants.all.config, proposer.constants.my_index, msg);

    lemma_ProposerCanNominateUsingOperationNumberAbstractifies(proposer, log_truncation_point, COperationNumber(proposer.next_operation_number_to_propose));
    lemma_NotAllAcceptorsHadNoProposalAbstractifies(proposer.received_1b_packets, opn_op);
    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(proposer.received_1b_packets);
    reveal_AbstractifyCVotesToVotes();

    assert Eq_LProposer(r_proposer', AbstractifyProposerStateToLProposer(proposer'));
}


/*method ProposerNominateNoOpValueAndSend2a(proposer:ProposerState,log_truncation_point:COperationNumber) returns (proposer':ProposerState, sent_packets:CBroadcast)
    requires ProposerIsValid(proposer);
    requires COperationNumberIsAbstractable(log_truncation_point);
    requires Proposer_CanNominateUsingOperationNumber(proposer, log_truncation_point, COperationNumber(proposer.next_operation_number_to_propose));
    requires AllAcceptorsHadNoProposal(proposer.received_1b_packets, COperationNumber(proposer.next_operation_number_to_propose));
    requires exists opn:COperationNumber :: opn.n > proposer.next_operation_number_to_propose && !AllAcceptorsHadNoProposal(proposer.received_1b_packets, opn);
    ensures  ProposerIsValid(proposer');
    ensures  CBroadcastIsValid(sent_packets);
    ensures  LProposerCanNominateUsingOperationNumber(AbstractifyProposerStateToLProposer(proposer), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), int(proposer.next_operation_number_to_propose));
    ensures  LSetOfMessage1b(AbstractifyProposerStateToLProposer(proposer).received_1b_packets);
    ensures  LAllAcceptorsHadNoProposal(AbstractifyProposerStateToLProposer(proposer).received_1b_packets, AbstractifyProposerStateToLProposer(proposer).next_operation_number_to_propose);
    ensures  exists l_opn :: l_opn > AbstractifyProposerStateToLProposer(proposer).next_operation_number_to_propose &&
                             !LAllAcceptorsHadNoProposal(AbstractifyProposerStateToLProposer(proposer).received_1b_packets, l_opn);
    ensures  LProposerNominateNewValueAndSend2a(AbstractifyProposerStateToLProposer(proposer), AbstractifyProposerStateToLProposer(proposer'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCBroadcastToRlsPacketSeq(sent_packets));
    ensures proposer.constants == proposer'.constants;
    ensures  OutboundPacketsHasCorrectSrc(Broadcast(sent_packets), proposer.constants.all.config.replica_ids[proposer.constants.my_index]);
{

    var v := [];
    var opn := proposer.next_operation_number_to_propose;
    var opn_op := COperationNumber(proposer.next_operation_number_to_propose);
    var sum := LCappedAdditionImpl(opn, 1, proposer.constants.all.params);
    ghost var ref_op := AbstractifyCOperationNumberToOperationNumber(opn_op);
    ghost var ref_v := AbstractifyCRequestBatchToRequestBatch(v);

    //print("Proposer sending 2a about no-op in ballot", proposer.max_ballot_i_sent_1a, "operation", opn_op, "value", v, "\n");

    proposer' := proposer[next_operation_number_to_propose := sum];
    var msg := CMessage_2a(proposer.max_ballot_i_sent_1a, opn_op, v);
    sent_packets := BuildBroadcastToEveryone(proposer.constants.all.config, proposer.constants.my_index, msg);

    ghost var ref_proposer  := AbstractifyProposerStateToLProposer(proposer);

    lemma_ProposerCanNominateUsingOperationNumberAbstractifies(proposer, log_truncation_point, COperationNumber(proposer.next_operation_number_to_propose));
    lemma_AllAcceptorsHadNoProposalAbstractifies(proposer.received_1b_packets, opn_op);

    ghost var e_opn:COperationNumber :| e_opn.n > proposer.next_operation_number_to_propose && !AllAcceptorsHadNoProposal(proposer.received_1b_packets, e_opn);
    ghost var ref_e_opn := AbstractifyCOperationNumberToOperationNumber(e_opn);

    lemma_NotAllAcceptorsHadNoProposalAbstractifies(proposer.received_1b_packets, e_opn);
    assert ref_e_opn > ref_proposer.next_operation_number_to_propose && !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, ref_e_opn);
    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(proposer.received_1b_packets);
    reveal_AbstractifyCVotesToVotes();

    ghost var ref_proposer' := AbstractifyProposerStateToLProposer(proposer');
    ghost var ref_logTruncationPoint := AbstractifyCOperationNumberToOperationNumber(log_truncation_point);

    assert ref_proposer'.next_operation_number_to_propose == LCappedAddition(ref_proposer.next_operation_number_to_propose, 1, ref_proposer.constants.all.params);
}*/

method IsAfterLogTruncationPointImpl(opn:COperationNumber, received_1b_packets:set<CPacket>) returns (b:bool)
    requires COperationNumberIsAbstractable(opn) && CPacketsIsAbstractable(received_1b_packets);
    ensures  b == IsAfterLogTruncationPoint(opn, received_1b_packets);
    ensures  b == LIsAfterLogTruncationPoint(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifySetOfCPacketsToSetOfRslPackets(received_1b_packets));
{
    reveal_AbstractifySetOfCPacketsToSetOfRslPackets();
    lemma_AbstractifyCPacketToRslPacket_isInjective();
    assert forall p :: CPacketIsAbstractable(p) && AbstractifyCPacketToRslPacket(p).msg.RslMessage_1b? ==> CPacketIsInjectiveType(p);
    
    b := (forall p :: p in received_1b_packets && p.msg.CMessage_1b? ==> p.msg.log_truncation_point.n <= opn.n);
}

method Proposer_CanNominateUsingOperationNumberImpl(proposer:ProposerState,log_truncation_point:COperationNumber) returns (b:bool)
    requires ProposerIsValid(proposer);
    requires COperationNumberIsAbstractable(log_truncation_point);
    ensures  b == Proposer_CanNominateUsingOperationNumber(proposer, log_truncation_point,
                                                           COperationNumber(proposer.next_operation_number_to_propose));
    ensures  b == LProposerCanNominateUsingOperationNumber(AbstractifyProposerStateToLProposer(proposer),
                                                            AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
                                                            AbstractifyProposerStateToLProposer(proposer).next_operation_number_to_propose);
{
    if (proposer.current_state == 2) {
        var opn := COperationNumber(proposer.next_operation_number_to_propose);
        var quorum_size := MinCQuorumSize(proposer.constants.all.config);

        var after_trunk;
        if (opn.n >= proposer.maxLogTruncationPoint.n) {
            after_trunk := true;
        } else { 
            after_trunk := IsAfterLogTruncationPointImpl(opn, proposer.received_1b_packets);
        }
        var sum := UpperBoundedAdditionImpl(log_truncation_point.n, proposer.constants.all.params.max_log_length, proposer.constants.all.params.max_integer_val);
        assert SetOfMessage1bAboutBallot(proposer.received_1b_packets, proposer.max_ballot_i_sent_1a);
        lemma_Received1bBound(proposer);

        b :=    proposer.election_state.current_view == proposer.max_ballot_i_sent_1a
             && proposer.current_state == 2
             && uint64(|proposer.received_1b_packets|) >= quorum_size
             // Should come for free from ProposerIsValid
             //&& SetOfMessage1bAboutBallot(proposer.received_1b_packets, proposer.max_ballot_i_sent_1a)
             && after_trunk
             && opn.n < sum
             && opn.n >=0;

        assert b == Proposer_CanNominateUsingOperationNumber(proposer, log_truncation_point,
                                                             COperationNumber(proposer.next_operation_number_to_propose));
        if b {
            lemma_ProposerCanNominateUsingOperationNumberAbstractifies(proposer, log_truncation_point, COperationNumber(proposer.next_operation_number_to_propose));
        } else {
            lemma_NotProposerCanNominateUsingOperationNumberAbstractifies(proposer, log_truncation_point, COperationNumber(proposer.next_operation_number_to_propose));
        }
    } else {
        b := false;
    }
}

method {:timeLimitMultiplier 6} AllAcceptorsHadNoProposalImpl(proposer:ProposerState) returns (b:bool)
    requires ProposerIsValid(proposer);
    requires proposer.current_state == 2;
    ensures  LSetOfMessage1b(AbstractifyProposerStateToLProposer(proposer).received_1b_packets);
    ensures  b == AllAcceptorsHadNoProposal(proposer.received_1b_packets,
                                            COperationNumber(proposer.next_operation_number_to_propose));
    ensures  b == LAllAcceptorsHadNoProposal(AbstractifyProposerStateToLProposer(proposer).received_1b_packets,
                                             AbstractifyProposerStateToLProposer(proposer).next_operation_number_to_propose);
{
    reveal_AbstractifySetOfCPacketsToSetOfRslPackets();
    reveal_AbstractifyCVotesToVotes();
    lemma_AbstractifyCPacketToRslPacket_isInjective();
    lemma_AbstractifyCOperationNumberToOperationNumber_isInjective();
    assert forall p :: p in proposer.received_1b_packets ==> CPacketIsInjectiveType(p);

    var start_time := Time.GetDebugTimeTicks();
    
    var end_time; 
    
    if(proposer.next_operation_number_to_propose < proposer.maxOpnWithProposal.n || proposer.maxOpnWithProposal.n == 0xffff_ffff_ffff_ffff) {
        var opn := COperationNumber(proposer.next_operation_number_to_propose);
        b := (forall p :: p in proposer.received_1b_packets ==> !(opn in p.msg.votes.v));
        end_time := Time.GetDebugTimeTicks();
        RecordTimingSeq("AllAcceptorsHadNoProposalImpl_full", start_time, end_time);
        //print("AllAcceptorsHadNoProposalImpl_full: Doing full search, nextOpnToPropose = ", proposer.next_operation_number_to_propose, " and maxOpnWithProposal = ", proposer.maxOpnWithProposal.n, "\n"); 
    } else {
        b := true;
        end_time := Time.GetDebugTimeTicks();
        RecordTimingSeq("AllAcceptorsHadNoProposalImpl_memoized", start_time, end_time);
        //print("AllAcceptorsHadNoProposalImpl_memoized: Memoized, nextOpnToPropose = ", proposer.next_operation_number_to_propose, " and maxOpnWithProposal = ", proposer.maxOpnWithProposal.n, "\n"); 
    }
    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(proposer.received_1b_packets);
}

lemma {:timeLimitMultiplier 6} lemma_AllAcceptorsHadNoProposalImpl(proposer:ProposerState)
    requires ProposerIsValid(proposer);
    requires proposer.current_state == 2;
    requires proposer.maxOpnWithProposal.n < 0xffff_ffff_ffff_ffff;
    ensures  LSetOfMessage1b(AbstractifyProposerStateToLProposer(proposer).received_1b_packets);
    requires proposer.next_operation_number_to_propose >= proposer.maxOpnWithProposal.n;
    ensures  AllAcceptorsHadNoProposal(proposer.received_1b_packets,
                                            COperationNumber(proposer.next_operation_number_to_propose));
    ensures  LAllAcceptorsHadNoProposal(AbstractifyProposerStateToLProposer(proposer).received_1b_packets,
                                             AbstractifyProposerStateToLProposer(proposer).next_operation_number_to_propose);
{
    reveal_AbstractifySetOfCPacketsToSetOfRslPackets();
    reveal_AbstractifyCVotesToVotes();
    lemma_AbstractifyCPacketToRslPacket_isInjective();
    lemma_AbstractifyCOperationNumberToOperationNumber_isInjective();
    assert forall p :: p in proposer.received_1b_packets ==> CPacketIsInjectiveType(p);
    
    
    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(proposer.received_1b_packets);
}

predicate ExistsPred(proposer:ProposerState, ref_proposer:LProposer, existsOpn:bool)
    requires LSetOfMessage1b(ref_proposer.received_1b_packets);
    requires ProposerIsValid(proposer);
{
    existsOpn <==> var ref_proposer := AbstractifyProposerStateToLProposer(proposer);
                   (exists opn :: opn > ref_proposer.next_operation_number_to_propose 
                               && LSetOfMessage1b(ref_proposer.received_1b_packets)
                               && !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn))
}

predicate AnAcceptorHadProposal(ref_proposer:LProposer, opn:OperationNumber)
    requires LSetOfMessage1b(ref_proposer.received_1b_packets);
{
    opn > ref_proposer.next_operation_number_to_propose &&
                                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn)
}

method DidSomeAcceptorHaveProposal(proposer:ProposerState) returns (b:bool) //, opn:COperationNumber)
    requires ProposerIsValid(proposer);
    requires proposer.current_state == 2;
    ensures  LSetOfMessage1b(AbstractifyProposerStateToLProposer(proposer).received_1b_packets);
    ensures b <==> (exists opn:COperationNumber ::
                                   opn.n > proposer.next_operation_number_to_propose &&
                                   !AllAcceptorsHadNoProposal(proposer.received_1b_packets, opn));
    ensures b == var ref_proposer := AbstractifyProposerStateToLProposer(proposer);
                   (exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));
{
    reveal_AbstractifyCVotesToVotes();
    lemma_AbstractifyCPacketToRslPacket_isInjective();
    lemma_AbstractifyCOperationNumberToOperationNumber_isInjective();
    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(proposer.received_1b_packets);
    assert forall p :: p in proposer.received_1b_packets ==> CPacketIsInjectiveType(p);

    if proposer.next_operation_number_to_propose >= proposer.maxOpnWithProposal.n {
        b := false;
    } else {
        b :=
            (exists p :: p in proposer.received_1b_packets &&
                (exists opn:COperationNumber :: opn in p.msg.votes.v && opn.n > proposer.next_operation_number_to_propose));
    }
    // The "exists opn" needs a trigger that relates to "opn.n > ...":
    ghost var gt := (i:int, j:int) => i > j;
    assert b <==>
        (exists p :: p in proposer.received_1b_packets &&
            (exists opn:COperationNumber :: opn in p.msg.votes.v && gt(AbstractifyCOperationNumberToOperationNumber(opn), int(proposer.next_operation_number_to_propose))));

    ghost var ref_proposer := AbstractifyProposerStateToLProposer(proposer);
    if ((exists opn :: gt(opn, ref_proposer.next_operation_number_to_propose) &&
                                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn))) {
        var ref_opn :| gt(ref_opn, ref_proposer.next_operation_number_to_propose) &&
                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, ref_opn);
        var ref_p :| ref_p in ref_proposer.received_1b_packets && ref_opn in ref_p.msg.votes;

        calc ==> {
            true;
                { reveal_AbstractifySetOfCPacketsToSetOfRslPackets(); }
            exists p :: p in proposer.received_1b_packets && ref_p == AbstractifyCPacketToRslPacket(p);
        }

        var p :| p in proposer.received_1b_packets && ref_p == AbstractifyCPacketToRslPacket(p);

        //assert exists o :: o in p.msg.votes.v && AbstractifyCOperationNumberToOperationNumber(o) == ref_opn;

        assert b;
    }

    assert b <==>
        (var ref_proposer := AbstractifyProposerStateToLProposer(proposer);
            (exists opn :: gt(opn, ref_proposer.next_operation_number_to_propose) && !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn)));
}

lemma lemma_DidSomeAcceptorHaveProposal(proposer:ProposerState) //, opn:COperationNumber)
    requires ProposerIsValid(proposer);
    requires proposer.current_state == 2;
    requires proposer.next_operation_number_to_propose >= proposer.maxOpnWithProposal.n;
    ensures  LSetOfMessage1b(AbstractifyProposerStateToLProposer(proposer).received_1b_packets);
    ensures !(exists opn:COperationNumber ::
                                   opn.n > proposer.next_operation_number_to_propose &&
                                   !AllAcceptorsHadNoProposal(proposer.received_1b_packets, opn));
    ensures !var ref_proposer := AbstractifyProposerStateToLProposer(proposer);
                   (exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));
{
    reveal_AbstractifyCVotesToVotes();
    lemma_AbstractifyCPacketToRslPacket_isInjective();
    lemma_AbstractifyCOperationNumberToOperationNumber_isInjective();
    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(proposer.received_1b_packets);
    assert forall p :: p in proposer.received_1b_packets ==> CPacketIsInjectiveType(p);

    var b := false;
    
    // The "exists opn" needs a trigger that relates to "opn.n > ...":
    ghost var gt := (i:int, j:int) => i > j;
    assert b <==>
        (exists p :: p in proposer.received_1b_packets &&
            (exists opn:COperationNumber :: opn in p.msg.votes.v && gt(AbstractifyCOperationNumberToOperationNumber(opn), int(proposer.next_operation_number_to_propose))));

    ghost var ref_proposer := AbstractifyProposerStateToLProposer(proposer);
    if ((exists opn :: gt(opn, ref_proposer.next_operation_number_to_propose) &&
                                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn))) {
        var ref_opn :| gt(ref_opn, ref_proposer.next_operation_number_to_propose) &&
                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, ref_opn);
        var ref_p :| ref_p in ref_proposer.received_1b_packets && ref_opn in ref_p.msg.votes;

        calc ==> {
            true;
                { reveal_AbstractifySetOfCPacketsToSetOfRslPackets(); }
            exists p :: p in proposer.received_1b_packets && ref_p == AbstractifyCPacketToRslPacket(p);
        }

        var p :| p in proposer.received_1b_packets && ref_p == AbstractifyCPacketToRslPacket(p);

        //assert exists o :: o in p.msg.votes.v && AbstractifyCOperationNumberToOperationNumber(o) == ref_opn;

        assert b;
    }

    assert b <==>
        (var ref_proposer := AbstractifyProposerStateToLProposer(proposer);
            (exists opn :: gt(opn, ref_proposer.next_operation_number_to_propose) && !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn)));
}

method {:timeLimitMultiplier 12} ProposerMaybeNominateValueAndSend2a(proposer:ProposerState, clock:uint64, log_truncation_point:COperationNumber) returns (proposer':ProposerState, sent_packets:CBroadcast)
    requires ProposerIsValid(proposer);
    requires COperationNumberIsAbstractable(log_truncation_point);
    ensures  ProposerIsValid(proposer');
    ensures  CBroadcastIsValid(sent_packets);
    ensures  OutboundPacketsHasCorrectSrc(Broadcast(sent_packets), proposer.constants.all.config.replica_ids[proposer.constants.my_index]);
    ensures  LProposerMaybeNominateValueAndSend2a(AbstractifyProposerStateToLProposer(proposer), AbstractifyProposerStateToLProposer(proposer'), int(clock), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCBroadcastToRlsPacketSeq(sent_packets));
    ensures proposer.constants == proposer'.constants;
    ensures proposer'.election_state.cur_req_set == proposer.election_state.cur_req_set;
    ensures proposer'.election_state.prev_req_set == proposer.election_state.prev_req_set;
{
    //var start_time := Time.GetDebugTimeTicks();
    var canNominate := Proposer_CanNominateUsingOperationNumberImpl(proposer, log_truncation_point);
    //var end_time:= Time.GetDebugTimeTicks();
    //RecordTimingSeq("ProposerMaybeNominateValueAndSend2a_preamble_Proposer_CanNominateUsingOperationNumberImpl", start_time, end_time);
    /*
    //start_time := Time.GetDebugTimeTicks();
    
    end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("ProposerMaybeNominateValueAndSend2a_preamble_AllAcceptorsHadNoProposalImpl", start_time, end_time);

    //start_time := Time.GetDebugTimeTicks();
    
    end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("ProposerMaybeNominateValueAndSend2a_preamble", start_time, end_time);*/
    //print("ProposerMaybeNominateValueAndSend2a: proposer.next_operation_number_to_propose = ", proposer.next_operation_number_to_propose, ", canNominate = ", canNominate, "\n");
    
    if !canNominate {
        proposer' := proposer;
        sent_packets := CBroadcastNop;
        //lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(sent_packets);
        //var end_timeNotCanNominate:= Time.GetDebugTimeTicks();
        //RecordTimingSeq("ProposerMaybeNominateValueAndSend2a_unable", start_time, end_timeNotCanNominate);
    } else {
        if (proposer.next_operation_number_to_propose >= proposer.maxOpnWithProposal.n && |proposer.request_queue| == 0 && proposer.maxOpnWithProposal.n < 0xffff_ffff_ffff_ffff) {
            lemma_DidSomeAcceptorHaveProposal(proposer);
            lemma_AllAcceptorsHadNoProposalImpl(proposer);
            
            //start_time := Time.GetDebugTimeTicks();
            proposer' := proposer;
            sent_packets := CBroadcastNop;
            //lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(sent_packets);
            //var end_time4 := Time.GetDebugTimeTicks();
            //RecordTimingSeq("ProposerMaybeNominateValueAndSend2a_nada", start_time, end_time4);
            //print("ProposerMaybeNominateValueAndSend2a: proposer.next_operation_number_to_propose = ", proposer.next_operation_number_to_propose, ". NADA\n");
        } else {
            var noProposal := AllAcceptorsHadNoProposalImpl(proposer);
            //var end_time2 := Time.GetDebugTimeTicks();
            //RecordTimingSeq("ProposerMaybeNominateValueAndSend2a_AllAcceptorsHadNoProposalImpl", start_time, end_time2);
            //print("ProposerMaybeNominateValueAndSend2a: proposer.next_operation_number_to_propose = ", proposer.next_operation_number_to_propose, ", AllAcceptorsHadNoProposalImpl = ", noProposal, "\n");
            if !noProposal {
                proposer', sent_packets := ProposerNominateOldValueAndSend2a(proposer, log_truncation_point);
                assert OutboundPacketsHasCorrectSrc(Broadcast(sent_packets), proposer.constants.all.config.replica_ids[proposer.constants.my_index]); //OBSERVE
                //var end_timeNotNoProposal := Time.GetDebugTimeTicks();
                //RecordTimingSeq("ProposerMaybeNominateValueAndSend2a_old", end_time2, end_timeNotNoProposal);
                //print("ProposerMaybeNominateValueAndSend2a: Nominating old value at proposer.next_operation_number_to_propose = ", proposer.next_operation_number_to_propose, "\n");
            } else {
                var queueSize := |proposer.request_queue|;
                var existsOpn := DidSomeAcceptorHaveProposal(proposer);
                ghost var ref_proposer := AbstractifyProposerStateToLProposer(proposer);
                assert existsOpn ==> (exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));
                assert ExistsPred(proposer, ref_proposer, existsOpn);
                //var end_time3 := Time.GetDebugTimeTicks();
                //var ref_proposer := AbstractifyProposerStateToLProposer(proposer);
                //   (exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                //                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));
                if existsOpn {
                    assert ExistsPred(proposer, ref_proposer, existsOpn);
                    assert existsOpn ==> (exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));
                    assert exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn);
                    //ghost var opn :| opn > ref_proposer.next_operation_number_to_propose &&
                    //               !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn);
                } else {
                    assert ghost var ref_proposer := AbstractifyProposerStateToLProposer(proposer); forall opn :: !(opn > ref_proposer.next_operation_number_to_propose &&
                                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));
                }
                //assert existsOpn <==> var ref_proposer := AbstractifyProposerStateToLProposer(proposer);(exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                //                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));

                 //                  ;var ref_proposer := AbstractifyProposerStateToLProposer(proposer);
                 //  (exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                 //                  !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));

                if (   (queueSize > 0 && proposer.incomplete_batch_timer.CIncompleteBatchTimerOn? && clock >= proposer.incomplete_batch_timer.when)
                    || (queueSize >= int(proposer.constants.all.params.max_batch_size))
                    || existsOpn 
                    ) {
                    if existsOpn {
                        assert ExistsPred(proposer, ref_proposer, existsOpn);
                        assert existsOpn ==> (exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                                       !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));
                        assert exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                                       !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn);
                        //ghost var opn :| opn > ref_proposer.next_operation_number_to_propose &&
                        //               !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn);
                    } else if (queueSize >= int(proposer.constants.all.params.max_batch_size)) {
                        assert |ref_proposer.request_queue| >= ref_proposer.constants.all.params.max_batch_size;
                    } else if (queueSize > 0 && proposer.incomplete_batch_timer.CIncompleteBatchTimerOn? && clock >= proposer.incomplete_batch_timer.when) {
                        assert (|ref_proposer.request_queue| > 0 && ref_proposer.incomplete_batch_timer.IncompleteBatchTimerOn? && int(clock) >= ref_proposer.incomplete_batch_timer.when);
                    }
                    //assume false;
                    //assert existsOpn <==> 
                    //    (exists opn:OperationNumber :: 
                    //        (opn > AbstractifyProposerStateToLProposer(proposer).next_operation_number_to_propose 
                    //     && !LAllAcceptorsHadNoProposal(AbstractifyProposerStateToLProposer(proposer).received_1b_packets, opn))
                    //     );
                    proposer', sent_packets := ProposerNominateNewValueAndSend2a(proposer, clock, log_truncation_point);
                    assert OutboundPacketsHasCorrectSrc(Broadcast(sent_packets), proposer.constants.all.config.replica_ids[proposer.constants.my_index]); //OBSERVE
                    //var end_timeNominateNew := Time.GetDebugTimeTicks();
                    //RecordTimingSeq("ProposerMaybeNominateValueAndSend2a_new_or_noop", end_time2, end_timeNominateNew);
                    //print("ProposerMaybeNominateValueAndSend2a: |proposer.request_queue| > 0. Nominating new value at ", proposer.next_operation_number_to_propose, "\n");
                } else {
                    if ( queueSize > 0 && proposer.incomplete_batch_timer.CIncompleteBatchTimerOff? ) {
                        var sum := UpperBoundedAdditionImpl(clock, proposer.constants.all.params.max_batch_delay, proposer.constants.all.params.max_integer_val);
                        proposer' := proposer[incomplete_batch_timer := CIncompleteBatchTimerOn(sum)];
                        sent_packets := CBroadcastNop;
                    } else {
                        proposer' := proposer;
                        sent_packets := CBroadcastNop;
                        
                        //RecordTimingSeq("ProposerMaybeNominateValueAndSend2a_DidSomeAcceptorHaveProposal", end_time2, end_time3);
                        //if existsOpn {
                        //    proposer', sent_packets := ProposerNominateNewValueAndSend2a(proposer, clock, log_truncation_point);
                        //    assert OutboundPacketsHasCorrectSrc(Broadcast(sent_packets), proposer.constants.all.config.replica_ids[proposer.constants.my_index]); //OBSERVE
                        //    var end_timeNoOp := Time.GetDebugTimeTicks();
                        //    RecordTimingSeq("ProposerMaybeNominateValueAndSend2a_noop", start_time, end_timeNoOp);
                        //    //print("ProposerMaybeNominateValueAndSend2a: proposer.next_operation_number_to_propose = ", proposer.next_operation_number_to_propose, ", DidSomeAcceptorHaveProposal = ", existsOpn, "\n");
                        //} else {
                        //    //assert proposer.next_operation_number_to_propose == proposer.maxOpnWithProposal.n;
                        //    //start_time := Time.GetDebugTimeTicks();
                        //    proposer' := proposer;
                        //    sent_packets := CBroadcastNop;
                        //    //lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(sent_packets);
                        //    var end_time4 := Time.GetDebugTimeTicks();
                        //    RecordTimingSeq("ProposerMaybeNominateValueAndSend2a_nada_shouldneverhappen", start_time, end_time4);
                        //    //print("ProposerMaybeNominateValueAndSend2a: proposer.next_operation_number_to_propose = ", proposer.next_operation_number_to_propose, ". NADA\n");
                        //}
                    }
                }
            }
        }
    }
}


method ProposerProcessHeartbeat(proposer:ProposerState, packet:CPacket, clock:uint64, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (proposer':ProposerState)
    requires ProposerIsValid(proposer);
    requires CPacketIsAbstractable(packet);
    requires packet.msg.CMessage_Heartbeat?;
    requires cur_req_set != null && prev_req_set != null;
    requires MutableSet.SetOf(cur_req_set) == proposer.election_state.cur_req_set;
    requires MutableSet.SetOf(prev_req_set) == proposer.election_state.prev_req_set;
    modifies cur_req_set, prev_req_set;
    ensures  ProposerIsValid(proposer');
    ensures  LProposerProcessHeartbeat(AbstractifyProposerStateToLProposer(proposer), AbstractifyProposerStateToLProposer(proposer'), AbstractifyCPacketToRslPacket(packet), int(clock));
    ensures proposer.constants == proposer'.constants;
    ensures  MutableSet.SetOf(cur_req_set) == proposer'.election_state.cur_req_set;
    ensures  MutableSet.SetOf(prev_req_set) == proposer'.election_state.prev_req_set;
{
    var election_state' := ElectionProcessHeartbeat(proposer.election_state, packet, clock, cur_req_set, prev_req_set);

    var current_state' := 0;
    var request_queue' := [];
    var lt := CBalLt(proposer.election_state.current_view, election_state'.current_view);
    if  lt {
        //assert AbstractifyCBallotToBallot(election_state'.current_view) > AbstractifyCBallotToBallot(proposer.election_state.current_view);
        current_state' := 0;
        request_queue' := [];
    } else {
        current_state' := proposer.current_state;
        request_queue' := proposer.request_queue;
    }

    proposer' := proposer[election_state := election_state'][current_state := current_state'][request_queue := request_queue'];
}

method ProposerCheckForViewTimeout(proposer:ProposerState, clock:uint64, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (proposer':ProposerState)
    requires ProposerIsValid(proposer);
    requires cur_req_set != null && prev_req_set != null;
    requires MutableSet.SetOf(cur_req_set) == proposer.election_state.cur_req_set;
    requires MutableSet.SetOf(prev_req_set) == proposer.election_state.prev_req_set;
    modifies cur_req_set, prev_req_set;
    ensures  ProposerIsValid(proposer');
    ensures  LProposerCheckForViewTimeout(AbstractifyProposerStateToLProposer(proposer), AbstractifyProposerStateToLProposer(proposer'), int(clock));
    ensures  proposer.constants == proposer'.constants;
    ensures  MutableSet.SetOf(cur_req_set) == proposer'.election_state.cur_req_set;
    ensures  MutableSet.SetOf(prev_req_set) == proposer'.election_state.prev_req_set;
{
    var election_state' := ElectionCheckForViewTimeout(proposer.election_state, clock, cur_req_set, prev_req_set);
    proposer' := proposer[election_state := election_state'];
}

method ProposerCheckForQuorumOfViewSuspicions(proposer:ProposerState, clock:uint64, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (proposer':ProposerState)
    requires ProposerIsValid(proposer);
    requires cur_req_set != null && prev_req_set != null;
    requires MutableSet.SetOf(cur_req_set) == proposer.election_state.cur_req_set;
    requires MutableSet.SetOf(prev_req_set) == proposer.election_state.prev_req_set;
    modifies cur_req_set, prev_req_set;
    ensures  ProposerIsValid(proposer');
    ensures  LProposerCheckForQuorumOfViewSuspicions(AbstractifyProposerStateToLProposer(proposer), AbstractifyProposerStateToLProposer(proposer'), int(clock));
    ensures  proposer.constants == proposer'.constants;
    ensures  MutableSet.SetOf(cur_req_set) == proposer'.election_state.cur_req_set;
    ensures  MutableSet.SetOf(prev_req_set) == proposer'.election_state.prev_req_set;
{
    var start_time := Time.GetDebugTimeTicks();
    var election_state' := ElectionCheckForQuorumOfViewSuspicions(proposer.election_state, clock, cur_req_set, prev_req_set);

    var current_state' := 0;
    var request_queue' := [];
    var lt := CBalLt(proposer.election_state.current_view, election_state'.current_view);
    if  lt {
        current_state' := 0;
        request_queue' := [];
    } else {
        current_state' := proposer.current_state;
        request_queue' := proposer.request_queue;
    }

    proposer' := proposer[election_state := election_state'][current_state := current_state'][request_queue := request_queue'];
    var end_time := Time.GetDebugTimeTicks();
    if lt {
        RecordTimingSeq("ProposerCheckForQuorumOfViewSuspicions_changed", start_time, end_time);
    } else {
        RecordTimingSeq("ProposerCheckForQuorumOfViewSuspicions_nada", start_time, end_time);
    }
}

method ProposerResetViewTimerDueToExecution(proposer:ProposerState, val:CRequestBatch, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (proposer':ProposerState)
    requires ProposerIsValid(proposer);
    requires CRequestBatchIsAbstractable(val);
    requires ValidRequestBatch(val);
    requires cur_req_set != null && prev_req_set != null;
    requires MutableSet.SetOf(cur_req_set) == proposer.election_state.cur_req_set;
    requires MutableSet.SetOf(prev_req_set) == proposer.election_state.prev_req_set;
    modifies cur_req_set, prev_req_set;
    ensures  ProposerIsValid(proposer');
    ensures  LProposerResetViewTimerDueToExecution(AbstractifyProposerStateToLProposer(proposer), AbstractifyProposerStateToLProposer(proposer'), AbstractifyCRequestBatchToRequestBatch(val));
    ensures proposer.constants == proposer'.constants;
    ensures  MutableSet.SetOf(cur_req_set) == proposer'.election_state.cur_req_set;
    ensures  MutableSet.SetOf(prev_req_set) == proposer'.election_state.prev_req_set;
{
    var election_state' := ElectionReflectExecutedRequestBatch(proposer.election_state, val, cur_req_set, prev_req_set);
    proposer' := proposer[election_state := election_state'];
}

} 
