include "AcceptorState.i.dfy"
include "Broadcast.i.dfy"
include "../Common/Util.i.dfy"

module LiveRSL__AcceptorModel_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__Acceptor_i
import opened LiveRSL__AcceptorState_i
import opened LiveRSL__CLastCheckpointedMap_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Message_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__ParametersState_i
import opened LiveRSL__ReplicaConstantsState_i
import opened LiveRSL__Types_i
import opened Impl__LiveRSL__Broadcast_i
import opened Collections__Maps_i
import opened Collections__Maps2_s
import opened Collections__Sets_i
import opened Common__NodeIdentity_i
import opened Common__UpperBound_s
import opened Common__UpperBound_i
import opened Common__Util_i
import opened Environment_s

method CreateSeq(len:int, init_int:uint64) returns (s:seq<COperationNumber>)
  requires len >= 0
  ensures  |s| == len && forall i :: 0 <= i < |s| ==> s[i] == COperationNumber(init_int)
{
  if len == 0 {
    s := [];
  } else { 
    var rest := CreateSeq(len - 1, init_int);
    s := [COperationNumber(init_int)] + rest;    
  }
}

method DummyInitLastCheckpointedOperation(config:CPaxosConfiguration) returns (ilco:CLastCheckpointedMap)
  requires CPaxosConfigurationIsValid(config)
  requires CPaxosConfigurationIsAbstractable(config)
  ensures CLastCheckpointedMapIsAbstractable(ilco)
  ensures LMinQuorumSize(AbstractifyCPaxosConfigurationToConfiguration(config)) <= |ilco|
  ensures |config.replica_ids| == |ilco|
  ensures forall i :: 0 <= i < |ilco| ==> ilco[i] == COperationNumber(0)
{
  ilco := CreateSeq(|config.replica_ids|, 0);
  ghost var rlco := AbstractifyCLastCheckpointedMapToOperationNumberSequence(ilco); // TRIGGER
  reveal AbstractifyCLastCheckpointedMapToOperationNumberSequence();
}

method InitAcceptorState(rcs:ReplicaConstantsState) returns (acceptor:AcceptorState)
  requires ReplicaConstantsState_IsValid(rcs)
  ensures NextAcceptorState_InitPostconditions(acceptor, rcs)
{
  reveal AbstractifyCVotesToVotes();

  var max_ballot := CBallot(0, 0);
  var votes := CVotes(map []);
  var last_checkpointed_operation := DummyInitLastCheckpointedOperation(rcs.all.config);
  var log_truncation_point := COperationNumber(0);
  var min_voted_opn := COperationNumber(0);
  acceptor := AcceptorState(
    rcs, max_ballot, votes, last_checkpointed_operation,  log_truncation_point, min_voted_opn);
  assert LAcceptorInit(AbstractifyAcceptorStateToAcceptor(acceptor), AbstractifyReplicaConstantsStateToLReplicaConstants(rcs));
}

method NextAcceptorState_Phase1(acceptor:AcceptorState, in_msg:CMessage, sender:EndPoint) returns (acceptor':AcceptorState, packets_sent:CBroadcast)
  requires NextAcceptorState_Phase1Preconditions(acceptor, in_msg, sender)
  ensures NextAcceptorState_Phase1Postconditions(acceptor, acceptor', in_msg, sender, packets_sent)
{
  //print("NextAcceptorState_Phase1: Responding to an 1a message\n");
  packets_sent := CBroadcastNop;
  var ballot := in_msg.bal_1a;
  lemma_AbstractifyEndPointsToNodeIdentities_properties(acceptor.constants.all.config.replica_ids);

  // if the ballot is not greater
  if (!CBallotIsLessThan(acceptor.maxBallot, ballot)) {
    //print("NextAcceptorState_Phase1: Ignoring the 1a message because I'm in ", acceptor.maxBallot.seqno, acceptor.maxBallot.proposer_id, " but the ballot is ", ballot.seqno, ballot.proposer_id, "\n");
    acceptor' := acceptor;
    return;
  }
  if (sender !in acceptor.constants.all.config.replica_ids) {
    //print("NextAcceptorState_Phase1: Ignoring the 1a message because it's from a non-replica ", sender.addr, sender.port, "\n");
    acceptor' := acceptor;
    return;
  }
  //print("NextAcceptorState_Phase1: Sending a 1b message for ballot ", ballot, "\n");
  var outMsg := CMessage_1b(ballot, acceptor.log_truncation_point, acceptor.votes);
  packets_sent := CBroadcast(acceptor.constants.all.config.replica_ids[acceptor.constants.my_index], 
                            [sender], outMsg);

  acceptor' := acceptor.(maxBallot := ballot);

  ghost var r_packet := AbstractifyCMessageToRslPacket(acceptor.constants.all.config.replica_ids[acceptor.constants.my_index], sender, in_msg);
  ghost var r_constants := AbstractifyReplicaConstantsStateToLReplicaConstants(acceptor.constants);
  ghost var dsts := [acceptor.constants.all.config.replica_ids[acceptor.constants.my_index]];
  calc {
    AbstractifyCBroadcastToRlsPacketSeq(packets_sent);
    [ LPacket(AbstractifyEndPointToNodeIdentity(sender), AbstractifyEndPointsToNodeIdentities(dsts)[0], AbstractifyCMessageToRslMessage(outMsg)) ];
    [ LPacket(AbstractifyEndPointToNodeIdentity(sender), AbstractifyEndPointToNodeIdentity(acceptor.constants.all.config.replica_ids[acceptor.constants.my_index]), AbstractifyCMessageToRslMessage(outMsg)) ];
    [ LPacket(r_packet.src, r_constants.all.config.replica_ids[r_constants.my_index], AbstractifyCMessageToRslMessage(outMsg)) ];
    [ LPacket(r_packet.src, r_constants.all.config.replica_ids[r_constants.my_index], RslMessage_1b(r_packet.msg.bal_1a, AbstractifyCOperationNumberToOperationNumber(acceptor.log_truncation_point), AbstractifyCVotesToVotes(acceptor.votes))) ];
  }

  assert NextAcceptorState_Phase1Postconditions(acceptor, acceptor', in_msg, sender, packets_sent);
}

lemma lemma_AcceptorVotesSizeIsBoundedByLogLength(
  votes:CVotes,
  log_truncation_point:COperationNumber,
  params:ParametersState
  )
  requires params.max_log_length > 0
  requires forall opn :: opn in votes.v ==>
                      AbstractifyCOperationNumberToOperationNumber(log_truncation_point)
                      <= AbstractifyCOperationNumberToOperationNumber(opn)
                      <= UpperBoundedAddition(AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
                                             (params.max_log_length-1) as int,
                                             UpperBoundFinite(params.max_integer_val as int))
  ensures  |votes.v| <= params.max_log_length as int
{
  var copns := mapdomain(votes.v);
  var opns := AbstractifyCOperationNumbersToOperationNumbers(copns);
  lemma_AbstractifyCOperationNumbersToOperationNumbers_maintainsSize(copns);
  lemma_CardinalityOfBoundedSet(opns, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCOperationNumberToOperationNumber(log_truncation_point) + (params.max_log_length as int));
  lemma_MapSizeIsDomainSize(mapdomain(votes.v), votes.v);
}


method AddVoteAndRemoveOldOnesImpl(acceptor:AcceptorState, votes:CVotes, new_opn:COperationNumber, new_vote:CVote, newLogTruncationPoint:COperationNumber, minVotedOpn:COperationNumber,
                                   ghost oldLogTruncationPoint:COperationNumber, ghost params:ParametersState) returns (votes':CVotes, newMinVotedOpn:COperationNumber)
  requires CVotesIsAbstractable(votes)
  requires COperationNumberIsAbstractable(new_opn)
  requires CVoteIsAbstractable(new_vote)
  requires COperationNumberIsAbstractable(newLogTruncationPoint)
  requires newLogTruncationPoint.n <= params.max_integer_val
  requires new_opn.n <= params.max_integer_val
  requires newLogTruncationPoint.n <= new_opn.n
  requires params.max_integer_val > params.max_log_length > 0
  requires newLogTruncationPoint.n >= oldLogTruncationPoint.n
  requires params.max_log_length as int < max_votes_len()
  requires AbstractifyCOperationNumberToOperationNumber(new_opn) <= AbstractifyCOperationNumberToOperationNumber(newLogTruncationPoint) + ((params.max_log_length-1) as int)
  requires forall opn :: opn in votes.v ==>
                      AbstractifyCOperationNumberToOperationNumber(oldLogTruncationPoint)
                      <= AbstractifyCOperationNumberToOperationNumber(opn)
                      <= UpperBoundedAddition(AbstractifyCOperationNumberToOperationNumber(oldLogTruncationPoint),
                                             (params.max_log_length-1) as int,
                                             UpperBoundFinite(params.max_integer_val as int))
  requires ValidVotes(votes)
  requires ValidVote(new_vote)
  requires AcceptorIsValid(acceptor)
  requires votes == acceptor.votes
  requires minVotedOpn == acceptor.minVotedOpn
  ensures  forall opn :: opn in votes'.v ==>
                      AbstractifyCOperationNumberToOperationNumber(newLogTruncationPoint)
                      <= AbstractifyCOperationNumberToOperationNumber(opn)
                      <= UpperBoundedAddition(AbstractifyCOperationNumberToOperationNumber(newLogTruncationPoint),
                                             (params.max_log_length-1) as int,
                                             UpperBoundFinite(params.max_integer_val as int))
  ensures  CVotesIsAbstractable(votes')
  ensures  ValidVotes(votes')
  ensures  LAddVoteAndRemoveOldOnes(AbstractifyCVotesToVotes(votes), AbstractifyCVotesToVotes(votes'), AbstractifyCOperationNumberToOperationNumber(new_opn), AbstractifyCVoteToVote(new_vote), AbstractifyCOperationNumberToOperationNumber(newLogTruncationPoint))
  ensures  forall v :: v in votes'.v ==> v.n >= newMinVotedOpn.n
{
  reveal AbstractifyCVotesToVotes();

  var updated_votes := votes.v[new_opn := new_vote];
  var new_votes;
  if (newLogTruncationPoint.n > minVotedOpn.n) {
    //print("Creating new table, going to ",newLogTruncationPoint.n," up from ",minVotedOpn.n,"\n");
    new_votes := (map op | op in updated_votes && op.n >= newLogTruncationPoint.n :: updated_votes[op]);
    newMinVotedOpn := newLogTruncationPoint;
  } else {
    new_votes := updated_votes;
    if( new_opn.n < minVotedOpn.n) {
      newMinVotedOpn := new_opn;
    } else {
      newMinVotedOpn := minVotedOpn;
    }
  }
  votes' := CVotes(new_votes);
  lemma_MapSizeIsDomainSize(domain(updated_votes), updated_votes);
  lemma_MapSizeIsDomainSize(domain(new_votes), new_votes);
  SubsetCardinality(domain(new_votes),domain(votes'.v));

  forall opn | opn in votes'.v
    ensures AbstractifyCOperationNumberToOperationNumber(newLogTruncationPoint)
            <= AbstractifyCOperationNumberToOperationNumber(opn)
            <= UpperBoundedAddition(AbstractifyCOperationNumberToOperationNumber(newLogTruncationPoint),
                                   (params.max_log_length-1) as int,
                                   UpperBoundFinite(params.max_integer_val as int))
  {
    if opn == new_opn {
      assert AbstractifyCOperationNumberToOperationNumber(opn)
        <= UpperBoundedAddition(AbstractifyCOperationNumberToOperationNumber(newLogTruncationPoint),
                               (params.max_log_length-1) as int,
                               UpperBoundFinite(params.max_integer_val as int));
    }
  }

  lemma_AcceptorVotesSizeIsBoundedByLogLength(votes', newLogTruncationPoint, params);
  assert |votes'.v| < 0x1_0000_0000;
}

method {:timeLimitMultiplier 2} NextAcceptorState_Phase2(acceptor:AcceptorState, in_msg:CMessage, sender:EndPoint) returns (acceptor':AcceptorState, packets_sent:CBroadcast)
  requires NextAcceptorState_Phase2Preconditions(acceptor, in_msg, sender)
  ensures NextAcceptorState_Phase2Postconditions(acceptor, acceptor', in_msg, sender, packets_sent)
{
  var start_time := Time.GetDebugTimeTicks();
//  reveal AbstractifyCVotesToVotes();

  packets_sent := CBroadcastNop;
  acceptor' := acceptor;

  var ballot := in_msg.bal_2a;

  //print("Acceptor receiving 2a message about operation", in_msg.opn_2a.n, "in ballot", in_msg.bal_2a, "\n");

  assert acceptor.constants.all.params.max_integer_val > acceptor.constants.all.params.max_log_length > 0;
  var maxLogLengthMinus1:uint64 := acceptor.constants.all.params.max_log_length - 1;
  var newLogTruncationPoint := acceptor.log_truncation_point;
  if in_msg.opn_2a.n >= maxLogLengthMinus1
  {
    var potentialNewTruncationPoint:uint64 := in_msg.opn_2a.n - maxLogLengthMinus1;
    if potentialNewTruncationPoint > acceptor.log_truncation_point.n
    {
      newLogTruncationPoint := COperationNumber(potentialNewTruncationPoint);
    }
  }

  assert AbstractifyCOperationNumberToOperationNumber(newLogTruncationPoint) ==
               if AbstractifyCOperationNumberToOperationNumber(in_msg.opn_2a) - (acceptor.constants.all.params.max_log_length as int) + 1
                  > AbstractifyCOperationNumberToOperationNumber(acceptor.log_truncation_point) then
                   AbstractifyCOperationNumberToOperationNumber(in_msg.opn_2a) - (acceptor.constants.all.params.max_log_length as int) + 1
               else
                   AbstractifyCOperationNumberToOperationNumber(acceptor.log_truncation_point);

  var addition := UpperBoundedAdditionImpl(acceptor.log_truncation_point.n, acceptor.constants.all.params.max_log_length, acceptor.constants.all.params.max_integer_val);
  assert AbstractifyCOperationNumberToOperationNumber(in_msg.opn_2a) <= 
        UpperBoundedAddition(AbstractifyCOperationNumberToOperationNumber(newLogTruncationPoint), 
            (acceptor.constants.all.params.max_log_length-1) as int,
            UpperBoundFinite(acceptor.constants.all.params.max_integer_val as int));

  var opn := in_msg.opn_2a;
  var value := in_msg.val_2a;
  var newVote := CVote(ballot, value);

  var votes', newMinVotedOpn;
  if(acceptor.log_truncation_point.n <= in_msg.opn_2a.n) {
    votes', newMinVotedOpn := AddVoteAndRemoveOldOnesImpl(acceptor, acceptor.votes, opn, newVote, newLogTruncationPoint, acceptor.minVotedOpn,
                                                          acceptor.log_truncation_point /* ghost */, acceptor.constants.all.params /* ghost */);
  } else {
    votes' := acceptor.votes;
    newMinVotedOpn := acceptor.minVotedOpn;
  }
    
  var outMsg := CMessage_2b(ballot, opn, value);

  acceptor' :=
        acceptor.(
            votes := votes',
            maxBallot := ballot,
            log_truncation_point := newLogTruncationPoint,
            minVotedOpn := newMinVotedOpn);

  packets_sent := BuildBroadcastToEveryone(acceptor.constants.all.config, acceptor.constants.my_index, outMsg);
  assert NextAcceptorState_Phase2Postconditions(acceptor, acceptor', in_msg, sender, packets_sent);
  var end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("NextAcceptorState_Phase2", start_time, end_time);
}

method {:timeLimitMultiplier 1} NextAcceptorState_ProcessHeartbeat(acceptor:AcceptorState, in_msg:CMessage, sender:EndPoint) returns (acceptor':AcceptorState)
  requires NextAcceptorState_ProcessHeartbeatPreconditions(acceptor, in_msg, sender)
  ensures NextAcceptorState_ProcessHeartbeatPostconditions(acceptor, acceptor', in_msg, sender)
{
  acceptor' := acceptor;
  lemma_AbstractifyEndPointsToNodeIdentities_properties(acceptor.constants.all.config.replica_ids);
  lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
  lemma_Uint64EndPointRelationships();
  var found:bool, index:uint64 := CGetReplicaIndex(sender, acceptor.constants.all.config);
  if (!found) {
    //print("Acceptor ignoring heartbeat from", sender, "\n");
    return;
  }

  ///assert AbstractifyEndPointToNodeIdentity(sender) in AbstractifyCLastCheckpointedMapToOperationNumberSequence(acceptor.last_checkpointed_operation);
  assert 0 <= index as int < |acceptor.constants.all.config.replica_ids|;
  if (in_msg.opn_ckpt.n <= acceptor.last_checkpointed_operation[index].n) {
    return;
  }

  //print("Acceptor updating last checkpointed operation for", sender, "to", in_msg.opn_ckpt.n, "\n");

  var LCO := acceptor.last_checkpointed_operation;

  var newLCO := acceptor.last_checkpointed_operation[index as int := in_msg.opn_ckpt];

  acceptor' := acceptor.(last_checkpointed_operation:= newLCO);
}

method {:timeLimitMultiplier 1} NextAcceptorState_TruncateLog(acceptor:AcceptorState, opn:COperationNumber) returns (acceptor':AcceptorState)
  requires NextAcceptorState_TruncateLogPreconditions(acceptor, opn)
  ensures NextAcceptorState_TruncateLogPostconditions(acceptor, acceptor', opn)
{
  //print("Acceptor truncating log to", opn, "\n");

  if (opn.n > acceptor.log_truncation_point.n) {
    assert AbstractifyCOperationNumberToOperationNumber(opn) > AbstractifyCOperationNumberToOperationNumber(acceptor.log_truncation_point);
    reveal AbstractifyCVotesToVotes();
    var truncatedVotes:map<COperationNumber,CVote> := (map op | op in acceptor.votes.v && op.n >= opn.n :: acceptor.votes.v[op]);
    acceptor' := acceptor.(log_truncation_point := opn,
                           votes := acceptor.votes.(v := truncatedVotes));
    lemma_MapSizeIsDomainSize(domain(truncatedVotes), truncatedVotes);
    lemma_MapSizeIsDomainSize(domain(acceptor.votes.v), acceptor.votes.v);
    SubsetCardinality(domain(truncatedVotes),domain(acceptor.votes.v));
  } else {
    acceptor' := acceptor;
  }
}

method AcceptorModel_GetNthHighestValueAmongReportedCheckpoints(acceptor:AcceptorState, minQuorumSize:uint64) returns (opn:COperationNumber)
  requires AcceptorIsValid(acceptor)
  requires AcceptorIsAbstractable(acceptor)
  requires minQuorumSize > 0
  requires minQuorumSize as int <= |acceptor.last_checkpointed_operation|
  requires LMinQuorumSize(AbstractifyAcceptorStateToAcceptor(acceptor).constants.all.config) == minQuorumSize as int
  ensures  IsLogTruncationPointValid(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifyAcceptorStateToAcceptor(acceptor).last_checkpointed_operation, AbstractifyAcceptorStateToAcceptor(acceptor).constants.all.config)
{
  opn := ComputeNthHighestValue(acceptor.last_checkpointed_operation, minQuorumSize);
  //print("Acceptor computes nth highest value as", opn, "\n");
}

} 
