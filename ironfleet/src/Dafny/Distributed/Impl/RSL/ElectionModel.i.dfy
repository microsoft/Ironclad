include "ElectionState.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "MinCQuorumSize.i.dfy"
include "../Common/Util.i.dfy"
include "../Common/UpperBound.i.dfy"

module LiveRSL__ElectionModel_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__ConstantsState_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__Election_i
import opened LiveRSL__ElectionState_i
import opened LiveRSL__MinCQuorumSize_i
import opened LiveRSL__ReplicaConstantsState_i
import opened LiveRSL__Types_i
import opened Common__NodeIdentity_i
import opened Common__SeqIsUnique_i
import opened Common__SeqIsUniqueDef_i
import opened Common__UpperBound_s
import opened Common__UpperBound_i
import opened Common__Util_i
import opened Collections__Seqs_s
import opened Collections__Sets_i

// Same as x == y, but triggers extensional equality on fields and provides better error diagnostics
predicate Eq_ElectionState(x:ElectionState, y:ElectionState)
{
  && x.constants == y.constants
  && x.current_view == y.current_view
  && x.current_view_suspectors == y.current_view_suspectors
  && x.epoch_end_time == y.epoch_end_time
  && x.epoch_length == y.epoch_length
  && x.requests_received_this_epoch == y.requests_received_this_epoch
  && x.requests_received_prev_epochs == y.requests_received_prev_epochs
}

//////////////////////
// BALLOT MATH
//////////////////////

method CComputeSuccessorView(cb:CBallot, constants:ConstantsState) returns(cb':CBallot)
  requires CBallotIsAbstractable(cb)
  requires ConstantsStateIsAbstractable(constants)
  requires CPaxosConfigurationIsValid(constants.config)
  requires cb.seqno < 0xFFFF_FFFF_FFFF_FFFF
  ensures  CBallotIsAbstractable(cb')
  ensures  ComputeSuccessorView(AbstractifyCBallotToBallot(cb), AbstractifyConstantsStateToLConstants(constants)) == AbstractifyCBallotToBallot(cb')
{
  ghost var b := AbstractifyCBallotToBallot(cb);

  if cb.proposer_id < (|constants.config.replica_ids| as uint64) - 1 { 
    cb' := CBallot(cb.seqno, cb.proposer_id + 1);
  } else {
    cb' := CBallot(cb.seqno + 1, 0);
  }
}

function ElectionStateUpdateValueSetsToReflectNextEpoch(es:ElectionState):ElectionState
{
  es.(requests_received_this_epoch := [],
      requests_received_prev_epochs := es.requests_received_prev_epochs + es.requests_received_this_epoch)
}

//function method CElectionStateValueSetsReflectNewView(es:CElectionState):CElectionState
//  requires CElectionStateIsAbstractable(es)
//  ensures CElectionStateIsAbstractable(CElectionStateValueSetsReflectNewView(es))
//  ensures ElectionStateUpdateValueSetsToReflectNextEpoch(AbstractifyCElectionStateToElectionState(es)) 
//            == AbstractifyCElectionStateToElectionState(CElectionStateValueSetsReflectNewView(es))
//{
//  lemma_AbstractifyCRequestsSeqToRequestsSeq_concat(es.requests_received_prev_epochs, es.requests_received_this_epoch);
//  es[requests_received_this_epoch := []]
//    [requests_received_prev_epochs := es.requests_received_prev_epochs + es.requests_received_this_epoch]
//}

//////////////////////
// SEQUENCE MATH
//////////////////////

function method BoundCRequestSequence(s:seq<CRequest>, lengthBound:uint64):(bool,seq<CRequest>)
  requires |s| < 0x1_0000_0000_0000_0000
{
  if 0 <= lengthBound < (|s| as uint64) then (true, s[..lengthBound]) else (false,s)
}

lemma lemma_BoundCRequestSequence(s:seq<CRequest>, lengthBound:uint64)
  requires |s| < 0x1_0000_0000_0000_0000
  requires CRequestsSeqIsAbstractable(s)
  ensures  BoundRequestSequence(AbstractifyCRequestsSeqToRequestsSeq(s), UpperBoundFinite(lengthBound as int))
           == AbstractifyCRequestsSeqToRequestsSeq(BoundCRequestSequence(s, lengthBound).1)
  ensures |BoundCRequestSequence(s, lengthBound).1| <= lengthBound as int
{
}

ghost method FindMatchingRequest(s:seq<CRequest>, headers:set<CRequestHeader>, header:CRequestHeader) returns (index:int)
  requires HeadersMatch(s, headers)
  requires header in headers
  requires |s| >= 1
  ensures  0 <= index < |s|
  ensures  CRequestHeader(s[index].client, s[index].seqno) == header
{
  if |s| == 1 {
    assert CRequestHeader(s[0].client, s[0].seqno) in headers;
    assert |headers| == 1;
    ThingsIKnowAboutASingletonSet(headers, CRequestHeader(s[0].client, s[0].seqno), header);
    return 0;
  } else {
    var head := CRequestHeader(s[0].client, s[0].seqno);
    if head == header {
      return 0;
    } else {
      var new_set := headers - { head };
      forall r | r in s[1..]
        ensures CRequestHeader(r.client, r.seqno) in new_set;
      {
        if CRequestHeader(r.client, r.seqno) != head {
          assert CRequestHeader(r.client, r.seqno) in new_set;
        } else {
          var j :| 0 <= j < |s[1..]| && s[1..][j] == r;
          assert s[j+1] == s[1..][j] == r;
          assert CRequestsMatch(s[0], s[j+1]);
          assert j+1 == 0;
          assert false;
        }
      }
      index := FindMatchingRequest(s[1..], new_set, header);
      index := index + 1;
    }
  }
}
    
// This is inefficient, but we never expect to call it in practice, since we shouldn't exceed lengthBound
method BoundCRequestHeaders(s:seq<CRequest>, ghost headers:set<CRequestHeader>, lengthBound:uint64, cur_req_set:MutableSet<CRequestHeader>)
  returns (ghost new_headers:set<CRequestHeader>)
  requires |s| < 0x1_0000_0000_0000_0000
  requires HeadersMatch(s, headers)
  requires |s| > lengthBound as int
  modifies cur_req_set
  ensures  HeadersMatch(BoundCRequestSequence(s, lengthBound).1, new_headers)
  ensures  forall h :: h in new_headers ==> h in headers
  ensures MutableSet.SetOf(cur_req_set) == new_headers
{
  var i := 0;
  new_headers := {};
  cur_req_set.RemoveAll();

  while i < lengthBound as int
    invariant 0 <= i <= lengthBound as int;
    invariant HeadersMatch(s[..i], new_headers)
      invariant forall h :: h in new_headers ==> h in headers
      invariant MutableSet.SetOf(cur_req_set) == new_headers
  {
    var new_header := CRequestHeader(s[i].client, s[i].seqno);
    if new_header in new_headers {
      var j := FindMatchingRequest(s[..i], new_headers, new_header); 
      assert CRequestsMatch(s[j], s[i]);
      assert false;
    }
    new_headers := new_headers + { new_header };
    cur_req_set.Add(new_header);
    i := i + 1;
  }
}


//////////////////////
// REQUESTS
//////////////////////

function {:fuel 5,6} RemoveAllSatisfiedCRequestsInSequence(s:seq<CRequest>, r:CRequest):seq<CRequest>
  ensures  forall r' :: r' in RemoveAllSatisfiedCRequestsInSequence(s, r) ==> r' in s
{
  if |s| == 0 then
    []
  else if CRequestSatisfiedBy(s[0], r) then
    RemoveAllSatisfiedCRequestsInSequence(s[1..], r)
  else
    [s[0]] + RemoveAllSatisfiedCRequestsInSequence(s[1..], r)
}

function {:fuel 5,6} RemoveAllSatisfiedCRequestsInSequenceAlt(s:seq<CRequest>, r:CRequest):seq<CRequest>
{
  if |s| == 0 then
    []
  else if CRequestSatisfiedBy(last(s), r) then
    RemoveAllSatisfiedCRequestsInSequence(all_but_last(s), r)
  else
    RemoveAllSatisfiedCRequestsInSequence(all_but_last(s), r) + [last(s)]
}

lemma lemma_RemoveAllSatisfiedCRequestsInSequenceAltEquivalent(s:seq<CRequest>, r:CRequest)
  ensures RemoveAllSatisfiedCRequestsInSequence(s, r) == RemoveAllSatisfiedCRequestsInSequenceAlt(s, r)
{
  if |s| == 0 || |s| == 1 {
    return;
  }

  lemma_RemoveAllSatisfiedCRequestsInSequenceAltEquivalent(s[1..], r);
  lemma_RemoveAllSatisfiedCRequestsInSequenceAltEquivalent(all_but_last(s[1..]), r);
  assert all_but_last(s)[0] == s[0];
  assert all_but_last(s)[1..] == all_but_last(s[1..]);
}

lemma lemma_RemoveAllSatisfiedCRequestsInSequenceUpdate(s:seq<CRequest>, r:CRequest, i:int)
  requires 0 <= i < |s|
  ensures  RemoveAllSatisfiedCRequestsInSequence(s[..i+1], r) == RemoveAllSatisfiedCRequestsInSequence(s[..i], r) + if CRequestSatisfiedBy(s[i], r) then [] else [s[i]]
{
  var s' := s[..i+1];
  assert last(s') == s[i];
  assert all_but_last(s') == s[..i];
  lemma_RemoveAllSatisfiedCRequestsInSequenceAltEquivalent(s', r);
}

function HeadersFromPrefix(s:seq<CRequest>, i:int):set<CRequestHeader>
  requires 0 <= i <= |s|
{
  set j | 0 <= j < i :: CRequestHeader(s[j].client, s[j].seqno)
}

lemma lemma_HeadersFromPrefixIncrease(s:seq<CRequest>, i:int)
  requires 0 <= i
  requires i+1 <= |s|
  ensures  HeadersFromPrefix(s, i+1) == HeadersFromPrefix(s, i) + { CRequestHeader(s[i].client, s[i].seqno) }
{
}

lemma lemma_EmptyHeadersMatch(
  s:seq<CRequest>,
  headers:set<CRequestHeader>
  )
  requires s == []
  requires headers == {}
  ensures HeadersMatch(s, headers)
{
}

lemma lemma_HeadersMatchImpliesEveryHeaderHasACorrespondingEntry(
  requests:seq<CRequest>,
  headers:set<CRequestHeader>,
  header:CRequestHeader
  ) returns (
  i:int
  )
  requires HeadersMatch(requests, headers)
  requires header in headers
  ensures  0 <= i < |requests|
  ensures  header.client == requests[i].client
  ensures  header.seqno == requests[i].seqno
{
  if |requests| == 0 {
    return;
  }

  var num_requests := |requests|;
  var last_header := CRequestHeader(requests[num_requests-1].client, requests[num_requests-1].seqno);
  assert last_header in headers;

  if header == last_header
  {
    i := num_requests - 1;
    return;
  }

  var requests' := requests[..num_requests-1];
  var headers' := headers - { last_header };

  forall r' | r' in requests'
    ensures CRequestHeader(r'.client, r'.seqno) in headers'
  {
    var j :| 0 <= j < |requests|-1 && r' == requests[j];
    var k := |requests| - 1;
    assert !CRequestsMatch(requests[j], requests[k]);
  }

  i := lemma_HeadersMatchImpliesEveryHeaderHasACorrespondingEntry(requests[..num_requests - 1], headers - { last_header }, header);
}

lemma lemma_AddingOneHeaderPreservesMatch(
  s:seq<CRequest>,
  headers:set<CRequestHeader>,
  r:CRequest,
  s':seq<CRequest>,
  headers':set<CRequestHeader>
  )
  requires s' == s + [r]
  requires headers' == headers + { CRequestHeader(r.client, r.seqno) }
  requires HeadersMatch(s, headers)
  requires forall r' :: r' in s ==> !CRequestsMatch(r', r)
  ensures  HeadersMatch(s', headers')
{
  var new_header := CRequestHeader(r.client, r.seqno);
  if new_header in headers
  {
    var i := lemma_HeadersMatchImpliesEveryHeaderHasACorrespondingEntry(s, headers, new_header);
    assert CRequestsMatch(s[i], r);
    assert false;
  }
  calc {
    |s'|;
    |s| + 1;
    |headers| + 1;
    |headers'|;
  }
  assert forall r' :: r' in s' ==> CRequestHeader(r'.client, r'.seqno) in headers';
}

lemma lemma_HeadersMatchImpliesHeadersFromPrefix(requests:seq<CRequest>, headers:set<CRequestHeader>)
  requires HeadersMatch(requests, headers)
  ensures  headers == HeadersFromPrefix(requests, |requests|)
{
  var headers' := HeadersFromPrefix(requests, |requests|);

  forall h | h in headers
    ensures h in headers'
  {
    var i := lemma_HeadersMatchImpliesEveryHeaderHasACorrespondingEntry(requests, headers, h);
  }

  forall h | h in headers'
    ensures h in headers
  {
    var i :| 0 <= i < |requests| && h == CRequestHeader(requests[i].client, requests[i].seqno);
  }
}

method{:timeLimitMultiplier 2} RemoveAllSatisfiedCRequestsInSequenceIter(
  requests:seq<CRequest>,
  ghost headers:set<CRequestHeader>,
  cur_req_set:MutableSet<CRequestHeader>,
  r:CRequest
  ) returns (
  requests':seq<CRequest>,
  ghost headers':set<CRequestHeader>
  )
  requires |requests| < 0x1_0000_0000_0000_0000
  requires HeadersMatch(requests, headers)
  requires MutableSet.SetOf(cur_req_set) == headers
  modifies cur_req_set
  ensures  requests' == RemoveAllSatisfiedCRequestsInSequence(requests, r)
  ensures  HeadersMatch(requests', headers')
//  ensures  headers' == headers <==> requests' == requests
  ensures  MutableSet.SetOf(cur_req_set) == headers'
{
  var i:uint64 := 0;
  var len := |requests| as uint64;
  ghost var removed_headers:set<CRequestHeader> := {};
  headers' := {};
  requests' := [];
  i := 0;

  lemma_EmptyHeadersMatch(requests', headers');

  while i < len
    invariant 0 <= i <= len
    invariant HeadersMatch(requests', headers')
    invariant forall r' :: r' in requests' ==> r' in requests[..i]
    invariant requests' == RemoveAllSatisfiedCRequestsInSequence(requests[..i], r)
    invariant MutableSet.SetOf(cur_req_set) == headers - removed_headers
    invariant headers' + removed_headers == HeadersFromPrefix(requests, i as int)
    invariant removed_headers * headers' == {}
  {
    ghost var old_requests' := requests';
    ghost var old_headers' := headers';

    lemma_RemoveAllSatisfiedCRequestsInSequenceUpdate(requests, r, i as int);

    var h := CRequestHeader(requests[i].client, requests[i].seqno);
    if h in removed_headers || h in headers'
    {
      var j :| 0 <= j < i && h == CRequestHeader(requests[j].client, requests[j].seqno);
      assert CRequestsMatch(requests[j], requests[i]);
      assert false;
    }
        
    if CRequestSatisfiedBy(requests[i], r) {
      cur_req_set.Remove(h);
      removed_headers := removed_headers + {h};
    }
    else {
      headers' := headers' + {h};
      requests' := requests' + [requests[i]];
      lemma_AddingOneHeaderPreservesMatch(old_requests', old_headers', requests[i], requests', headers');
    }

    lemma_HeadersFromPrefixIncrease(requests, i as int);
    i := i + 1;
  }

  assert requests[..i] == requests;
  lemma_HeadersMatchImpliesHeadersFromPrefix(requests, headers);
}

lemma lemma_RemoveAllSatisfiedCRequestsProducesCRequestSubset(requests:seq<CRequest>, r:CRequest)
  ensures  forall r' :: r' in RemoveAllSatisfiedCRequestsInSequence(requests, r) ==> r' in requests
{
}

lemma lemma_RemoveAllSatisfiedCRequestsProducesHeaderSubset(
  requests:seq<CRequest>,
  headers:set<CRequestHeader>,
  requests':seq<CRequest>,
  headers':set<CRequestHeader>,
  r:CRequest
  )
  requires HeadersMatch(requests, headers)
  requires HeadersMatch(requests', headers')
  requires requests' == RemoveAllSatisfiedCRequestsInSequence(requests, r)
  ensures  headers' <= headers
{
  forall h | h in headers'
    ensures h in headers
  {
    var i := lemma_HeadersMatchImpliesEveryHeaderHasACorrespondingEntry(requests', headers', h);
    lemma_RemoveAllSatisfiedCRequestsProducesCRequestSubset(requests, r);
    assert requests'[i] in requests;
  }
}
    

lemma lemma_RemoveAllSatisfiedPreservesHeaderMatches(requests1:seq<CRequest>,  headers1:set<CRequestHeader>, 
                                                     requests2:seq<CRequest>,  headers2:set<CRequestHeader>,
                                                     requests1':seq<CRequest>, headers1':set<CRequestHeader>,
                                                     requests2':seq<CRequest>, headers2':set<CRequestHeader>,
                                                     r:CRequest)
  requires HeadersMatch(requests1, headers1)
  requires HeadersMatch(requests2, headers2)
  requires HeadersMatch(requests1 + requests2, headers1 + headers2)
  requires HeadersMatch(requests1', headers1')
  requires HeadersMatch(requests2', headers2')
  requires requests1' == RemoveAllSatisfiedCRequestsInSequence(requests1, r)
  requires requests2' == RemoveAllSatisfiedCRequestsInSequence(requests2, r)
  ensures  HeadersMatch(requests1' + requests2', headers1' + headers2')
{
  var requests3 := requests1 + requests2;
  var requests3' := requests1' + requests2';
  var headers3' := headers1' + headers2';

  lemma_RemoveAllSatisfiedCRequestsProducesHeaderSubset(requests1, headers1, requests1', headers1', r);
  lemma_RemoveAllSatisfiedCRequestsProducesHeaderSubset(requests2, headers2, requests2', headers2', r);

  forall h | h in headers1' && h in headers2'
    ensures false
  {
    assert h in headers1 && h in headers2;
    var i := lemma_HeadersMatchImpliesEveryHeaderHasACorrespondingEntry(requests1, headers1, h);
    var j := lemma_HeadersMatchImpliesEveryHeaderHasACorrespondingEntry(requests2, headers2, h);
    assert CRequestsMatch(requests3[i], requests3[j + |requests1|]);
  }
  assert headers1' * headers2' == {};
  assert |requests3'| == |headers3'|;
}

lemma lemma_RemoveAllSatisfiedCRequestsInSequenceAbstractable(s:seq<CRequest>, r:CRequest)
  requires CRequestsSeqIsAbstractable(s)
  requires CRequestIsAbstractable(r)
  ensures  CRequestsSeqIsAbstractable(RemoveAllSatisfiedCRequestsInSequence(s, r))
{
}

lemma lemma_CRequestsMatch()
  ensures forall r1:CRequest, r2:CRequest :: CRequestIsAbstractable(r1) && CRequestIsAbstractable(r2) ==>
            CRequestsMatch(r1, r2) == RequestsMatch(AbstractifyCRequestToRequest(r1), AbstractifyCRequestToRequest(r2))
{
  forall r1:CRequest, r2:CRequest | CRequestIsAbstractable(r1) && CRequestIsAbstractable(r2)
    ensures CRequestsMatch(r1, r2) == RequestsMatch(AbstractifyCRequestToRequest(r1), AbstractifyCRequestToRequest(r2))
  {
    lemma_AbstractifyCRequestToRequest_isInjective();
    lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
  }
}


lemma lemma_SequenceDots<T>(s:seq<T>, start:int)
  requires 0 <= start <= |s|
  ensures s[start..] == s[start..|s|]
{}

lemma lemma_RemoveAllSatisfiedCRequestsInSequenceProperties(s:seq<CRequest>, r:CRequest)
  requires CRequestsSeqIsAbstractable(s)
  requires CRequestIsAbstractable(r)
  ensures  CRequestsSeqIsAbstractable(RemoveAllSatisfiedCRequestsInSequence(s, r))
  ensures  AbstractifyCRequestsSeqToRequestsSeq(RemoveAllSatisfiedCRequestsInSequence(s, r)) 
           == RemoveAllSatisfiedRequestsInSequence(AbstractifyCRequestsSeqToRequestsSeq(s), AbstractifyCRequestToRequest(r))
  ensures  |RemoveAllSatisfiedCRequestsInSequence(s, r)| <= |s|
  ensures ElectionRequestQueueValid(s) ==> ElectionRequestQueueValid(RemoveAllSatisfiedCRequestsInSequence(s, r))
{
  lemma_RemoveAllSatisfiedCRequestsInSequenceAbstractable(s, r);
  reveal AbstractifyCRequestsSeqToRequestsSeq();

  if |s| == 0
  {
    return;
  }

  if AbstractifyCRequestToRequest(s[0]).client == AbstractifyCRequestToRequest(r).client
  {
    lemma_AbstractifyEndPointToNodeIdentity_injective(s[0].client, r.client);
  }

  lemma_RemoveAllSatisfiedCRequestsInSequenceProperties(s[1..], r);
}

//////////////////////
// ACTIONS
//////////////////////

method InitElectionState(constants:ReplicaConstantsState) returns (election:CElectionState, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>)
  requires ReplicaConstantsStateIsAbstractable(constants)
  requires ReplicaConstantsState_IsValid(constants)
  requires CPaxosConfigurationIsValid(constants.all.config)
  ensures  CElectionStateIsAbstractable(election)
  ensures  WellFormedLConfiguration(AbstractifyReplicaConstantsStateToLReplicaConstants(constants).all.config)
  ensures  ElectionStateInit(AbstractifyCElectionStateToElectionState(election), AbstractifyReplicaConstantsStateToLReplicaConstants(constants))
  ensures  CElectionStateIsValid(election)
  ensures  fresh(cur_req_set) && fresh(prev_req_set) && cur_req_set != prev_req_set
  ensures  MutableSet.SetOf(cur_req_set) == election.cur_req_set
  ensures  MutableSet.SetOf(prev_req_set) == election.prev_req_set
{
  election := CElectionState(constants,
                             CBallot(1, 0),
                             [],
                             0,
                             constants.all.params.baseline_view_timeout_period,
                             [],
                             {},
                             [],
                             {});
  cur_req_set  := MutableSet.EmptySet();
  prev_req_set := MutableSet.EmptySet();

  calc ==> {
    true;
      { reveal SeqIsUnique(); }
    SeqIsUnique(election.current_view_suspectors);
  }

  // Some subset of below is an OBSERVE
  ghost var es := AbstractifyCElectionStateToElectionState(election);
  ghost var c := AbstractifyReplicaConstantsStateToLReplicaConstants(constants);

  assert es.constants == c;
  assert es.current_view == Ballot(1, 0);
  ghost var empty_set := {};
  calc { 
    es.current_view_suspectors; 
      { reveal AbstractifySeqOfUint64sToSetOfInts(); } 
    empty_set;
  }
  assert es.epoch_end_time == 0;
  assert es.epoch_length == c.all.params.baseline_view_timeout_period;
}


method {:timeLimitMultiplier 3} ElectionProcessHeartbeat(ces:CElectionState, cp:CPacket, clock:uint64, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (ces':CElectionState)
  requires CElectionStateIsValid(ces)
  requires CPacketIsAbstractable(cp)
  requires cp.msg.CMessage_Heartbeat?
  requires MutableSet.SetOf(cur_req_set) == ces.cur_req_set
  requires MutableSet.SetOf(prev_req_set) == ces.prev_req_set
  modifies cur_req_set, prev_req_set
  ensures  CElectionStateIsValid(ces')
  ensures  ElectionStateProcessHeartbeat(AbstractifyCElectionStateToElectionState(ces), AbstractifyCElectionStateToElectionState(ces'), AbstractifyCPacketToRslPacket(cp), clock as int)
  ensures MutableSet.SetOf(cur_req_set) == ces'.cur_req_set
  ensures MutableSet.SetOf(prev_req_set) == ces'.prev_req_set
{
  var src_ep := cp.src;
  var found:bool, index:uint64 := CGetReplicaIndex(src_ep, ces.constants.all.config);

  ghost var es := AbstractifyCElectionStateToElectionState(ces);
  ghost var es':ElectionState;
  lemma_AbstractifySeqOfUint64sToSetOfInts_properties(ces.current_view_suspectors);

  if !found {
    es' := es;
    ces' := ces;
  } else {
    ghost var p := AbstractifyCPacketToRslPacket(cp);
    ghost var sender_index := GetReplicaIndex(p.src, es.constants.all.config);
    if cp.msg.bal_heartbeat == ces.current_view && cp.msg.suspicious {
      es' := es.(current_view_suspectors := es.current_view_suspectors + {sender_index});
      ces' := ces.(current_view_suspectors := AppendToUniqueSeqMaybe(ces.current_view_suspectors, index));
      lemma_AbstractifySeqOfUint64sToSetOfInts_append(ces.current_view_suspectors, index);
      assert Eq_ElectionState(es', AbstractifyCElectionStateToElectionState(ces'));
    } else {
      var cmp := CBalLt(ces.current_view, cp.msg.bal_heartbeat);
      if cmp {
        ghost var new_epoch_length := UpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val);
        es' := es.(current_view := p.msg.bal_heartbeat,
                   current_view_suspectors := (if p.msg.suspicious then {sender_index} else {}),
                   epoch_length := new_epoch_length,
                   epoch_end_time := UpperBoundedAddition(clock as int, new_epoch_length, es.constants.all.params.max_integer_val),
                   requests_received_prev_epochs := BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val),
                   requests_received_this_epoch := []);

        var cnewEpochLength := UpperBoundedAdditionImpl(ces.epoch_length, ces.epoch_length, ces.constants.all.params.max_integer_val);
        var cnewEpochEndTime := UpperBoundedAdditionImpl(clock, cnewEpochLength, ces.constants.all.params.max_integer_val);

        var new_seq := ces.requests_received_prev_epochs + ces.requests_received_this_epoch;
        ghost var new_set := ces.prev_req_set + ces.cur_req_set;
        prev_req_set.AddSet(cur_req_set);
        cur_req_set.RemoveAll();
        assert HeadersMatch(new_seq, new_set);
        var tuple := BoundCRequestSequence(new_seq, ces.constants.all.params.max_integer_val);
        var bounded, bounded_seq := tuple.0, tuple.1;
        if bounded { // Should never happen
          new_set := BoundCRequestHeaders(new_seq, new_set, ces.constants.all.params.max_integer_val, prev_req_set);
        }
        ces' := ces.( //CElectionStateValueSetsReflectNewView(ces)
          current_view := cp.msg.bal_heartbeat,
          current_view_suspectors := (if cp.msg.suspicious then [index] else []),
          epoch_length := cnewEpochLength,
          epoch_end_time := cnewEpochEndTime,
          requests_received_prev_epochs := bounded_seq,
          requests_received_this_epoch := [],
          cur_req_set := {},
          prev_req_set := new_set);

        lemma_AbstractifyCRequestsSeqToRequestsSeq_concat(ces.requests_received_prev_epochs, ces.requests_received_this_epoch);
        lemma_BoundCRequestSequence(ces.requests_received_prev_epochs + ces.requests_received_this_epoch, ces.constants.all.params.max_integer_val);
        forall ensures SeqIsUnique(ces'.current_view_suspectors)
        {
          reveal SeqIsUnique();
        }
        calc {
          AbstractifySeqOfUint64sToSetOfInts(ces'.current_view_suspectors);
            { assert index as int == sender_index; reveal AbstractifySeqOfUint64sToSetOfInts();
          lemma_AbstractifySeqOfUint64sToSetOfInts_properties(ces'.current_view_suspectors); }
          es'.current_view_suspectors;
        }

        assert Eq_ElectionState(es', AbstractifyCElectionStateToElectionState(ces'));
      } else {
        es' := es;
        ces' := ces;
      }
    }
    reveal AbstractifyEndPointsToNodeIdentities();
  }
  assert Eq_ElectionState(es', AbstractifyCElectionStateToElectionState(ces'));
}

method {:timeLimitMultiplier 3} ElectionCheckForViewTimeout(ces:CElectionState, clock:uint64, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (ces':CElectionState)
  requires CElectionStateIsValid(ces)
  requires MutableSet.SetOf(cur_req_set) == ces.cur_req_set
  requires MutableSet.SetOf(prev_req_set) == ces.prev_req_set
  modifies cur_req_set, prev_req_set
  ensures  CElectionStateIsValid(ces')
  ensures  ElectionStateCheckForViewTimeout(AbstractifyCElectionStateToElectionState(ces), AbstractifyCElectionStateToElectionState(ces'), clock as int)
  ensures MutableSet.SetOf(cur_req_set) == ces'.cur_req_set
  ensures MutableSet.SetOf(prev_req_set) == ces'.prev_req_set
{
  var start_time := Time.GetDebugTimeTicks();
  ghost var es := AbstractifyCElectionStateToElectionState(ces);
  ghost var es':ElectionState;
  lemma_AbstractifySeqOfUint64sToSetOfInts_properties(ces.current_view_suspectors);

  if clock < ces.epoch_end_time {
    es' := es;
    ces' := ces;
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("ElectionCheckForViewTimeout_nada", start_time, end_time);
    assert Eq_ElectionState(es', AbstractifyCElectionStateToElectionState(ces'));
  } else if |ces.requests_received_prev_epochs| == 0 {
    ghost var new_epoch_length := es.constants.all.params.baseline_view_timeout_period;
    es' := es.(epoch_length := new_epoch_length,
               epoch_end_time := UpperBoundedAddition(clock as int, new_epoch_length, es.constants.all.params.max_integer_val),
               requests_received_prev_epochs := es.requests_received_this_epoch,
               requests_received_this_epoch := []);

    var cnewEpochLength := ces.constants.all.params.baseline_view_timeout_period;
    var cnewEpochEndTime := UpperBoundedAdditionImpl(clock, cnewEpochLength, ces.constants.all.params.max_integer_val);
    ces' := ces.(epoch_length := cnewEpochLength,
                 epoch_end_time := cnewEpochEndTime,
                 requests_received_prev_epochs := ces.requests_received_this_epoch,
                 requests_received_this_epoch := [],
                 cur_req_set := {},
                 prev_req_set := ces.cur_req_set);
    prev_req_set.TransferSet(cur_req_set);
    assert Eq_ElectionState(es', AbstractifyCElectionStateToElectionState(ces'));
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("ElectionCheckForViewTimeout_noprev", start_time, end_time);
  } else {
    es' := es.(current_view_suspectors := es.current_view_suspectors + {es.constants.my_index},
               epoch_end_time := UpperBoundedAddition(clock as int, es.epoch_length, es.constants.all.params.max_integer_val),
               requests_received_prev_epochs := BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val),
               requests_received_this_epoch := []);

    var cnewEpochEndTime := UpperBoundedAdditionImpl(clock, ces.epoch_length, ces.constants.all.params.max_integer_val);

    var new_seq := ces.requests_received_prev_epochs + ces.requests_received_this_epoch;
    ghost var new_set := ces.prev_req_set + ces.cur_req_set;
    prev_req_set.AddSet(cur_req_set);
    cur_req_set.RemoveAll();
    assert HeadersMatch(new_seq, new_set);
    var tuple := BoundCRequestSequence(new_seq, ces.constants.all.params.max_integer_val);
    var bounded, bounded_seq := tuple.0, tuple.1;
    if bounded { // Should never happen
      new_set := BoundCRequestHeaders(new_seq, new_set, ces.constants.all.params.max_integer_val, prev_req_set);
    }

    ces' := ces.(current_view_suspectors := AppendToUniqueSeqMaybe(ces.current_view_suspectors, ces.constants.my_index),
                 epoch_end_time := cnewEpochEndTime,
                 requests_received_prev_epochs := bounded_seq,
                 requests_received_this_epoch := [],
                 cur_req_set := {},
                 prev_req_set := new_set);

    lemma_AbstractifyCRequestsSeqToRequestsSeq_concat(ces.requests_received_prev_epochs, ces.requests_received_this_epoch);
    lemma_BoundCRequestSequence(ces.requests_received_prev_epochs + ces.requests_received_this_epoch, ces.constants.all.params.max_integer_val);
    calc {
      AbstractifySeqOfUint64sToSetOfInts(AppendToUniqueSeqMaybe(ces.current_view_suspectors, ces.constants.my_index));
        { lemma_AbstractifySeqOfUint64sToSetOfInts_append(ces.current_view_suspectors, ces.constants.my_index); }
      es.current_view_suspectors + {es.constants.my_index};
    }

    assert Eq_ElectionState(es', AbstractifyCElectionStateToElectionState(ces'));
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("ElectionCheckForViewTimeout_timeout", start_time, end_time);
  } 

  assert Eq_ElectionState(es', AbstractifyCElectionStateToElectionState(ces'));
}

method {:timeLimitMultiplier 3} ElectionCheckForQuorumOfViewSuspicions(ces:CElectionState, clock:uint64, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns(ces':CElectionState)
  requires CElectionStateIsValid(ces)
  requires MutableSet.SetOf(cur_req_set) == ces.cur_req_set
  requires MutableSet.SetOf(prev_req_set) == ces.prev_req_set
  modifies cur_req_set, prev_req_set
  ensures  CElectionStateIsValid(ces')
  ensures  ElectionStateCheckForQuorumOfViewSuspicions(AbstractifyCElectionStateToElectionState(ces), AbstractifyCElectionStateToElectionState(ces'), clock as int)
  ensures MutableSet.SetOf(cur_req_set) == ces'.cur_req_set
  ensures MutableSet.SetOf(prev_req_set) == ces'.prev_req_set
{
  reveal SeqIsUnique();
  ghost var es := AbstractifyCElectionStateToElectionState(ces);
  ghost var es':ElectionState;
  lemma_AbstractifySeqOfUint64sToSetOfInts_properties(ces.current_view_suspectors);
  lemma_AbstractifyEndPointsToNodeIdentities_properties(ces.constants.all.config.replica_ids);

  var minq := MinCQuorumSize(ces.constants.all.config);
  if |ces.current_view_suspectors| < minq as int || ces.current_view.seqno >= ces.constants.all.params.max_integer_val { //|| |ces.constants.all.config.replica_ids| == 0 {
    es' := es;
    ces' := ces;
  } else {
    ghost var new_epoch_length := UpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val);
    es' := es.(
      current_view := ComputeSuccessorView(es.current_view, es.constants.all),
      current_view_suspectors := {},
      epoch_length := new_epoch_length,
      epoch_end_time := UpperBoundedAddition(clock as int, new_epoch_length, es.constants.all.params.max_integer_val),
      requests_received_prev_epochs := BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val),
      requests_received_this_epoch := []);

    var cview := CComputeSuccessorView(ces.current_view, ces.constants.all);
    var cnewEpochLength := UpperBoundedAdditionImpl(ces.epoch_length, ces.epoch_length, ces.constants.all.params.max_integer_val);
    var cnewEpochEndTime := UpperBoundedAdditionImpl(clock, cnewEpochLength, ces.constants.all.params.max_integer_val);

    var new_seq := ces.requests_received_prev_epochs + ces.requests_received_this_epoch;
    ghost var new_set := ces.prev_req_set + ces.cur_req_set;
    prev_req_set.AddSet(cur_req_set);
    cur_req_set.RemoveAll();
    assert HeadersMatch(new_seq, new_set);
    var tuple := BoundCRequestSequence(new_seq, ces.constants.all.params.max_integer_val);
    var bounded, bounded_seq := tuple.0, tuple.1;
    if bounded { // Should never happen
      new_set := BoundCRequestHeaders(new_seq, new_set, ces.constants.all.params.max_integer_val, prev_req_set);
    }

    ces' := ces.(
            current_view := cview,
            current_view_suspectors := [],
            epoch_length := cnewEpochLength,
            epoch_end_time := cnewEpochEndTime,
            requests_received_prev_epochs := bounded_seq,
            requests_received_this_epoch := [],
            cur_req_set := {},
            prev_req_set := new_set);
    lemma_AbstractifyCRequestsSeqToRequestsSeq_concat(ces.requests_received_prev_epochs, ces.requests_received_this_epoch);
    lemma_BoundCRequestSequence(ces.requests_received_prev_epochs + ces.requests_received_this_epoch, ces.constants.all.params.max_integer_val);
  }
  reveal AbstractifyEndPointsToNodeIdentities();
  lemma_AbstractifySeqOfUint64sToSetOfInts_properties([]);
  assert Eq_ElectionState(es', AbstractifyCElectionStateToElectionState(ces'));
}

/*
method FindEarlierRequest(r1:seq<CRequest>, r2:seq<CRequest>, target:CRequest) returns (b:bool)
  requires CRequestsSeqIsAbstractable(r1)
  requires CRequestsSeqIsAbstractable(r2)
  requires CRequestIsAbstractable(target)
  requires |r1| < 0x1_0000_0000_0000_0000
  requires |r2| < 0x1_0000_0000_0000_0000
  ensures  b == exists earlier_req :: (earlier_req in r1 || earlier_req in r2)
                                     && CRequestsMatch(earlier_req, target)
  ensures  b == exists earlier_req :: (earlier_req in AbstractifyCRequestsSeqToRequestsSeq(r1) 
                                         || earlier_req in AbstractifyCRequestsSeqToRequestsSeq(r2))
                                     && RequestsMatch(earlier_req, AbstractifyCRequestToRequest(target))
{
  lemma_CRequestsMatch();

  var i:uint64 := 0;
  while i < |r1| as uint64
    invariant 0 <= i as int <= |r1|
    invariant forall j :: 0 <= j < i ==> !CRequestsMatch(r1[j], target)
  {
    if CRequestsMatch(r1[i], target) {
      b := true;
      return;
    }
    i := i + 1;
  }

  i := 0;
  while i < |r2| as uint64
    invariant 0 <= i as int <= |r2|
    invariant forall j :: 0 <= j < i ==> !CRequestsMatch(r2[j], target)
  {
    if CRequestsMatch(r2[i], target) {
      b := true;
      return;
    }
    i := i + 1;
  }

  b := false;
}
*/

method FindEarlierRequestSets(ces:CElectionState, target:CRequest, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (b:bool)
  requires CElectionStateIsValid(ces)
  requires CRequestIsAbstractable(target)
  requires MutableSet.SetOf(cur_req_set) == ces.cur_req_set
  requires MutableSet.SetOf(prev_req_set) == ces.prev_req_set
  ensures  b == exists earlier_req :: (earlier_req in ces.requests_received_prev_epochs 
                                         || earlier_req in ces.requests_received_this_epoch)
                                     && CRequestsMatch(earlier_req, target)
  ensures  b == exists earlier_req :: (earlier_req in AbstractifyCRequestsSeqToRequestsSeq(ces.requests_received_prev_epochs) 
                                         || earlier_req in AbstractifyCRequestsSeqToRequestsSeq(ces.requests_received_this_epoch))
                                     && RequestsMatch(earlier_req, AbstractifyCRequestToRequest(target))
{
  var header := CRequestHeader(target.client, target.seqno);
  var b1 := cur_req_set.Contains(header);
  if b1 {
    b := true;
  } else {
    var b2 := prev_req_set.Contains(header);
    b := b2;
  }
  assert b == (header in ces.cur_req_set) || (header in ces.prev_req_set);
  lemma_CRequestsMatch();
  if b {
    ghost var requests := ces.requests_received_prev_epochs + ces.requests_received_this_epoch;
    ghost var i := FindMatchingRequest(requests, ces.prev_req_set + ces.cur_req_set, header); 
    // Lots of OBSERVE below to satisfy the existential in the ensures clause
    if i < |ces.requests_received_prev_epochs| {
      assert requests[i] == ces.requests_received_prev_epochs[i];
      ghost var r_req := AbstractifyCRequestToRequest(ces.requests_received_prev_epochs[i]);
      assert r_req in AbstractifyCRequestsSeqToRequestsSeq(ces.requests_received_prev_epochs);
      assert RequestsMatch(r_req, AbstractifyCRequestToRequest(target));
    } else {
      assert requests[i] == ces.requests_received_this_epoch[i - |ces.requests_received_prev_epochs|];
      ghost var r_req := AbstractifyCRequestToRequest(ces.requests_received_this_epoch[i - |ces.requests_received_prev_epochs|]);
      assert r_req in AbstractifyCRequestsSeqToRequestsSeq(ces.requests_received_this_epoch);
      assert RequestsMatch(r_req, AbstractifyCRequestToRequest(target));
    }
  }
}

lemma lemma_HeadersMatchAddition(requests:seq<CRequest>, headers:set<CRequestHeader>, req:CRequest)
  requires HeadersMatch(requests, headers)
  requires !(exists earlier_req :: earlier_req in requests && CRequestsMatch(earlier_req, req))
  ensures  HeadersMatch(requests + [req], headers + { CRequestHeader(req.client, req.seqno) })
{
  var header := CRequestHeader(req.client, req.seqno);
  if header in headers {
    ghost var i := FindMatchingRequest(requests, headers, header); 
    assert requests[i] in requests && CRequestsMatch(requests[i], req);
  }
  assert !(header in headers);
}

function ExtractHeader(req:CRequest) : CRequestHeader
{
  CRequestHeader(req.client, req.seqno)
}

lemma lemma_AddNewReqPreservesHeaderMatches(s1:seq<CRequest>,  headers1:set<CRequestHeader>, 
                                            s2:seq<CRequest>,  headers2:set<CRequestHeader>,
                                            s1':seq<CRequest>, headers1':set<CRequestHeader>,
                                            s2':seq<CRequest>, headers2':set<CRequestHeader>,
                                            r:CRequest)
  requires HeadersMatch(s1, headers1)
  requires HeadersMatch(s2, headers2)
  requires HeadersMatch(s1 + s2, headers1 + headers2)
  requires HeadersMatch(s1', headers1')
  requires HeadersMatch(s2', headers2')
  requires headers1' == headers1;
  requires s1' == s1
  requires forall req :: req in s2' && !CRequestsMatch(req, r) ==> req in s2
  requires forall h :: h in headers2' && h != CRequestHeader(r.client, r.seqno) ==> h in headers2
  requires forall other_r :: other_r in s1 || other_r in s2 ==> !CRequestsMatch(other_r, r)
  ensures  HeadersMatch(s1' + s2', headers1' + headers2')
{
  var total_s := s1' + s2'; 
  var total_h := headers1' + headers2'; 
  forall i,j | 0 <= i < j < |total_s| && CRequestsMatch(total_s[i], total_s[j]) 
    ensures i == j
  {
    if j < |s1'| {
      assert total_s[i] in s1 && total_s[j] in s1;
      assert i == j;
    } else if i >= |s1'| {
      assert total_s[i] in s2 && total_s[j] in s2;
      assert i == j;
    } else {
      assert i < |s1'| && j >= |s1'|;
      assert total_s[i] in s1 && total_s[j] in s2;
      var tot_s := s1 + s2;
      assert total_s[i] in tot_s && total_s[j] in tot_s;
      var i' :| 0 <= i' < |tot_s| && total_s[i] == tot_s[i'];
      var j' :| 0 <= j' < |tot_s| && total_s[j] == tot_s[j'];
      assert HeadersMatch(tot_s, headers1 + headers2);
      if (i' < j') {
        assert CRequestsMatch(tot_s[i'], tot_s[j']);
      } else if (i' > j') {
        assert CRequestsMatch(tot_s[j'], tot_s[i']);
      }
      assert i' == j';
      assert total_s[i] == total_s[j];
      if (total_s[j] in s1) {
        i' :| 0 <= i' < |s1| && total_s[j] == s1[i'];
        j' :| 0 <= j' < |s2| && total_s[j] == s2[j'];
        assert total_s[j] == tot_s[i'];
        assert total_s[j] == tot_s[|s1| + j'];
      }
      assert total_s[j] !in s1;
      assert i == j;
    }
  }

  var header_seq := [];
  var i := 0;
  while i < |total_s|
    invariant 0 <= i <= |total_s|
    invariant |header_seq| == i
    invariant forall j :: 0 <= j < i ==> header_seq[j] == ExtractHeader(total_s[j])
  {
    header_seq := header_seq + [ExtractHeader(total_s[i])];
    i := i + 1;
  }
    
  forall i', j' | 0 <= i' < |header_seq| && 0 <= j' < |header_seq| && header_seq[i'] == header_seq[j']
    ensures i' == j'
  {
    assert header_seq[i'] == ExtractHeader(total_s[i']);
    assert header_seq[j'] == ExtractHeader(total_s[j']);
    if i' < j' {
      assert CRequestsMatch(total_s[i'], total_s[j']);  // OBSERVE
    } else if j' < i' {
      assert CRequestsMatch(total_s[j'], total_s[i']);  // OBSERVE
    }
  }
  forall ensures SeqIsUnique(header_seq)
  {
    reveal SeqIsUnique();
  }

  //var headers := set r | r in total_s :: ExtractHeader(r);
  var header_set := UniqueSeqToSet(header_seq);
  lemma_seqs_set_cardinality(header_seq, header_set);
  forall h | h in header_set
    ensures h in total_h
  {
  }

  forall h | h in total_h
    ensures h in header_set
  {
    if h in headers1' {
      var j := FindMatchingRequest(s1', headers1', h); 
      assert total_s[j] == s1'[j];
      assert header_seq[j] == ExtractHeader(total_s[j]);
      assert header_seq[j] == h;
      assert header_seq[j] in header_seq;
      assert header_seq[j] in header_set;
    } else {
      assert h in headers2';
      var j := FindMatchingRequest(s2', headers2', h); 
      var j_offset := j + |s1'|;
      assert total_s[j_offset] == s2'[j];
      assert header_seq[j_offset] == ExtractHeader(total_s[j_offset]);
      assert header_seq[j_offset] == h;
      assert header_seq[j_offset] in header_seq;
      assert header_seq[j_offset] in header_set;
    }
  }
  lemma_MapSetCardinalityOver(total_h, header_set, h => h);
  assert |total_h| == |header_set|;       // OBSERVE
}

method {:timeLimitMultiplier 10} ElectionReflectReceivedRequest(ces:CElectionState, creq:CRequest, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (ces':CElectionState)
  requires CElectionStateIsValid(ces)
  requires CRequestIsAbstractable(creq)
  requires ValidRequest(creq)
  requires prev_req_set != cur_req_set
  requires MutableSet.SetOf(cur_req_set) == ces.cur_req_set
  requires MutableSet.SetOf(prev_req_set) == ces.prev_req_set
  modifies cur_req_set
  ensures  CElectionStateIsValid(ces')
  ensures  ElectionStateReflectReceivedRequest(AbstractifyCElectionStateToElectionState(ces), AbstractifyCElectionStateToElectionState(ces'), AbstractifyCRequestToRequest(creq))
  ensures MutableSet.SetOf(cur_req_set) == ces'.cur_req_set
  ensures MutableSet.SetOf(prev_req_set) == ces'.prev_req_set
{
  ghost var req := AbstractifyCRequestToRequest(creq);
  ghost var es  := AbstractifyCElectionStateToElectionState(ces);
  ghost var es':ElectionState;

  //var earlier_start_time := Time.GetDebugTimeTicks();
  //var earlier:bool := FindEarlierRequest(ces.requests_received_this_epoch, ces.requests_received_prev_epochs, creq);
  var earlier:bool := FindEarlierRequestSets(ces, creq, cur_req_set, prev_req_set);
  //var earlier_end_time := Time.GetDebugTimeTicks();
  //RecordTimingSeq("ElectionReflectReceivedRequest_FindEarlier", earlier_start_time, earlier_end_time);

  if earlier {
    es' := es;
    ces' := ces;
  } else {
    //var update_start_time := Time.GetDebugTimeTicks();
    es' := es.(requests_received_this_epoch := BoundRequestSequence(es.requests_received_this_epoch + [req], es.constants.all.params.max_integer_val));
    var new_seq := ces.requests_received_this_epoch + [creq];
    var header := CRequestHeader(creq.client, creq.seqno);
    ghost var new_set := ces.cur_req_set + { header };
    cur_req_set.Add(header);
    lemma_HeadersMatchAddition(ces.requests_received_this_epoch, ces.cur_req_set, creq);
    assert HeadersMatch(new_seq, new_set);
    var tuple := BoundCRequestSequence(new_seq, ces.constants.all.params.max_integer_val);
    var bounded, bounded_seq := tuple.0, tuple.1;
    if bounded { // Should never happen
      new_set := BoundCRequestHeaders(new_seq, new_set, ces.constants.all.params.max_integer_val, cur_req_set);
    }
    ces' := ces.(requests_received_this_epoch := bounded_seq, cur_req_set := new_set);

    lemma_AddNewReqPreservesHeaderMatches(ces.requests_received_prev_epochs, ces.prev_req_set,
                                          ces.requests_received_this_epoch,  ces.cur_req_set,
                                          ces.requests_received_prev_epochs, ces.prev_req_set,
                                          bounded_seq, new_set,
                                          creq);
    lemma_AbstractifyCRequestsSeqToRequestsSeq_concat(ces.requests_received_this_epoch, [creq]);
    lemma_BoundCRequestSequence(bounded_seq, ces.constants.all.params.max_integer_val);

    assert {:split_here} true;

    assert Eq_ElectionState(es', AbstractifyCElectionStateToElectionState(ces'));
  }
}

lemma lemma_SequenceRemoveAllSatisfied(rseq:seq<Request>, batch:RequestBatch, i:int, rseq':seq<Request>, rseq'':seq<Request>)
  requires 0 <= i < |batch|
  requires rseq' == RemoveExecutedRequestBatch(rseq, batch[..i])
  requires rseq'' == RemoveAllSatisfiedRequestsInSequence(rseq', batch[i])
  ensures rseq'' == RemoveExecutedRequestBatch(rseq, batch[..i+1])
  decreases i
{
  if i > 0 {
    assert batch[1..][..i-1] == batch[1..i]; 
    assert batch[1..][..i] == batch[1..i+1]; 
    var rseqalt := RemoveAllSatisfiedRequestsInSequence(rseq, batch[0]);
    var rseqalt' := RemoveExecutedRequestBatch(rseqalt, batch[1..i]);
    var rseqalt'' := RemoveAllSatisfiedRequestsInSequence(rseqalt', batch[i]);

    lemma_SequenceRemoveAllSatisfied(rseqalt, batch[1..], i-1, rseqalt', rseqalt''); 
  }
}

method {:timeLimitMultiplier 3} ElectionReflectExecutedRequestBatch(ces:CElectionState, creqb:CRequestBatch, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (ces':CElectionState)
  requires CElectionStateIsValid(ces)
  requires CRequestBatchIsAbstractable(creqb)
  requires ValidRequestBatch(creqb)
  requires cur_req_set != prev_req_set
  requires MutableSet.SetOf(cur_req_set) == ces.cur_req_set
  requires MutableSet.SetOf(prev_req_set) == ces.prev_req_set
  modifies cur_req_set, prev_req_set
  ensures  CElectionStateIsValid(ces')
  ensures  ElectionStateReflectExecutedRequestBatch(AbstractifyCElectionStateToElectionState(ces), AbstractifyCElectionStateToElectionState(ces'), AbstractifyCRequestBatchToRequestBatch(creqb))
  ensures MutableSet.SetOf(cur_req_set) == ces'.cur_req_set
  ensures MutableSet.SetOf(prev_req_set) == ces'.prev_req_set
  decreases |creqb|
{
  ghost var es  := AbstractifyCElectionStateToElectionState(ces);
  var i:uint64 := 0;
  assert AbstractifyCRequestBatchToRequestBatch(creqb[..i]) == [];
  var tempces' := ces;

  while i < |creqb| as uint64
    invariant 0 <= i as int <= |creqb|
    invariant CElectionStateIsAbstractable(tempces')
    invariant CElectionStateIsValid(tempces')
    invariant ElectionStateReflectExecutedRequestBatch(es, AbstractifyCElectionStateToElectionState(tempces'), AbstractifyCRequestBatchToRequestBatch(creqb[..i]))
    invariant MutableSet.SetOf(cur_req_set) == tempces'.cur_req_set
    invariant MutableSet.SetOf(prev_req_set) == tempces'.prev_req_set
  { 
    var creq := creqb[i];
    ghost var req := AbstractifyCRequestToRequest(creq);
    ghost var es':ElectionState := AbstractifyCElectionStateToElectionState(tempces');
       
    lemma_RemoveAllSatisfiedCRequestsInSequenceProperties(tempces'.requests_received_prev_epochs, creq);
    lemma_RemoveAllSatisfiedCRequestsInSequenceProperties(tempces'.requests_received_this_epoch, creq);

    assert ElectionStateReflectExecutedRequestBatch(es, AbstractifyCElectionStateToElectionState(tempces'), AbstractifyCRequestBatchToRequestBatch(creqb[..i]));
    ghost var es'' := es'.(requests_received_prev_epochs := RemoveAllSatisfiedRequestsInSequence(es'.requests_received_prev_epochs, req),
                           requests_received_this_epoch := RemoveAllSatisfiedRequestsInSequence(es'.requests_received_this_epoch, req));

    var prevEpoch;
    ghost var prevEpochSet;
    prevEpoch, prevEpochSet := RemoveAllSatisfiedCRequestsInSequenceIter(tempces'.requests_received_prev_epochs, tempces'.prev_req_set, prev_req_set, creq);
    var thisEpoch; 
    ghost var thisEpochSet;
    thisEpoch, thisEpochSet := RemoveAllSatisfiedCRequestsInSequenceIter(tempces'.requests_received_this_epoch, tempces'.cur_req_set, cur_req_set, creq);


    lemma_RemoveAllSatisfiedPreservesHeaderMatches(tempces'.requests_received_prev_epochs, tempces'.prev_req_set,
                                                   tempces'.requests_received_this_epoch, tempces'.cur_req_set,
                                                   prevEpoch, prevEpochSet,
                                                   thisEpoch, thisEpochSet,
                                                   creq);

    tempces' := tempces'.(requests_received_prev_epochs := prevEpoch,
                          requests_received_this_epoch := thisEpoch,
                          cur_req_set := thisEpochSet,
                          prev_req_set := prevEpochSet);
    assert {:split_here} true;
    assert AbstractifyCRequestBatchToRequestBatch(creqb[..i]) == AbstractifyCRequestBatchToRequestBatch(creqb)[..i];
    assert AbstractifyCRequestBatchToRequestBatch(creqb[..i+1]) == AbstractifyCRequestBatchToRequestBatch(creqb)[..i+1];
    lemma_SequenceRemoveAllSatisfied(es.requests_received_prev_epochs, AbstractifyCRequestBatchToRequestBatch(creqb), i as int, es'.requests_received_prev_epochs, es''.requests_received_prev_epochs);
    lemma_SequenceRemoveAllSatisfied(es.requests_received_this_epoch, AbstractifyCRequestBatchToRequestBatch(creqb), i as int, es'.requests_received_this_epoch, es''.requests_received_this_epoch);
    i := i + 1;
  }
  assert creqb[..i] == creqb;
  ces' := tempces';
}

} 

