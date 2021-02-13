include "../../Protocol/RSL/Types.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../../Common/Native/NativeTypes.i.dfy"
include "AppInterface.i.dfy"
include "../Common/Util.i.dfy"
include "../Common/GenericRefinement.i.dfy"
include "../../Common/Collections/Sets.i.dfy"

module LiveRSL__CTypes_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Native__NativeTypes_i
import opened LiveRSL__AppInterface_i
import opened LiveRSL__Types_i
import opened Common__NodeIdentity_i
import opened Common__UdpClient_i
import opened Common__Util_i
import opened Collections__Maps_i
import opened Collections__Sets_i
import opened GenericRefinement_i
import opened Concrete_NodeIdentity_i

//////////////////////////////////////////////////////////////////////////////
// Ballot

// Note: proposer_id is now an index into the shared configuration, not a Uint64 representation of an EndPoint
datatype CBallot = CBallot(seqno:uint64, proposer_id:uint64)

function method BallotSize() : uint64 { Uint64Size() + Uint64Size() }

function method CBallotIsLessThan(lhs:CBallot, rhs:CBallot) : bool
{
  || lhs.seqno < rhs.seqno
  || (lhs.seqno == rhs.seqno && lhs.proposer_id < rhs.proposer_id)
}

function method CBallotIsNotGreaterThan(lhs:CBallot, rhs:CBallot) : bool
{
  || lhs.seqno < rhs.seqno
  || (lhs.seqno == rhs.seqno && lhs.proposer_id <= rhs.proposer_id)
}

predicate CBallotIsAbstractable(ballot:CBallot)
{
  && ballot.CBallot?     // OBSERVE: Always true, but seems necessary to avoid errors below
  && ballot.proposer_id <= 0xFFFF_FFFF_FFFF_FFFF // We don't support more than 2^64-1 replicas.  Such is life.
  //&& EndPointUint64Representation(ballot.proposer_id)
}

function AbstractifyCBallotToBallot(ballot:CBallot) : Ballot
  // the specification of the ballot does not account for a null state.
  requires CBallotIsAbstractable(ballot)
{
  //Ballot(int(ballot.seqno), AbstractifyUint64ToNodeIdentity(ballot.proposer_id))
  Ballot(ballot.seqno as int, ballot.proposer_id as int)
}


predicate CCBalLeq(ba:CBallot, bb:CBallot)
  requires CBallotIsAbstractable(ba) && CBallotIsAbstractable(bb)
{
  BalLeq(AbstractifyCBallotToBallot(ba), AbstractifyCBallotToBallot(bb))
}

predicate CCBalLt(ba:CBallot, bb:CBallot)
  requires CBallotIsAbstractable(ba) && CBallotIsAbstractable(bb)
{
  BalLt(AbstractifyCBallotToBallot(ba), AbstractifyCBallotToBallot(bb))
}

method CBalLeq(ba:CBallot, bb:CBallot) returns (b:bool)
  requires CBallotIsAbstractable(ba) && CBallotIsAbstractable(bb)
  ensures b == BalLeq(AbstractifyCBallotToBallot(ba), AbstractifyCBallotToBallot(bb))
  ensures b == CCBalLeq(ba, bb)
{
  if (ba.seqno < bb.seqno || (ba.seqno == bb.seqno && ba.proposer_id <= bb.proposer_id)) {
    b := true;
  } else {
    b := false;
  }
}

method CBalLt(ba:CBallot, bb:CBallot) returns (b:bool)
  requires CBallotIsAbstractable(ba) && CBallotIsAbstractable(bb)
  ensures b == BalLt(AbstractifyCBallotToBallot(ba), AbstractifyCBallotToBallot(bb))
  ensures b == CCBalLt(ba, bb)
{
  if (ba.seqno < bb.seqno || (ba.seqno == bb.seqno && ba.proposer_id < bb.proposer_id)) {
    b := true;
  } else {
    b := false;
  }
}

lemma lemma_BallotInjective(b1:CBallot, b2:CBallot)
  requires CBallotIsAbstractable(b1)
  requires CBallotIsAbstractable(b2)
  requires AbstractifyCBallotToBallot(b1) == AbstractifyCBallotToBallot(b2)
  ensures b1 == b2
{
}

//////////////////////////////////////////////////////////////////////////////
// OperationNumber

datatype COperationNumber = COperationNumber(n:uint64)

function method OpNumSize()  : uint64 { Uint64Size() }

predicate COperationNumberIsAbstractable(opn:COperationNumber)
{
  opn.COperationNumber?     // OBSERVE: Always true, but seems necessary to avoid errors below
}

function AbstractifyCOperationNumberToOperationNumber(opn:COperationNumber) : OperationNumber
  // requires COperationNumberIsAbstractable(opn)
  ensures COperationNumberIsAbstractable(opn) ==> (0 <= AbstractifyCOperationNumberToOperationNumber(opn) <= 0xffff_ffff_ffff_ffff)
{
  opn.n as int
}

lemma lemma_AbstractifyCOperationNumberToOperationNumber_isInjective() 
  ensures forall opn1, opn2 :: COperationNumberIsAbstractable(opn1) && COperationNumberIsAbstractable(opn2) && AbstractifyCOperationNumberToOperationNumber(opn1) == AbstractifyCOperationNumberToOperationNumber(opn2) ==> opn1 == opn2
{
}

function AbstractifyCOperationNumbersToOperationNumbers(copns:set<COperationNumber>):set<OperationNumber>
  requires forall opn :: opn in copns ==> COperationNumberIsAbstractable(opn)
{
  set copn | copn in copns :: AbstractifyCOperationNumberToOperationNumber(copn)
}

lemma lemma_AbstractifyCOperationNumbersToOperationNumbers_maintainsSize(copns:set<COperationNumber>)
  requires forall opn :: opn in copns ==> COperationNumberIsAbstractable(opn)
  ensures  |copns| == |AbstractifyCOperationNumbersToOperationNumbers(copns)|
{
  var opns := AbstractifyCOperationNumbersToOperationNumbers(copns);
  lemma_AbstractifyCOperationNumberToOperationNumber_isInjective();

  var f := AbstractifyCOperationNumberToOperationNumber;
  assert forall x :: x in copns ==> f(x) in opns;
  forall opn1, opn2 | f(opn1) == f(opn2)
    ensures opn1 == opn2
  {
  }
  assert forall x :: f(x) in opns ==> x in copns;

  lemma_MapSetCardinality(copns, opns, f);
}


////////////////////////////////////////////////
//      CRequest
////////////////////////////////////////////////

datatype CRequest = CRequest(client:EndPoint, seqno:uint64, request:CAppMessage)

predicate method ValidRequest(c:CRequest)
{
  c.CRequest? ==> EndPointIsValidIPV4(c.client) && ValidAppMessage(c.request)
}

predicate CRequestIsAbstractable(c:CRequest)
{
  EndPointIsValidIPV4(c.client) && CAppMessageIsAbstractable(c.request)
}

function AbstractifyCRequestToRequest(c:CRequest) : Request
  requires CRequestIsAbstractable(c)
{
  Request(AbstractifyEndPointToNodeIdentity(c.client), c.seqno as int, AbstractifyCAppMessageToAppMessage(c.request))  
}

lemma lemma_AbstractifyCRequestToRequest_isInjective()
  ensures forall v1, v2 :: CRequestIsAbstractable(v1) && CRequestIsAbstractable(v2) && AbstractifyCRequestToRequest(v1) == AbstractifyCRequestToRequest(v2) ==> v1 == v2
{
//  assert forall u1:uint64, u2:uint64 :: u1 as int == u2 as int ==> u1 == u2;
  lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
  lemma_Uint64EndPointRelationships();
}


predicate CRequestsSeqIsAbstractable(cvals:seq<CRequest>)
{
  forall cval :: cval in cvals ==> CRequestIsAbstractable(cval)
}


function {:opaque} AbstractifyCRequestsSeqToRequestsSeq(cvals:seq<CRequest>) : seq<Request>
  requires CRequestsSeqIsAbstractable(cvals)
  ensures |cvals| == |AbstractifyCRequestsSeqToRequestsSeq(cvals)|
  ensures forall i {:trigger AbstractifyCRequestsSeqToRequestsSeq(cvals)[i]} :: 0 <= i < |cvals| ==> AbstractifyCRequestToRequest(cvals[i]) == AbstractifyCRequestsSeqToRequestsSeq(cvals)[i]
  ensures  forall c :: CRequestIsAbstractable(c) ==> (c in cvals <==> AbstractifyCRequestToRequest(c) in AbstractifyCRequestsSeqToRequestsSeq(cvals))
{   
  lemma_AbstractifyCRequestToRequest_isInjective();
  if |cvals| == 0 then []
  else [AbstractifyCRequestToRequest(cvals[0])] + AbstractifyCRequestsSeqToRequestsSeq(cvals[1..])
}

lemma lemma_SequenceIndexing<T>(s:seq<T>, s':seq<T>, index:int)
  requires |s| <= index < |s| + |s'|
  ensures  (s + s')[index] == s'[index - |s|]
{
}

lemma lemma_AbstractifyCRequestsSeqToRequestsSeq_concat(r1:seq<CRequest>, r2:seq<CRequest>)
  requires CRequestsSeqIsAbstractable(r1)
  requires CRequestsSeqIsAbstractable(r2)
  ensures  AbstractifyCRequestsSeqToRequestsSeq(r1) + AbstractifyCRequestsSeqToRequestsSeq(r2) == AbstractifyCRequestsSeqToRequestsSeq(r1 + r2)
  ensures  CRequestsSeqIsAbstractable(r1 + r2)
{
  if |r1| == 0 {

  } else {
    var r_cat := AbstractifyCRequestsSeqToRequestsSeq(r1) + AbstractifyCRequestsSeqToRequestsSeq(r2);
    forall i | 0 <= i < |AbstractifyCRequestsSeqToRequestsSeq(r1 + r2)|
      ensures (r_cat)[i] == AbstractifyCRequestsSeqToRequestsSeq(r1 + r2)[i]
    {
      assert AbstractifyCRequestsSeqToRequestsSeq(r1 + r2)[i] == AbstractifyCRequestToRequest((r1+r2)[i]);
      if i < |r1| {
        assert (r1+r2)[i] == r1[i];
      } else {
        lemma_SequenceIndexing(r1, r2, i); 
        assert (r1+r2)[i] == r2[i-|r1|];
      }
    }
  }
}

lemma lemma_AbstractifyCRequestsSeqToRequestsSeq_suffix(r:seq<CRequest>, n:int)
  requires 0 <= n <= |r|
  requires CRequestsSeqIsAbstractable(r)
  ensures AbstractifyCRequestsSeqToRequestsSeq(r[n..]) == AbstractifyCRequestsSeqToRequestsSeq(r)[n..]
  ensures AbstractifyCRequestsSeqToRequestsSeq(r[..n]) == AbstractifyCRequestsSeqToRequestsSeq(r)[..n]
{
}

////////////////////////////////////////////////
//      CRequestBatch
////////////////////////////////////////////////

type CRequestBatch = seq<CRequest>

function method RequestBatchSizeLimit() : int { 100 } //{ 0xFFFF }
    
predicate ValidRequestBatch(c:CRequestBatch)
{
  (forall cr :: cr in c ==> ValidRequest(cr)) && |c| <= RequestBatchSizeLimit()
}

predicate CRequestBatchIsAbstractable(c:CRequestBatch)
{
  CRequestsSeqIsAbstractable(c)
}

predicate CRequestBatchSeqIsAbstractable(s:seq<CRequestBatch>)
{
  forall cval :: cval in s ==> CRequestBatchIsAbstractable(cval)
}

function {:opaque} AbstractifyCRequestBatchToRequestBatch(cvals:CRequestBatch) : RequestBatch
  requires CRequestsSeqIsAbstractable(cvals)
  ensures |cvals| == |AbstractifyCRequestBatchToRequestBatch(cvals)|
  ensures forall i :: 0 <= i < |cvals| ==> AbstractifyCRequestToRequest(cvals[i]) == AbstractifyCRequestBatchToRequestBatch(cvals)[i]
  ensures  forall c :: CRequestIsAbstractable(c) ==> (c in cvals <==> AbstractifyCRequestToRequest(c) in AbstractifyCRequestBatchToRequestBatch(cvals))
{
  AbstractifyCRequestsSeqToRequestsSeq(cvals)
}

lemma lemma_AbstractifyCRequestBatchToRequestBatch_isInjective()
  ensures forall v1, v2 :: CRequestBatchIsAbstractable(v1) && CRequestBatchIsAbstractable(v2) && AbstractifyCRequestBatchToRequestBatch(v1) == AbstractifyCRequestBatchToRequestBatch(v2) ==> v1 == v2
{
  forall v1, v2 | CRequestBatchIsAbstractable(v1) && CRequestBatchIsAbstractable(v2) && AbstractifyCRequestBatchToRequestBatch(v1) == AbstractifyCRequestBatchToRequestBatch(v2)
    ensures v1 == v2
  {
    assert |v1| == |AbstractifyCRequestBatchToRequestBatch(v1)|;
    assert |v1| == |v2|;
    forall i | 0 <= i < |v1|
      ensures v1[i] == v2[i]
    {
      assert AbstractifyCRequestBatchToRequestBatch(v1)[i] == AbstractifyCRequestBatchToRequestBatch(v2)[i];
      lemma_AbstractifyCRequestToRequest_isInjective();
    }
    reveal AbstractifyCRequestBatchToRequestBatch();
  }
}

////////////////////////////////////////////////
//      CReply (Almost identical to CRequest)
////////////////////////////////////////////////
// Not yet in use.  Will be needed for the reply cache.  
datatype CReply   = CReply  (client:EndPoint, seqno:uint64, reply  :CAppMessage)

predicate method ValidReply(c:CReply)
{
  c.CReply? ==> EndPointIsValidIPV4(c.client) && ValidAppMessage(c.reply)
}

predicate CReplyIsAbstractable(c:CReply)
{
  EndPointIsValidIPV4(c.client) && CAppMessageIsAbstractable(c.reply)
}

function AbstractifyCReplyToReply(c:CReply) : Reply
  // requires CReplyIsAbstractable(c)
{
  Reply(AbstractifyEndPointToNodeIdentity(c.client), c.seqno as int, AbstractifyCAppMessageToAppMessage(c.reply))  
}

lemma lemma_AbstractifyCReplyToReply_isInjective()
  ensures forall v1, v2 :: CReplyIsAbstractable(v1) && CReplyIsAbstractable(v2) && AbstractifyCReplyToReply(v1) == AbstractifyCReplyToReply(v2) ==> v1 == v2
{
//  assert forall u1:uint64, u2:uint64 :: u1 as int == u2 as int ==> u1 == u2;
  lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
  lemma_Uint64EndPointRelationships();
}

predicate CReplySeqIsAbstractable(creplies:seq<CReply>)
{
  forall creply :: creply in creplies ==> CReplyIsAbstractable(creply)
}

function {:opaque} AbstractifyCReplySeqToReplySeq(s:seq<CReply>) : seq<Reply>
  requires CReplySeqIsAbstractable(s)
  ensures |AbstractifyCReplySeqToReplySeq(s)| == |s|
  ensures forall i :: 0 <= i < |AbstractifyCReplySeqToReplySeq(s)| ==> AbstractifyCReplySeqToReplySeq(s)[i] == AbstractifyCReplyToReply(s[i])
{
  if |s| == 0 then
    []
  else
    [AbstractifyCReplyToReply(s[0])] + AbstractifyCReplySeqToReplySeq(s[1..])
}

//////////////////////////////////////////////////////////////////////////////
// ReplyCache

type CReplyCache = map<EndPoint, CReply>

predicate CReplyCacheIsAbstractable(m:CReplyCache)
{
  forall e {:trigger EndPointIsValidIPV4(e)} :: e in m ==> EndPointIsValidIPV4(e) && CReplyIsAbstractable(m[e])
}

function max_reply_cache_size() : int { 256 } // 0x1_0000_0000

predicate ValidReplyCache(m:CReplyCache)
{
  && CReplyCacheIsAbstractable(m) && |m| < max_reply_cache_size()
  && (forall e {:trigger ValidReply(m[e])} :: e in m ==> ValidReply(m[e]))
}

function {:opaque} AbstractifyCReplyCacheToReplyCache(m:CReplyCache) : ReplyCache
  requires CReplyCacheIsAbstractable(m)
{
  assert forall e :: e in m ==> EndPointIsValidIPV4(e);
  lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
  // var test:CReply->Reply := (AbstractifyCReplyToReply as CReply->Reply);
  AbstractifyMap(m, AbstractifyEndPointToNodeIdentity, AbstractifyCReplyToReply, RefineNodeIdentityToEndPoint)
}

lemma lemma_AbstractifyCReplyCacheToReplyCache_properties(m:CReplyCache)
  requires CReplyCacheIsAbstractable(m)
  ensures  m == map [] ==> AbstractifyCReplyCacheToReplyCache(m) == map []
  ensures  forall e {:trigger e in m}{:trigger e in AbstractifyCReplyCacheToReplyCache(m)} :: (e in m <==> EndPointIsValidIPV4(e) && e in AbstractifyCReplyCacheToReplyCache(m))
  ensures  forall e :: (e !in m && EndPointIsValidIPV4(e) ==> e !in AbstractifyCReplyCacheToReplyCache(m))
  ensures  forall e {:trigger AbstractifyCReplyToReply(m[e])}{:trigger AbstractifyCReplyCacheToReplyCache(m)[e]} :: e in m ==> AbstractifyCReplyCacheToReplyCache(m)[e] == AbstractifyCReplyToReply(m[e])
  ensures  forall re :: re in AbstractifyCReplyCacheToReplyCache(m) ==> re in m
  ensures  forall e, r :: EndPointIsValidIPV4(e) && ValidReply(r) ==> 
              var rm  := AbstractifyCReplyCacheToReplyCache(m);
              var rm' := AbstractifyCReplyCacheToReplyCache(m[e := r]);
              rm' == AbstractifyCReplyCacheToReplyCache(m)[AbstractifyEndPointToNodeIdentity(e) := AbstractifyCReplyToReply(r)]
  ensures forall e {:trigger RemoveElt(m,e)} :: 
              (EndPointIsValidIPV4(e) && NodeIdentityIsRefinable(AbstractifyEndPointToNodeIdentity(e))
               && RefineNodeIdentityToEndPoint(AbstractifyEndPointToNodeIdentity(e)) == e && e in m) ==>
          var rm  := AbstractifyCReplyCacheToReplyCache(m); 
          var rm' := AbstractifyCReplyCacheToReplyCache(RemoveElt(m, e));
          rm' == RemoveElt(rm, e)
{
  assert forall e :: e in m ==> EndPointIsValidIPV4(e);
  reveal AbstractifyCReplyCacheToReplyCache();
  lemma_AbstractifyMap_properties(m, AbstractifyEndPointToNodeIdentity, AbstractifyCReplyToReply, RefineNodeIdentityToEndPoint);
}


//////////////////////////////////////////////////////////////////////////////
// MapOfSeqNums


predicate MapOfSeqNumsIsAbstractable(m:map<EndPoint,uint64>)
{
  forall e :: e in m ==> EndPointIsValidIPV4(e)
}

function {:opaque} AbstractifyMapOfSeqNums(m:map<EndPoint,uint64>) : map<NodeIdentity,int>
  requires MapOfSeqNumsIsAbstractable(m)
{
  lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
  AbstractifyMap(m, AbstractifyEndPointToNodeIdentity, uint64_to_int, RefineNodeIdentityToEndPoint)
}

lemma lemma_AbstractifyMapOfSeqNums_properties(m:map<EndPoint,uint64>)
  requires MapOfSeqNumsIsAbstractable(m)
  ensures  m == map [] ==> AbstractifyMapOfSeqNums(m) == map []
  ensures  forall e :: (e in m <==> EndPointIsValidIPV4(e) && AbstractifyEndPointToNodeIdentity(e) in AbstractifyMapOfSeqNums(m))
  ensures  forall e :: (e !in m && EndPointIsValidIPV4(e) ==> AbstractifyEndPointToNodeIdentity(e) !in AbstractifyMapOfSeqNums(m))
  ensures  forall e :: e in m ==> AbstractifyMapOfSeqNums(m)[AbstractifyEndPointToNodeIdentity(e)] == m[e] as int
  ensures  forall e, u {:trigger AbstractifyMapOfSeqNums(m[e := u])} :: EndPointIsValidIPV4(e) ==> 
              var rm  := AbstractifyMapOfSeqNums(m);
              var rm' := AbstractifyMapOfSeqNums(m[e := u]);
              rm' == AbstractifyMapOfSeqNums(m)[AbstractifyEndPointToNodeIdentity(e) := u as int]
{
  lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
  assert forall ck1, ck2 :: EndPointIsValidIPV4(ck1) && EndPointIsValidIPV4(ck2) && AbstractifyEndPointToNodeIdentity(ck1) == AbstractifyEndPointToNodeIdentity(ck2) ==> ck1 == ck2;
  assert forall ck1, ck2 :: AbstractifyEndPointToNodeIdentity.requires(ck1) && AbstractifyEndPointToNodeIdentity.requires(ck2) && AbstractifyEndPointToNodeIdentity(ck1) == AbstractifyEndPointToNodeIdentity(ck2) ==> ck1 == ck2;

  reveal AbstractifyMapOfSeqNums();
  lemma_AbstractifyMap_properties(m, AbstractifyEndPointToNodeIdentity, uint64_to_int, RefineNodeIdentityToEndPoint);
}

//////////////////////////////////////////////////////////////////////////////
// Vote

datatype CVote = CVote(max_value_bal:CBallot, max_val:CRequestBatch)
datatype CVotes = CVotes(v:map<COperationNumber,CVote>)

function ValidVote(vote:CVote) : bool
{
  ValidRequestBatch(vote.max_val)
}

function method max_votes_len() : int { 8 } // previously 0x10_0000

function ValidVotes(votes:CVotes) : bool
{
  && |votes.v| < max_votes_len()
  && (forall o :: o in votes.v ==> ValidVote(votes.v[o]))
}

predicate CVoteIsAbstractable(vote:CVote)
{
  && vote.CVote?     // OBSERVE: Always true, but seems necessary to avoid errors below
  && CBallotIsAbstractable(vote.max_value_bal)
  && CRequestBatchIsAbstractable(vote.max_val)
}

function AbstractifyCVoteToVote(vote:CVote) : Vote
  requires CVoteIsAbstractable(vote)
{
  Vote(AbstractifyCBallotToBallot(vote.max_value_bal), AbstractifyCRequestBatchToRequestBatch(vote.max_val))
}

predicate CVotesIsAbstractable(votes:CVotes)
{
  forall i :: i in votes.v ==> COperationNumberIsAbstractable(i) && CVoteIsAbstractable(votes.v[i])
}

lemma lemma_AbstractifyMapOfThings<T>(m:map<COperationNumber,T>, newDomain:set<OperationNumber>)
  requires newDomain == set i | i in m :: AbstractifyCOperationNumberToOperationNumber(i)
  ensures forall o :: o in newDomain ==> 0<=o<0x10000000000000000
  ensures forall o :: o in newDomain ==> COperationNumber(o as uint64) in m
{
  forall o | o in newDomain
    ensures 0<=o<0x10000000000000000
    ensures COperationNumber(o as uint64) in m
  {
    var i :| i in m && o==AbstractifyCOperationNumberToOperationNumber(i);
    assert 0 <= i.n as int < 0x10000000000000000;
  }
}

function {:opaque} AbstractifyCVotesToVotes(votes:CVotes) : Votes
  requires CVotesIsAbstractable(votes)
{
  // var newDomain := set i | i in votes.v :: AbstractifyCOperationNumberToOperationNumber(i);
  lemma_AbstractifyMapOfThings(votes.v, set i | i in votes.v :: AbstractifyCOperationNumberToOperationNumber(i));
  // map i | i in newDomain :: AbstractifyCVoteToVote(votes.v[COperationNumber(i as uint64)])
  map j | j in (set i | i in votes.v :: AbstractifyCOperationNumberToOperationNumber(i)) :: AbstractifyCVoteToVote(votes.v[COperationNumber(j as uint64)])
}

lemma lemma_VotesInjective(v1:CVotes, v2:CVotes)
  requires CVotesIsAbstractable(v1)
  requires CVotesIsAbstractable(v2)
  requires AbstractifyCVotesToVotes(v1) == AbstractifyCVotesToVotes(v2)
  ensures v1 == v2
{
  reveal AbstractifyCVotesToVotes();
  forall k | k in v1.v ensures k in v2.v
  {
    assert AbstractifyCOperationNumberToOperationNumber(k) in AbstractifyCVotesToVotes(v1);
    assert AbstractifyCOperationNumberToOperationNumber(k) in AbstractifyCVotesToVotes(v2);
    assert k in v2.v;
  }
  forall k | k in v2.v ensures k in v1.v
  {
    assert AbstractifyCOperationNumberToOperationNumber(k) in AbstractifyCVotesToVotes(v2);
    assert AbstractifyCOperationNumberToOperationNumber(k) in AbstractifyCVotesToVotes(v1);
    assert k in v1.v;
  }
  assert domain(v1.v)==domain(v2.v);
  forall k | k in domain(v1.v) ensures v1.v[k] == v2.v[k];
  {
    assert AbstractifyCVoteToVote(v1.v[k]) == AbstractifyCVotesToVotes(v1)[AbstractifyCOperationNumberToOperationNumber(k)];   // OBSERVER trigger map
    assert AbstractifyCVoteToVote(v2.v[k]) == AbstractifyCVotesToVotes(v2)[AbstractifyCOperationNumberToOperationNumber(k)];   // OBSERVER trigger map

    assert AbstractifyCBallotToBallot(v1.v[k].max_value_bal) == AbstractifyCBallotToBallot(v2.v[k].max_value_bal);
//    assert v1.v[k].max_value_bal.seqno == v2.v[k].max_value_bal.seqno;
    lemma_BallotInjective(v1.v[k].max_value_bal, v2.v[k].max_value_bal);

    assert AbstractifyCRequestBatchToRequestBatch(v1.v[k].max_val) == AbstractifyCRequestBatchToRequestBatch(v2.v[k].max_val);
    lemma_AbstractifyCRequestBatchToRequestBatch_isInjective();
    assert v1.v[k].max_val == v2.v[k].max_val;
  }
  assert v1.v==v2.v;
  assert v1==v2;
}

/////////////////////
// LearnerDecidableOpn

datatype OptionOpn = ExistsOperation(opn:COperationNumber) 
                   | NotExistsOperation()

} 
