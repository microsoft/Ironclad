include "../../Common/Collections/Maps.i.dfy"
include "../../Protocol/RSL/Configuration.i.dfy"
include "../../Protocol/RSL/Message.i.dfy"
include "../../Protocol/RSL/Types.i.dfy"
include "../Common/GenericMarshalling.i.dfy"
include "CTypes.i.dfy"
include "CMessage.i.dfy"
include "CMessageRefinements.i.dfy"

module LiveRSL__PacketParsing_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Maps_i
import opened LiveRSL__AppInterface_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Message_i
import opened LiveRSL__Types_i
import opened Common__GenericMarshalling_i
import opened Common__NodeIdentity_i
import opened Common__UdpClient_i
import opened Common__Util_i
import opened AppStateMachine_s
import opened Environment_s
import opened Math__mul_i
import opened Math__mul_nonlinear_i

////////////////////////////////////////////////////////////////////
//    Grammars for the Paxos types
////////////////////////////////////////////////////////////////////
function method EndPoint_grammar() : G { GUint64 }
function method CRequest_grammar() : G { GTuple([EndPoint_grammar(), GUint64, GByteArray]) }
function method CRequestBatch_grammar() : G { GArray(CRequest_grammar()) }
function method CReply_grammar() : G { GTuple([EndPoint_grammar(), GUint64, GByteArray]) }
function method CBallot_grammar() : G { GTuple([GUint64, GUint64]) }
function method COperationNumber_grammar() : G { GUint64 }
function method CVote_grammar() : G { GTuple([CBallot_grammar(), CRequestBatch_grammar()])} 
function method CMap_grammar(key:G, val:G) : G { GArray(GTuple([key, val])) }
function method CVotes_grammar() : G { GArray(GTuple([COperationNumber_grammar(), CVote_grammar()])) }
function method CReplyCache_grammar() : G { GArray(GTuple([EndPoint_grammar(), CReply_grammar()])) }

////////////////////////////////////////////////////////////////////
//    Grammars for the Paxos messages 
////////////////////////////////////////////////////////////////////
function method CMessage_Request_grammar() : G { GTuple([GUint64, GByteArray]) }
function method CMessage_1a_grammar() : G { CBallot_grammar() }
function method CMessage_1b_grammar() : G { GTuple([CBallot_grammar(), COperationNumber_grammar(), CVotes_grammar()]) }
function method CMessage_2a_grammar() : G { GTuple([CBallot_grammar(), COperationNumber_grammar(), CRequestBatch_grammar()]) }
function method CMessage_2b_grammar() : G { GTuple([CBallot_grammar(), COperationNumber_grammar(), CRequestBatch_grammar()]) }
function method CMessage_Heartbeat_grammar() : G { GTuple([CBallot_grammar(), GUint64, COperationNumber_grammar()]) }
function method CMessage_Reply_grammar() : G { GTuple( [GUint64, GByteArray] ) }
function method CMessage_AppStateRequest_grammar() : G { GTuple([CBallot_grammar(), COperationNumber_grammar()]) }
function method CMessage_AppStateSupply_grammar() : G { GTuple([CBallot_grammar(), COperationNumber_grammar(), GByteArray, CReplyCache_grammar()]) }
function method CMessage_StartingPhase2_grammar() : G { GTuple([CBallot_grammar(), COperationNumber_grammar()]) }

function method CMessage_grammar() : G { GTaggedUnion([
  CMessage_Request_grammar(),
  CMessage_1a_grammar(),
  CMessage_1b_grammar(),
  CMessage_2a_grammar(),
  CMessage_2b_grammar(),
  CMessage_Heartbeat_grammar(),
  CMessage_Reply_grammar(),
  CMessage_AppStateRequest_grammar(),
  CMessage_AppStateSupply_grammar(),
  CMessage_StartingPhase2_grammar()
  ]) }

predicate UdpPacketBound(data:seq<byte>) 
{
  |data| < MaxPacketSize()
}

////////////////////////////////////////////////////////////////////
//    64-bit Limits
////////////////////////////////////////////////////////////////////

predicate CRequestBatchIs64Bit(batch:CRequestBatch)
{
  |batch| < 0x1_0000_0000_0000_0000
}

predicate CVoteIs64Bit(vote:CVote)
{
  CRequestBatchIs64Bit(vote.max_val)
}

predicate CVotesIs64Bit(votes:CVotes)
{
  && |votes.v| < 0x1_0000_0000_0000_0000
  && (forall opn :: opn in votes.v ==> CVoteIs64Bit(votes.v[opn]))
}

predicate CReplyCacheIs64Bit(rc:CReplyCache)
{
  |rc| < 0x1_0000_0000_0000_0000
}

predicate CMessageIs64Bit(msg:CMessage)
{
  match msg
    case CMessage_Invalid => true
    case CMessage_Request(seqno, val) => true
    case CMessage_1a(bal) => true
    case CMessage_1b(bal, log_truncation_point, votes) => CVotesIs64Bit(votes)
    case CMessage_2a(bal, opn, batch) => CRequestBatchIs64Bit(batch)
    case CMessage_2b(bal, opn, batch) => CRequestBatchIs64Bit(batch)
    case CMessage_Heartbeat(bal, suspicious, opn) => true
    case CMessage_Reply(seqno, reply) => true
    case CMessage_AppStateRequest(bal, opn) => true
    case CMessage_AppStateSupply(bal, opn, app, rc) => CReplyCacheIs64Bit(rc)
    case CMessage_StartingPhase2(bal, log_truncation_point) => true
}

////////////////////////////////////////////////////////////////////
//    Parsing
////////////////////////////////////////////////////////////////////

function method parse_EndPoint(val:V) : EndPoint
  requires ValInGrammar(val, EndPoint_grammar())
  ensures  EndPointIsAbstractable(parse_EndPoint(val))
{
  if val.u <= 0xffffffffffff then
    ConvertUint64ToEndPoint(val.u)
  else
    EndPoint([0,0,0,0], 0)
}

function method parse_Request(val:V) : CRequest
  requires ValInGrammar(val, CRequest_grammar())
  ensures  CRequestIsAbstractable(parse_Request(val))
{
  assert ValInGrammar(val.t[0], CRequest_grammar().t[0]);      // OBSERVE 
  assert ValInGrammar(val.t[1], CRequest_grammar().t[1]);      // OBSERVE 
  assert ValInGrammar(val.t[2], CRequest_grammar().t[2]);      // OBSERVE 
  var ep := parse_EndPoint(val.t[0]);
  CRequest(ep, val.t[1].u, val.t[2].b)
}

function parse_RequestBatch(val:V) : CRequestBatch
  requires ValInGrammar(val, CRequestBatch_grammar())
  ensures  |parse_RequestBatch(val)| == |val.a|
  ensures  forall i :: 0 <= i < |parse_RequestBatch(val)| ==> parse_RequestBatch(val)[i] == parse_Request(val.a[i])
  ensures  CRequestBatchIsAbstractable(parse_RequestBatch(val))
  ensures  ValidVal(val) ==> CRequestBatchIs64Bit(parse_RequestBatch(val))
  decreases |val.a|
{
  if |val.a| == 0 then
    []
  else 
    var req := parse_Request(val.a[0]);
    var restVal:V := VArray(val.a[1..]);
    var rest := parse_RequestBatch(restVal);
    [req] + rest
}

/*
method parse_RequestBatchIter(val:V) returns (batch:CRequestBatch)
  requires ValInGrammar(val, CRequestBatch_grammar())
  requires ValidVal(val)
  ensures |batch| == |val.a|
  ensures forall i :: 0 <= i < |batch| ==> batch[i] == parse_Request(val.a[i])
{
  batch := [];

  var i:uint64 := 0;
  while i < |val.a| as uint64 
    invariant 0 <= int(i) <= |val.a|
    invariant int(i) == |batch|
    invariant forall j :: 0 <= j < int(i) ==> batch[j] == parse_Request(val.a[j])
  {
    var req := parse_Request(val.a[i]);
    batch := batch + [req];
    i := i + 1;
  }
}
*/

method Parse_RequestBatch(val:V) returns (batch:CRequestBatch)
  requires ValInGrammar(val, CRequestBatch_grammar())
  requires ValidVal(val)
  ensures |batch| == |val.a|
  ensures  CRequestBatchIs64Bit(batch)
  ensures  forall i :: 0 <= i < |batch| ==> batch[i] == parse_Request(val.a[i])
  ensures  batch == parse_RequestBatch(val)
  ensures  CRequestBatchIsAbstractable(batch)
{
  var batchArr := new CRequest[|val.a| as uint64];

  var i:uint64 := 0;
  while i < |val.a| as uint64
    invariant 0 <= i as int <= |val.a|
    invariant forall j :: 0 <= j < i as int ==> batchArr[j] == parse_Request(val.a[j])
  {
    var req := parse_Request(val.a[i]);
    batchArr[i] := req;
    i := i + 1;
  }
  batch := batchArr[..];
}

function method parse_Reply(val:V) : CReply
  requires ValInGrammar(val, CReply_grammar())
  ensures  CReplyIsAbstractable(parse_Reply(val))
{
  assert ValInGrammar(val.t[0], CReply_grammar().t[0]);      // OBSERVE 
  assert ValInGrammar(val.t[1], CReply_grammar().t[1]);      // OBSERVE 
  assert ValInGrammar(val.t[2], CReply_grammar().t[2]);      // OBSERVE 
  var ep := parse_EndPoint(val.t[0]);
  CReply(ep, val.t[1].u, val.t[2].b)
}

function method parse_Ballot(val:V) : CBallot
  requires ValInGrammar(val, CBallot_grammar())
  ensures  CBallotIsAbstractable(parse_Ballot(val))
{
  assert ValInGrammar(val.t[0], CBallot_grammar().t[0]);      // OBSERVE 
  assert ValInGrammar(val.t[1], CBallot_grammar().t[1]);      // OBSERVE
  CBallot(val.t[0].u, val.t[1].u)
}

function method parse_OperationNumber(val:V) : COperationNumber
  requires ValInGrammar(val, COperationNumber_grammar())
  ensures  COperationNumberIsAbstractable(parse_OperationNumber(val))
{
  COperationNumber(val.u)
}

function parse_Vote(val:V) : CVote
  requires ValInGrammar(val, CVote_grammar())
  ensures  CVoteIsAbstractable(parse_Vote(val))
  ensures  ValidVal(val) ==> CVoteIs64Bit(parse_Vote(val))
{
  CVote(parse_Ballot(val.t[0]), parse_RequestBatch(val.t[1]))
}

method Parse_Vote(val:V) returns (vote:CVote)
  requires ValInGrammar(val, CVote_grammar())
  requires ValidVal(val)
  ensures  parse_Vote(val) == vote
  ensures  CVoteIs64Bit(vote)
{
  var batch := Parse_RequestBatch(val.t[1]);
  vote := CVote(parse_Ballot(val.t[0]), batch);
}


// Abandoned for now, since the marshalling side is all methods, so we can't easily make it higher order
// 
//function method parse_Map<KT, VT>(val:V, parse_key:V->KT, parse_val:V->VT, key_grammar:G, val_grammar:G) : map<KT, VT>
//  requires ValInGrammar(val, CMap_grammar(key_grammar, val_grammar))
//  requires forall v :: parse_key.requires(v) && parse_val.requires(v)
//  reads parse_key.reads, parse_val.reads;
//  decreases |val.a|
//{
//  if |val.a| == 0 then
//    map []
//  else 
//    var tuple := val.a[0];
//    assert ValInGrammar(tuple, CMap_grammar(key_grammar, val_grammar).elt);
//    assert ValInGrammar(tuple.t[0], CMap_grammar(key_grammar, val_grammar).elt.t[0]); // OBSERVE
//    assert ValInGrammar(tuple.t[1], CMap_grammar(key_grammar, val_grammar).elt.t[1]); // OBSERVE
//    var k := parse_key(tuple.t[0]);
//    var v := parse_val(tuple.t[1]);
//    var others := parse_Map(VArray(val.a[1..]), parse_key, parse_val, key_grammar, val_grammar);
//    var m := others[k := v];
//    m
//}

function method parse_ReplyCache(val:V) : CReplyCache
  requires ValInGrammar(val, CReplyCache_grammar())
  ensures  CReplyCacheIsAbstractable(parse_ReplyCache(val))
  ensures  |parse_ReplyCache(val)| <= |val.a|
  ensures  ValidVal(val) ==> CReplyCacheIs64Bit(parse_ReplyCache(val))
  decreases |val.a|
{
  if |val.a| == 0 then
    map []
  else 
    var tuple := val.a[0];
    assert ValInGrammar(tuple, CReplyCache_grammar().elt);
    assert ValInGrammar(tuple.t[0], CReplyCache_grammar().elt.t[0]); // OBSERVE
    assert ValInGrammar(tuple.t[1], CReplyCache_grammar().elt.t[1]); // OBSERVE
    var e := parse_EndPoint(tuple.t[0]);
    var reply := parse_Reply(tuple.t[1]);
    var others := parse_ReplyCache(VArray(val.a[1..]));
    var m := others[e := reply];
    assert forall e' :: e' in m ==> EndPointIsValidIPV4(e');
    assert forall e' :: e' in m ==> CReplyIsAbstractable(m[e']);
    m
}

function parse_Votes(val:V) : CVotes
  requires ValInGrammar(val, CVotes_grammar())
  ensures  CVotesIsAbstractable(parse_Votes(val))
  ensures  |parse_Votes(val).v| <= |val.a|
  ensures  ValidVal(val) ==> CVotesIs64Bit(parse_Votes(val))
  decreases |val.a|
{
  if |val.a| == 0 then
    CVotes(map [])
  else 
    var tuple := val.a[0];
    assert ValInGrammar(tuple, CVotes_grammar().elt);
    assert ValInGrammar(tuple.t[0], CVotes_grammar().elt.t[0]); // OBSERVE
    assert ValInGrammar(tuple.t[1], CVotes_grammar().elt.t[1]); // OBSERVE
    var op := parse_OperationNumber(tuple.t[0]);
    var vote := parse_Vote(tuple.t[1]);
    var others := parse_Votes(VArray(val.a[1..]));
    calc {
      ValidVal(val);
      ==> { assert val.a[0] in val.a; } ValidVal(val.a[0]);
      ==> ValidVal(tuple);
      ==> { assert tuple.t[1] in tuple.t; } ValidVal(tuple.t[1]);
      ==> CVoteIs64Bit(vote);
    }
    var m := others.v[op := vote];
    assert COperationNumberIsAbstractable(op);
    CVotes(m)
}

method Parse_Votes(val:V) returns (votes:CVotes)
  requires ValInGrammar(val, CVotes_grammar())
  requires ValidVal(val)
  ensures  CVotesIsAbstractable(votes)
  ensures  CVotesIs64Bit(votes)
  decreases |val.a|
  ensures votes == parse_Votes(val)
{
  if |val.a| as uint64 == 0 {
    votes := CVotes(map []);
  } else {
    var tuple := val.a[0];
    assert ValInGrammar(tuple, CVotes_grammar().elt);
    assert ValInGrammar(tuple.t[0], CVotes_grammar().elt.t[0]); // OBSERVE
    assert ValInGrammar(tuple.t[1], CVotes_grammar().elt.t[1]); // OBSERVE
    calc ==> {
      ValidVal(val);
      ValidVal(tuple);
      ValidVal(tuple.t[1]);
    }
    var op := parse_OperationNumber(tuple.t[0]);
    var vote := Parse_Vote(tuple.t[1]);
    var others := Parse_Votes(VArray(val.a[1..]));
    var m := others.v[op := vote];
    votes := CVotes(m);
  }
}

function method parse_Message_Request(val:V) : CMessage
  requires ValInGrammar(val, CMessage_Request_grammar())
  ensures  CMessageIsAbstractable(parse_Message_Request(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_Request(val))
{
  assert ValInGrammar(val.t[0], CMessage_Request_grammar().t[0]);      // OBSERVE
  assert ValInGrammar(val.t[1], CMessage_Request_grammar().t[1]);      // OBSERVE
  CMessage_Request(val.t[0].u, val.t[1].b)
}

function method parse_Message_1a(val:V) : CMessage
  requires ValInGrammar(val, CMessage_1a_grammar())
  ensures  CMessageIsAbstractable(parse_Message_1a(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_1a(val))
{
  CMessage_1a(parse_Ballot(val))
}

function parse_Message_1b(val:V) : CMessage
  requires ValInGrammar(val, CMessage_1b_grammar())
  ensures  CMessageIsAbstractable(parse_Message_1b(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_1b(val))
{
  CMessage_1b(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), parse_Votes(val.t[2]))
}

method Parse_Message_1b(val:V) returns (msg:CMessage)
  requires ValInGrammar(val, CMessage_1b_grammar())
  requires ValidVal(val)
  ensures  msg == parse_Message_1b(val)
  ensures  CMessageIsAbstractable(msg)
  ensures  CMessageIs64Bit(msg)
{
  var votes := Parse_Votes(val.t[2]);
  msg := CMessage_1b(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), votes);
}

function parse_Message_2a(val:V) : CMessage
  requires ValInGrammar(val, CMessage_2a_grammar())
  ensures  CMessageIsAbstractable(parse_Message_2a(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_2a(val))
{
  CMessage_2a(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), parse_RequestBatch(val.t[2]))
}

method Parse_Message_2a(val:V) returns (msg:CMessage)
  requires ValInGrammar(val, CMessage_2a_grammar())
  requires ValidVal(val)
  ensures  msg == parse_Message_2a(val)
  ensures  CMessageIsAbstractable(msg)
  ensures  CMessageIs64Bit(msg)
{
  var batch := Parse_RequestBatch(val.t[2]);
  msg := CMessage_2a(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), batch);
}

function parse_Message_2b(val:V) : CMessage
  requires ValInGrammar(val, CMessage_2b_grammar())
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_2b(val))
{
  CMessage_2b(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), parse_RequestBatch(val.t[2]))
}

method Parse_Message_2b(val:V) returns (msg:CMessage)
  requires ValInGrammar(val, CMessage_2b_grammar())
  requires ValidVal(val)
  ensures  msg == parse_Message_2b(val)
  ensures  CMessageIsAbstractable(msg)
  ensures  CMessageIs64Bit(msg)
{
  var batch := Parse_RequestBatch(val.t[2]);
  msg := CMessage_2b(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), batch);
}

function method parse_Message_Heartbeat(val:V) : CMessage
  requires ValInGrammar(val, CMessage_Heartbeat_grammar())
  ensures  CMessageIsAbstractable(parse_Message_Heartbeat(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_Heartbeat(val))
{
  assert ValInGrammar(val.t[1], CMessage_Heartbeat_grammar().t[1]);      // OBSERVE
  CMessage_Heartbeat(parse_Ballot(val.t[0]), val.t[1].u != 0, parse_OperationNumber(val.t[2]))
}

function method parse_Message_Reply(val:V) : CMessage
  requires ValInGrammar(val, CMessage_Reply_grammar())
  ensures  CMessageIsAbstractable(parse_Message_Reply(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_Reply(val))
{
  assert ValInGrammar(val.t[0], CMessage_Reply_grammar().t[0]);      // OBSERVE
  assert ValInGrammar(val.t[1], CMessage_Reply_grammar().t[1]);      // OBSERVE
  CMessage_Reply(val.t[0].u, val.t[1].b)
}

function method parse_Message_AppStateRequest(val:V) : CMessage
  requires ValInGrammar(val, CMessage_AppStateRequest_grammar())
  ensures  CMessageIsAbstractable(parse_Message_AppStateRequest(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_AppStateRequest(val))
{
  CMessage_AppStateRequest(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]))
}

function method parse_Message_AppStateSupply(val:V) : CMessage
  requires ValInGrammar(val, CMessage_AppStateSupply_grammar())
  ensures  CMessageIsAbstractable(parse_Message_AppStateSupply(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_AppStateSupply(val))
{
  assert ValInGrammar(val.t[2], GByteArray);
  CMessage_AppStateSupply(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), val.t[2].b, parse_ReplyCache(val.t[3]))
}

function method parse_Message_StartingPhase2(val:V) : CMessage
  requires ValInGrammar(val, CMessage_StartingPhase2_grammar())
  ensures  CMessageIsAbstractable(parse_Message_StartingPhase2(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_StartingPhase2(val))
{
  CMessage_StartingPhase2(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]))
}


function parse_Message(val:V) : CMessage
  requires ValInGrammar(val, CMessage_grammar())
  ensures  CMessageIsAbstractable(parse_Message(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message(val))
{
  if val.c == 0 then
    parse_Message_Request(val.val)
  else if val.c == 1 then
    parse_Message_1a(val.val)
  else if val.c == 2 then
    parse_Message_1b(val.val)
  else if val.c == 3 then
    parse_Message_2a(val.val)
  else if val.c == 4 then
    parse_Message_2b(val.val)
  else if val.c == 5 then
    parse_Message_Heartbeat(val.val)
  else if val.c == 6 then
    parse_Message_Reply(val.val)
  else if val.c == 7 then
    parse_Message_AppStateRequest(val.val)
  else if val.c == 8 then
    parse_Message_AppStateSupply(val.val)
  else if val.c == 9 then
    parse_Message_StartingPhase2(val.val)
  else
    assert false;       // Should never get here
    parse_Message_Request(val)
}

method Parse_Message(val:V) returns (msg:CMessage)
	requires ValInGrammar(val, CMessage_grammar())
	requires ValidVal(val)
	ensures	 msg == parse_Message(val)
	ensures	 !msg.CMessage_Invalid?
	ensures	 CMessageIsAbstractable(msg)
	ensures	 CMessageIs64Bit(msg)
{
	if val.c == 0 {
		msg := parse_Message_Request(val.val);
	} else if val.c == 1 {
		msg := parse_Message_1a(val.val);
	} else if val.c == 2 {
		msg := Parse_Message_1b(val.val);
	} else if val.c == 3 {
		msg := Parse_Message_2a(val.val);
	} else if val.c == 4 {
		msg := Parse_Message_2b(val.val);
	} else if val.c == 5 {
		msg := parse_Message_Heartbeat(val.val);
	} else if val.c == 6 {
		msg := parse_Message_Reply(val.val);
	} else if val.c == 7 {
		msg := parse_Message_AppStateRequest(val.val);
	} else if val.c == 8 {
		msg := parse_Message_AppStateSupply(val.val);
	} else if val.c == 9 {
		msg := parse_Message_StartingPhase2(val.val);
	} else {
		assert false;				// Should never get here
		msg := parse_Message_Request(val);
	}
}

function PaxosDemarshallData(data:seq<byte>) : CMessage
  ensures  CMessageIsAbstractable(PaxosDemarshallData(data))
{
  if Demarshallable(data, CMessage_grammar()) then
    var val := DemarshallFunc(data, CMessage_grammar());
    parse_Message(val)
  else
    CMessage_Invalid()
}

method PaxosDemarshallDataMethod(data:array<byte>, msg_grammar:G) returns (msg:CMessage)
  requires data.Length < 0x1_0000_0000_0000_0000
  requires msg_grammar == CMessage_grammar()
  requires ValidGrammar(msg_grammar)
  ensures  CMessageIsAbstractable(msg)
  ensures  if Demarshallable(data[..], msg_grammar) then
             msg == PaxosDemarshallData(data[..]) 
           else
             msg.CMessage_Invalid?
  ensures  CMessageIs64Bit(msg)
{
  var success, val := Demarshall(data, msg_grammar);
  if success {
    assert ValInGrammar(val, msg_grammar);
    msg := Parse_Message(val);
    assert !msg.CMessage_Invalid?;
  } else {
    msg := CMessage_Invalid();
  }
}

////////////////////////////////////////////////////////////////////
//    Can a value be marshalled?
////////////////////////////////////////////////////////////////////

function Marshallable_2a(msg:CMessage) : bool
{
  && msg.CMessage_2a?
  && ValidRequestBatch(msg.val_2a)
}

function Marshallable_2b(msg:CMessage) : bool
{
  && msg.CMessage_2b?
  && ValidRequestBatch(msg.val_2b)
}

function Marshallable(msg:CMessage) : bool
{
  && (!msg.CMessage_Invalid?)
  && (msg.CMessage_Request? ==> CAppRequestMarshallable(msg.val))
  && (msg.CMessage_1a? ==> true)
  && (msg.CMessage_1b? ==> ValidVotes(msg.votes))
  && (msg.CMessage_2a? ==> Marshallable_2a(msg))
  && (msg.CMessage_2b? ==> Marshallable_2b(msg))
  && (msg.CMessage_Heartbeat? ==> true)
  && (msg.CMessage_Reply? ==> CAppReplyMarshallable(msg.reply))
  && (msg.CMessage_AppStateRequest? ==> true)
  && (msg.CMessage_AppStateSupply? ==> CAppStateMarshallable(msg.app_state) && ValidReplyCache(msg.reply_cache))
  && (msg.CMessage_StartingPhase2? ==> true)
}

function CMessageIsValid(msg:CMessage) : bool
{
  Marshallable(msg)
}

predicate CPacketsIsMarshallable(cps:set<CPacket>)
{
  forall cp :: cp in cps ==> Marshallable(cp.msg)
}

method DetermineIfValidVote(vote:CVote) returns (b:bool)
  requires CVoteIsAbstractable(vote)
  requires CVoteIs64Bit(vote)
  ensures b == ValidVote(vote)
{
  var num_votes:uint64 := |vote.max_val| as uint64;
  if num_votes > 100 {  // RequestBatchSizeLimit
    b := false;
    return;
  }

  var pos:uint64 := 0;
  while pos < num_votes
    invariant 0 <= pos <= num_votes
    invariant forall i :: 0 <= i < pos ==> ValidRequest(vote.max_val[i])
  {
    var c := vote.max_val[pos];
    if c.CRequest? && !CAppRequestMarshallable(c.request) {
      assert !ValidRequest(c);
      assert !ValidRequestBatch(vote.max_val);
      b := false;
      return;
    }
    pos := pos + 1;
  }

  b := true;
}

method DetermineIfValidVotes(votes:CVotes) returns (b:bool)
  requires CVotesIsAbstractable(votes)
  requires CVotesIs64Bit(votes)
  ensures  b == ValidVotes(votes)
{
  b := (|votes.v| as uint64) < 8;  // max_votes_len
  if !b {
    return;
  }

  var keys := domain(votes.v);
  lemma_MapSizeIsDomainSize(keys, votes.v);
  while |keys| > 0
    invariant |keys| < max_votes_len()
    invariant forall opn :: opn in keys ==> opn in votes.v
    invariant forall opn :: opn in votes.v ==> opn in keys || ValidVote(votes.v[opn])
    decreases |keys|
  {
    var opn :| opn in keys;
    keys := keys - {opn};
    b := DetermineIfValidVote(votes.v[opn]);
    if !b {
      return;
    }
  }
}

method DetermineIfValidReplyCache(m:CReplyCache) returns (b:bool)
  requires CReplyCacheIsAbstractable(m)
  requires CReplyCacheIs64Bit(m)
  ensures  b == ValidReplyCache(m)
{
  b := (|m| as uint64) < 256; // RequestBatchSizeLimit
  if !b {
    return;
  }

  assert CReplyCacheIsAbstractable(m);

  var keys := domain(m);
  lemma_MapSizeIsDomainSize(keys, m);
  while |keys| > 0
    invariant |keys| < 256
    invariant forall e :: e in keys ==> e in m
    invariant forall e :: e in m ==> e in keys || ValidReply(m[e])
    decreases |keys|
  {
    var e :| e in keys;
    assert EndPointIsValidIPV4(e);
    assert CReplyIsAbstractable(m[e]);
    if m[e].CReply? && !CAppReplyMarshallable(m[e].reply) {
      b := false;
      assert !ValidReply(m[e]);
      return;
    }
    keys := keys - {e};
  }
}

method DetermineIfValidRequestBatch(c:CRequestBatch) returns (b:bool)
  requires CRequestBatchIsAbstractable(c)
  requires CRequestBatchIs64Bit(c)
  ensures  b == ValidRequestBatch(c)
{
  var n := |c| as uint64;
  b := n <= 100;
  if !b {
    return;
  }

  var pos: uint64 := 0;
  while pos < n
    invariant 0 <= pos <= n
    invariant forall i :: 0 <= i < pos ==> ValidRequest(c[i])
  {
    var cr := c[pos];
    if !ValidRequest(c[pos]) {
      b := false;
      return;
    }
    pos := pos + 1;
  }
}

method DetermineIfMessageMarshallable(msg:CMessage) returns (b:bool)
  requires CMessageIsAbstractable(msg)
  requires CMessageIs64Bit(msg)
  ensures  b == Marshallable(msg)
{
  if msg.CMessage_Invalid? {
    b := false;
  }
  else if msg.CMessage_Request? {
    b := CAppRequestMarshallable(msg.val);
  }
  else if msg.CMessage_1a? {
    b := true;
  }
  else if msg.CMessage_1b? {
    b := DetermineIfValidVotes(msg.votes);
  }
  else if msg.CMessage_2a? {
    b := DetermineIfValidRequestBatch(msg.val_2a);
  }
  else if msg.CMessage_2b? {
    b := DetermineIfValidRequestBatch(msg.val_2b);
  }
  else if msg.CMessage_Heartbeat? {
    b := true;
  }
  else if msg.CMessage_Reply? {
    b := CAppReplyMarshallable(msg.reply);
  }
  else if msg.CMessage_AppStateRequest? {
    b := true;
  }
  else if msg.CMessage_AppStateSupply? {
    var b1 := CAppStateMarshallable(msg.app_state);
    var b2 := DetermineIfValidReplyCache(msg.reply_cache);
    b := b1 && b2;
  }
  else if msg.CMessage_StartingPhase2? {
    b := true;
  }
  else {
    assert false;
  }
}

////////////////////////////////////////////////////////////////////
//    Marshalling 
////////////////////////////////////////////////////////////////////

method MarshallEndPoint(c:EndPoint) returns (val:V)
  requires EndPointIsValidIPV4(c)
  ensures  ValInGrammar(val, EndPoint_grammar())
  ensures  ValidVal(val)
  ensures  parse_EndPoint(val) == c
{
  val := VUint64(ConvertEndPointToUint64(c));
  lemma_Uint64EndPointRelationships();
}

method MarshallRequest(c:CRequest) returns (val:V)
  requires ValidRequest(c)
  ensures  ValInGrammar(val, CRequest_grammar())
  ensures  ValidVal(val)
  ensures  parse_Request(val) == c
{
  var marshalled_app_message := MarshallCAppRequest(c.request);
  var marshalled_ep := MarshallEndPoint(c.client);
  val := VTuple([marshalled_ep, VUint64(c.seqno), marshalled_app_message]);

  assert ValInGrammar(val.t[0], CRequest_grammar().t[0]);      // OBSERVE 
  assert ValInGrammar(val.t[1], CRequest_grammar().t[1]);      // OBSERVE 
  assert ValInGrammar(val.t[2], CRequest_grammar().t[2]);      // OBSERVE 
  calc {
    ValidVal(val);
    ValidVal(val.t[0]) && ValidVal(val.t[1]) && ValidVal(val.t[2]);
  }
}

method MarshallRequestBatch(c:CRequestBatch) returns (val:V)
  requires ValidRequestBatch(c)
  ensures  ValInGrammar(val, CRequestBatch_grammar())
  ensures  ValidVal(val)
  ensures  parse_RequestBatch(val) == c
{
  var reqs := new V[|c| as uint64];

  var i:uint64 := 0;
  while i < |c| as uint64
    invariant 0 <= i as int <= |c|
    invariant forall j :: 0 <= j < i ==> ValInGrammar(reqs[j], CRequest_grammar())
    invariant forall j :: 0 <= j < i ==> ValidVal(reqs[j])
    invariant forall j :: 0 <= j < i ==> parse_Request(reqs[j]) == c[j]
  {
    var single := MarshallRequest(c[i]);
    assert ValInGrammar(single, CRequest_grammar());
    reqs[i] := single;
    i := i + 1;
  }

  val := VArray(reqs[..]);
}

method MarshallReply(c:CReply) returns (val:V)
  requires ValidReply(c)
  ensures  ValInGrammar(val, CReply_grammar())
  ensures  ValidVal(val)
  ensures  parse_Reply(val) == c
{
  var marshalled_app_message := MarshallCAppReply(c.reply);
  var marshalled_ep := MarshallEndPoint(c.client);
  val := VTuple([marshalled_ep, VUint64(c.seqno), marshalled_app_message]);
  assert ValInGrammar(val.t[0], CReply_grammar().t[0]);      // OBSERVE 
  assert ValInGrammar(val.t[1], CReply_grammar().t[1]);      // OBSERVE 
  assert ValInGrammar(val.t[2], CReply_grammar().t[2]);      // OBSERVE 
  calc {
    ValidVal(val);
    ValidVal(val.t[0]) && ValidVal(val.t[1]) && ValidVal(val.t[2]);
  }
}

method MarshallBallot(c:CBallot) returns (val:V)
  ensures  ValInGrammar(val, CBallot_grammar())
  ensures  ValidVal(val)
  ensures  parse_Ballot(val) == c
{
  val := VTuple([VUint64(c.seqno), VUint64(c.proposer_id)]);
}

method MarshallOperationNumber(c:COperationNumber) returns (val:V)
  ensures  ValInGrammar(val, COperationNumber_grammar())
  ensures  ValidVal(val)
  ensures  parse_OperationNumber(val) == c
{
  val := VUint64(c.n);
}

method MarshallVote(c:CVote) returns (val:V)
  requires ValidVote(c)
  ensures  ValInGrammar(val, CVote_grammar())
  ensures  ValidVal(val)
  ensures  parse_Vote(val) == c
{
  var bal := MarshallBallot(c.max_value_bal);
  var v := MarshallRequestBatch(c.max_val);
  val := VTuple([bal, v]);
}

method MarshallReplyCache(c:CReplyCache) returns (val:V)
  requires ValidReplyCache(c)
  decreases |c|
  ensures  ValInGrammar(val, CReplyCache_grammar())
  ensures  |val.a| == |c|
  ensures  ValidVal(val)
  ensures  parse_ReplyCache(val) == c
  ensures SeqSum(val.a) <= |c| * (8 + (8 + 8) + (24 + MaxAppReplySize())); 
{
  if |c| == 0 {
    val := VArray([]);
    reveal SeqSum();
  } else {
    //lemma_non_empty_map_has_elements(c);
    var ep :| ep in c;
    var marshalled_ep := MarshallEndPoint(ep);
    var marshalled_reply := MarshallReply(c[ep]);
    var remainder := RemoveElt(c, ep);
    assert forall e :: e in remainder ==> ValidReply(remainder[e]);
    var marshalled_remainder := MarshallReplyCache(remainder);
    assert parse_ReplyCache(marshalled_remainder) == remainder;
    val := VArray([VTuple([marshalled_ep, marshalled_reply])] + marshalled_remainder.a);

    // OBSERVE (everything below; not sure which bit is critical to proving the final ensures
    ghost var tuple := val.a[0];
    ghost var rest := val.a[1..];
    assert ValInGrammar(tuple, CReplyCache_grammar().elt);
    assert ValInGrammar(tuple.t[0], CReplyCache_grammar().elt.t[0]); 
    assert ValInGrammar(tuple.t[1], CReplyCache_grammar().elt.t[1]);
    ghost var ep' := parse_EndPoint(tuple.t[0]);
    ghost var reply' := parse_Reply(tuple.t[1]);
    ghost var others' := parse_ReplyCache(VArray(val.a[1..]));
    ghost var m' := others'[ep' := reply'];
    assert ep' == ep;
    assert reply' == c[ep];
    assert others' == remainder;
    assert m' == c;

    // Prove the SeqSum ensure
    calc {
      SeqSum(val.a);
        { reveal SeqSum(); }
      SizeOfV(val.a[0]) + SeqSum(val.a[1..]);
      <=  
      SizeOfV(val.a[0]) + |remainder| * (8 + (8 + 8) + (24 + MaxAppReplySize()));
      SizeOfV(val.a[0]) + |remainder| * (8 + (8 + 8) + (24 + MaxAppReplySize()));
        { lemma_SeqSum2(val.a[0]); }
      SizeOfV(val.a[0].t[0]) + SizeOfV(val.a[0].t[1]) + |remainder| * (8 + (8 + 8) + (24 + MaxAppReplySize()));
      <   { lemma_ReplyValValid(c[ep], val.a[0].t[1]); lemma_ReplyBound(c[ep], val.a[0].t[1]); }
      8 + (8 + 8) + (24 + MaxAppReplySize()) + |remainder| * (8 + (8 + 8) + (24 + MaxAppReplySize()));
      1*(8 + (8 + 8) + (24 + MaxAppReplySize())) + |remainder| * (8 + (8 + 8) + (24 + MaxAppReplySize()));
        { lemma_mul_is_distributive((8 + (8 + 8) + (24 + MaxAppReplySize())), 1, |remainder|); }
      (1+|remainder|) * (8 + (8 + 8) + (24 + MaxAppReplySize()));
      |c| * (8 + (8 + 8) + (24 + MaxAppReplySize()));
    }
  }
}

method{:timeLimitMultiplier 3} MarshallVotes(c:CVotes) returns (val:V)
  requires ValidVotes(c)
  decreases |c.v|
  ensures  ValInGrammar(val, CVotes_grammar())
  ensures  |val.a| == |c.v|
  ensures  ValidVal(val)
  ensures  parse_Votes(val) == c
  //ensures  val == fun_MarshallVotes(c)
  ensures SeqSum(val.a) <= |c.v| * (8 + (8 + 8) + (8 + (24 + MaxAppRequestSize())*RequestBatchSizeLimit()))
{
  if |c.v| == 0 {
    val := VArray([]);
    reveal SeqSum();
  } else {
    lemma_non_empty_map_has_elements(c.v);
    var op :| op in c.v;
    var marshalled_op := MarshallOperationNumber(op);
    var marshalled_vote := MarshallVote(c.v[op]);
    var remainder := RemoveElt(c.v, op);
    var marshalled_remainder := MarshallVotes(CVotes(remainder));
    assert parse_Votes(marshalled_remainder) == CVotes(remainder);
    val := VArray([VTuple([marshalled_op, marshalled_vote])] + marshalled_remainder.a);

    // OBSERVE (everything below; not sure which bit is critical to proving the final ensures
    ghost var tuple := val.a[0];
    ghost var rest := val.a[1..];
    assert ValInGrammar(tuple, CVotes_grammar().elt);
    assert ValInGrammar(tuple.t[0], CVotes_grammar().elt.t[0]); 
    assert ValInGrammar(tuple.t[1], CVotes_grammar().elt.t[1]);
    ghost var op' := parse_OperationNumber(tuple.t[0]);
    ghost var vote' := parse_Vote(tuple.t[1]);
    ghost var others' := parse_Votes(VArray(val.a[1..]));
    ghost var m' := others'.v[op' := vote'];
    assert op' == op;
    assert vote' == c.v[op];
    assert others' == CVotes(remainder);
    assert m' == c.v;

    // Prove the SeqSum ensure
    calc {
      SeqSum(val.a);
        { reveal SeqSum(); }
      SizeOfV(val.a[0]) + SeqSum(val.a[1..]);
      <=  
      SizeOfV(val.a[0]) + |remainder| * (8 + (8 + 8) + (8 + ((24 + MaxAppRequestSize())*RequestBatchSizeLimit())));
      //SizeOfV(val.a[0]) + |remainder| * (8 + (8 + 8) + (24 + MaxAppRequestSize()));
        { lemma_SeqSum2(val.a[0]); }
      SizeOfV(val.a[0].t[0]) + SizeOfV(val.a[0].t[1]) + |remainder| * (8 + (8 + 8) + (8 + ((24 + MaxAppRequestSize())*RequestBatchSizeLimit())));
      <=   { lemma_VoteValValid(c.v[op], val.a[0].t[1]); lemma_VoteBound(c.v[op], val.a[0].t[1]); }
      8 + (8 + 8) + 8 + ((24 + MaxAppRequestSize())*|val.a[0].t[1].t[1].a|) + |remainder| * (8 + (8 + 8) + (8 + ((24 + MaxAppRequestSize())*RequestBatchSizeLimit())));
      <= { assert |val.a[0].t[1].t[1].a| <= RequestBatchSizeLimit(); lemma_mul_upper_bound(24 + MaxAppRequestSize(), 24 + MaxAppRequestSize(), |val.a[0].t[1].t[1].a|, RequestBatchSizeLimit());}
      8 + (8 + 8) + 8 + ((24 + MaxAppRequestSize())*RequestBatchSizeLimit()) + |remainder| * (8 + (8 + 8) + (8 + ((24 + MaxAppRequestSize())*RequestBatchSizeLimit())));
      1*(8 + (8 + 8) + (8 + ((24 + MaxAppRequestSize())*RequestBatchSizeLimit()))) + |remainder| * (8 + (8 + 8) + (8 + ((24 + MaxAppRequestSize())*RequestBatchSizeLimit())));
        { lemma_mul_is_distributive((8 + (8 + 8) + (8 + ((24 + MaxAppRequestSize())*RequestBatchSizeLimit()))), 1, |remainder|); }
      (1+|remainder|) * (8 + (8 + 8) + (8 + ((24 + MaxAppRequestSize())*RequestBatchSizeLimit())));
      |c.v| * (8 + (8 + 8) + (8 + ((24 + MaxAppRequestSize())*RequestBatchSizeLimit())));
    }
  }
}

method MarshallMessage_Request(c:CMessage) returns (val:V)
  requires c.CMessage_Request?
  requires Marshallable(c)
  ensures  ValInGrammar(val, CMessage_Request_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message_Request(val) == c
{
  var v := MarshallCAppRequest(c.val);
  val := VTuple([VUint64(c.seqno), v]);
}

method MarshallMessage_1a(c:CMessage) returns (val:V)
  requires c.CMessage_1a?
  requires Marshallable(c)
  ensures  ValInGrammar(val, CMessage_1a_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message_1a(val) == c
{
  val := MarshallBallot(c.bal_1a);
}

method MarshallMessage_1b(c:CMessage) returns (val:V)
  requires c.CMessage_1b?
  requires Marshallable(c)
  ensures  ValInGrammar(val, CMessage_1b_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message_1b(val) == c
  ensures  0 <= SizeOfV(val) < MaxPacketSize() - 8
{
  var bal := MarshallBallot(c.bal_1b);
  var log_truncation_point := MarshallOperationNumber(c.log_truncation_point);
  var votes := MarshallVotes(c.votes);
  val := VTuple([bal, log_truncation_point, votes]);
  // Prove the bound on SizeOfV(val)
  lemma_SeqSum3(val);
  assert ValInGrammar(val.t[0], CBallot_grammar());   // OBSERVE
  lemma_BallotBound(c.bal_1b, val.t[0]);
  assert ValInGrammar(val.t[1], COperationNumber_grammar());    // OBSERVE
  assert ValInGrammar(val.t[2], CVotes_grammar());    // OBSERVE
  calc {
    SizeOfV(val);
    16 + 8 + SizeOfV(val.t[2]);
    <= 
    16 + 8 + 8 + (|c.votes.v| * (8 + (8 + 8) + (8 + (24 + MaxAppRequestSize())*RequestBatchSizeLimit())));
    32 + (|c.votes.v| * (32 + (24 + MaxAppRequestSize()) * 100));
    < { lemma_mul_strict_inequality(|c.votes.v|, 8, (32 + (24 + MaxAppRequestSize()) * 100)); }
    32 + (8 * (32 + (24 + MaxAppRequestSize()) * 100));
    <
    MaxPacketSize() - 8;
  }
}

method MarshallMessage_2a(c:CMessage) returns (val:V)
  requires c.CMessage_2a?
  requires Marshallable_2a(c)
  ensures  ValInGrammar(val, CMessage_2a_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message_2a(val) == c
{
  var bal := MarshallBallot(c.bal_2a);
  var op := MarshallOperationNumber(c.opn_2a);
  var v := MarshallRequestBatch(c.val_2a);
  val := VTuple([bal, op, v]);
  assert forall u :: u in val.t ==> ValidVal(u);  // OBSERVE
  assert ValInGrammar(bal, CMessage_2a_grammar().t[0]);    // OBSERVE
  assert ValInGrammar(op,  CMessage_2a_grammar().t[1]);    // OBSERVE
  assert ValInGrammar(v, CMessage_2a_grammar().t[2]);    // OBSERVE
  assert ValInGrammar(val, CMessage_2a_grammar());    // OBSERVE
  assert ValidVal(val);
}

method MarshallMessage_2b(c:CMessage) returns (val:V)
  requires c.CMessage_2b?
  requires Marshallable_2b(c)
  ensures  ValInGrammar(val, CMessage_2b_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message_2b(val) == c
{
  var bal := MarshallBallot(c.bal_2b);
  var op := MarshallOperationNumber(c.opn_2b);
  var v := MarshallRequestBatch(c.val_2b);
  val := VTuple([bal, op, v]);
  assert ValInGrammar(bal, CBallot_grammar());    // OBSERVE
  assert ValInGrammar(op, COperationNumber_grammar());    // OBSERVE
  assert ValInGrammar(v, CRequestBatch_grammar());    // OBSERVE
  assert ValInGrammar(val, CMessage_2b_grammar());    // OBSERVE
}

method MarshallMessage_Heartbeat(c:CMessage) returns (val:V)
  requires c.CMessage_Heartbeat?
  requires Marshallable(c)
  ensures  ValInGrammar(val, CMessage_Heartbeat_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message_Heartbeat(val) == c
{
  var ballot := MarshallBallot(c.bal_heartbeat);
  var op := MarshallOperationNumber(c.opn_ckpt);
  val := VTuple([ballot, VUint64(if c.suspicious then 1 else 0), op]);
}

method MarshallMessage_Reply(c:CMessage) returns (val:V)
  requires c.CMessage_Reply?
  requires Marshallable(c)
  ensures  ValInGrammar(val, CMessage_Reply_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message_Reply(val) == c
{
  var app_val := MarshallCAppReply(c.reply);
  val := VTuple([VUint64(c.seqno_reply), app_val]);
}

method MarshallMessage_AppStateRequest(c:CMessage) returns (val:V)
  requires c.CMessage_AppStateRequest?
  requires Marshallable(c)
  ensures  ValInGrammar(val, CMessage_AppStateRequest_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message_AppStateRequest(val) == c
{
  var ballot := MarshallBallot(c.bal_state_req);
  var opn := MarshallOperationNumber(c.opn_state_req);
  val := VTuple([ballot, opn]);
}

method MarshallMessage_AppStateSupply(c:CMessage) returns (val:V)
  requires c.CMessage_AppStateSupply?
  requires Marshallable(c)
  ensures  ValInGrammar(val, CMessage_AppStateSupply_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message_AppStateSupply(val) == c
  ensures  0 <= SizeOfV(val) < MaxPacketSize() - 8
{
  var ballot := MarshallBallot(c.bal_state_supply);
  var opn_state_supply := MarshallOperationNumber(c.opn_state_supply);
  var app_state := MarshallCAppState(c.app_state);
  var reply_cache := MarshallReplyCache(c.reply_cache);
  val := VTuple([ballot, opn_state_supply, app_state, reply_cache]);

  // Prove the bound on SizeOfV(val)
  lemma_SeqSum4(val);
  assert ValInGrammar(val.t[0], CBallot_grammar());   // OBSERVE
  lemma_BallotBound(c.bal_state_supply, val.t[0]);
  assert ValInGrammar(val.t[1], COperationNumber_grammar());   // OBSERVE
  assert ValInGrammar(val.t[2], GByteArray);    // OBSERVE
  assert ValInGrammar(val.t[3], CReplyCache_grammar());    // OBSERVE
  calc {
    SizeOfV(val);
    SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3]);
    <=
    16 + 16 + MaxAppStateSize() + SizeOfV(val.t[3]);
    <=
    16 + 16 + MaxAppStateSize() + (8 + |c.reply_cache| * (8 + (8 + 8) + (24 + MaxAppRequestSize())));  
    16 + 16 + MaxAppStateSize() + (8 + |c.reply_cache| * (MaxAppRequestSize() + 48)); 
    40 + MaxAppStateSize() + |c.reply_cache| * (MaxAppRequestSize() + 48); 
    < { lemma_mul_strict_inequality(|c.reply_cache|, max_reply_cache_size(), (MaxAppRequestSize() + 48)); }
    40 + MaxAppStateSize() + max_reply_cache_size() * (MaxAppRequestSize() + 48); 
    <
    MaxPacketSize() - 8;
  }
}

method MarshallMessage_StartingPhase2(c:CMessage) returns (val:V)
  requires c.CMessage_StartingPhase2?
  requires Marshallable(c)
  ensures  ValInGrammar(val, CMessage_StartingPhase2_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message_StartingPhase2(val) == c
{
  var bal := MarshallBallot(c.bal_2);
  var op := MarshallOperationNumber(c.logTruncationPoint_2);
  val := VTuple([bal, op]);
}

method {:timeLimitMultiplier 2} MarshallMessage(c:CMessage) returns (val:V)
  requires Marshallable(c)
  ensures  ValInGrammar(val, CMessage_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message(val) == c
  ensures  c.CMessage_1b? ==> 0 <= SizeOfV(val) < MaxPacketSize()
  ensures  c.CMessage_AppStateSupply? ==> 0 <= SizeOfV(val) < MaxPacketSize()
{
  var start_time := Time.GetDebugTimeTicks();
  assert !c.CMessage_Invalid?;
  if c.CMessage_Request? {
    var msg := MarshallMessage_Request(c);  
    val := VCase(0, msg); 
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("MarshallMessage_Request", start_time, end_time);
  } else if c.CMessage_1a? {
    var msg := MarshallMessage_1a(c);  
    val := VCase(1, msg); 
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("MarshallMessage_1a", start_time, end_time);
  } else if c.CMessage_1b? {
    var msg := MarshallMessage_1b(c);  
    val := VCase(2, msg); 
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("MarshallMessage_1b", start_time, end_time);
  } else if c.CMessage_2a? {
    var msg := MarshallMessage_2a(c);  
    val := VCase(3, msg); 
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("MarshallMessage_2a", start_time, end_time);
  } else if c.CMessage_2b? {
    var msg := MarshallMessage_2b(c);  
    val := VCase(4, msg); 
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("MarshallMessage_2b", start_time, end_time);
  } else if c.CMessage_Heartbeat? {
    var msg := MarshallMessage_Heartbeat(c);  
    val := VCase(5, msg); 
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("MarshallMessage_Heartbeat", start_time, end_time);
  } else if c.CMessage_Reply? {
    var msg := MarshallMessage_Reply(c);
    val := VCase(6, msg); 
    assert CMessage_grammar().cases[6] == CMessage_Reply_grammar();
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("MarshallMessage_Reply", start_time, end_time);
  } else if c.CMessage_AppStateRequest? {
    var msg := MarshallMessage_AppStateRequest(c);  
    val := VCase(7, msg); 
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("MarshallMessage_AppStateRequest", start_time, end_time);
  } else if c.CMessage_AppStateSupply? {
    var msg := MarshallMessage_AppStateSupply(c);  
    val := VCase(8, msg); 
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("MarshallMessage_AppStateSupply", start_time, end_time);
  } else if c.CMessage_StartingPhase2? {
    var msg := MarshallMessage_StartingPhase2(c);  
    val := VCase(9, msg); 
    var end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("MarshallMessage_StartingPhase2", start_time, end_time);
  }

    // The following should work just as well as above, but it doesn't.  Not sure why. 
//    var msg:V;
//    match c 
//      case CMessage_Request(_,_) => msg := MarshallMessage_Request(c);
//      case CMessage_1a(_)        => msg := MarshallMessage_1a(c);  assert ValInGrammar(msg, CMessage_1a_grammar());
//      case CMessage_1b(_,_)      => msg := MarshallMessage_1b(c);
//      case CMessage_2a(_,_,_)    => msg := MarshallMessage_2a(c);
//      case CMessage_2b(_,_,_)    => msg := MarshallMessage_2b(c);
//      case CMessage_Decision(_,_)=> msg := MarshallMessage_Decision(c);
//    
//    assert CMessage_grammar().cases[1] == CMessage_1a_grammar();
//
//    match c 
//      case CMessage_Request(_,_) => val := VCase(0, msg); 
//      case CMessage_1a(_)        => val := VCase(1, msg); 
//      case CMessage_1b(_,_)      => val := VCase(2, msg); 
//      case CMessage_2a(_,_,_)    => val := VCase(3, msg); 
//      case CMessage_2b(_,_,_)    => val := VCase(4, msg); 
//      case CMessage_Decision(_,_)=> val := VCase(5, msg); 
//    }
}

lemma lemma_SeqSum2(val:V)
  requires val.VTuple?
  requires |val.t| == 2
  ensures  SizeOfV(val) == SizeOfV(val.t[0]) + SizeOfV(val.t[1])
{
  calc {
    SeqSum(val.t);
      { reveal SeqSum(); }
    SizeOfV(val.t[0]) + SeqSum(val.t[1..]);
      { reveal SeqSum(); }
    SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SeqSum(val.t[2..]);
      { assert val.t[2..] == []; }        // OBSERVE
    SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SeqSum([]);
      { reveal SeqSum(); }
    SizeOfV(val.t[0]) + SizeOfV(val.t[1]);
  }
}

lemma lemma_SeqSum3(val:V)
  requires val.VTuple?
  requires |val.t| == 3
  ensures  SizeOfV(val) == SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2])
{
  calc {
    SeqSum(val.t);
      { reveal SeqSum(); }
    SizeOfV(val.t[0]) + SeqSum(val.t[1..]);
      { reveal SeqSum(); }
    SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SeqSum(val.t[2..]);
      { reveal SeqSum(); }
    SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SeqSum(val.t[3..]);
      { assert val.t[3..] == []; }        // OBSERVE
    SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SeqSum([]);
      { reveal SeqSum(); }
    SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]);
  }
}

lemma lemma_SeqSum4(val:V)
  requires val.VTuple?
  requires |val.t| == 4
  ensures  SizeOfV(val) == SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3])
{
  calc {
    SeqSum(val.t);
      { reveal SeqSum(); }
    SizeOfV(val.t[0]) + SeqSum(val.t[1..]);
      { reveal SeqSum(); }
    SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SeqSum(val.t[2..]);
      { reveal SeqSum(); }
    SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SeqSum(val.t[3..]);
      { reveal SeqSum(); }
    SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3]) + SeqSum(val.t[4..]);
      { assert val.t[4..] == []; }        // OBSERVE
    SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3]) + SeqSum([]);
      { reveal SeqSum(); }
    SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3]);
  }
}

lemma lemma_BallotBound(c:CBallot, val:V)
  requires ValInGrammar(val, CBallot_grammar())
  requires ValidVal(val)
  requires parse_Ballot(val) == c
  ensures  SizeOfV(val) == 16
{
  assert |val.t| == |CBallot_grammar().t| == 2;
  assert ValInGrammar(val.t[0], GUint64);
  assert ValInGrammar(val.t[1], GUint64);
  lemma_SeqSum2(val);
  assert SeqSum(val.t) == 16;
}

lemma lemma_CRequestBound(c:CRequest, val:V)
  requires ValInGrammar(val, CRequest_grammar())
  requires ValidRequest(c)
  requires parse_Request(val) == c
  ensures  SizeOfV(val) <= 24 + MaxAppRequestSize()
{
  ghost var gtuple := GTuple([EndPoint_grammar(), GUint64, GByteArray]);
  assert ValInGrammar(val, gtuple);

  lemma_SeqSum3(val);
  assert ValInGrammar(val.t[0], gtuple.t[0]);
  assert ValInGrammar(val.t[1], gtuple.t[1]);
  assert SizeOfV(val.t[0]) == 8;
  assert SizeOfV(val.t[1]) == 8;
  assert SizeOfV(val.t[2]) <= 8 + MaxAppRequestSize();
}

lemma lemma_CRequestBatchBound(c:CRequestBatch, val:V)
  requires ValInGrammar(val, CRequestBatch_grammar())
  requires ValidRequestBatch(c)
  requires parse_RequestBatch(val) == c
  decreases |c|
  ensures  SeqSum(val.a) <= (24 + MaxAppRequestSize())*|val.a|
{
  //ghost var gtuple := GTuple([EndPoint_grammar(), GUint64, GByteArray]);
  ghost var garray := GArray(CRequest_grammar());
  assert ValInGrammar(val, garray);
  reveal SeqSum();
  if |val.a| == 0 {
    assert SeqSum(val.a) <= (24 + MaxAppRequestSize())*|val.a|;
  } else {
    var req := parse_Request(val.a[0]);
    var restVal:V := VArray(val.a[1..]);
    var rest := parse_RequestBatch(restVal);
    assert c == [req] + rest;
    var x := 24 + MaxAppRequestSize();
    var N := |val.a|;
    lemma_CRequestBatchBound(rest, restVal);
    assert SeqSum(val.a[1..]) <= (x)*(N-1);
    lemma_CRequestBound(req, val.a[0]);
    assert SizeOfV(val.a[0]) <= x;
    assert SeqSum(val.a) == SizeOfV(val.a[0]) + SeqSum(val.a[1..]);
    assert |val.a| == |val.a[1..]| + 1;
    lemma_mul_is_distributive(x, N-1, 1);
    assert SeqSum(val.a) <= (x)*N;
  }
}

lemma lemma_ReplyBound(c:CReply, val:V)
  requires ValInGrammar(val, CReply_grammar())
  requires ValidReply(c)
  requires parse_Reply(val) == c
  ensures  SizeOfV(val) <= 24 + MaxAppRequestSize()
{
  ghost var gtuple := GTuple([EndPoint_grammar(), GUint64, GByteArray]);
  assert ValInGrammar(val, gtuple);
  lemma_SeqSum3(val);
  assert ValInGrammar(val.t[0], gtuple.t[0]);
  assert ValInGrammar(val.t[1], gtuple.t[1]);
  assert SizeOfV(val.t[0]) == 8;
  assert SizeOfV(val.t[1]) == 8;
  assert SizeOfV(val.t[2]) <= 8 + MaxAppRequestSize();
}

lemma lemma_ReplyValValid(c:CReply, val:V)
  requires ValInGrammar(val, CReply_grammar())
  requires ValidReply(c)
  requires parse_Reply(val) == c
  ensures ValidVal(val)
{
  lemma_SeqSum3(val);
  assert ValInGrammar(val.t[0], EndPoint_grammar());    // OBSERVE
  assert ValInGrammar(val.t[1], GUint64);    // OBSERVE
  assert ValInGrammar(val.t[2], GByteArray);    // OBSERVE

  // Lots of OBSERVE below
  ghost var gtuple := GTuple([EndPoint_grammar(), GUint64, GByteArray]);
  assert ValInGrammar(val, gtuple);               
  assert ValInGrammar(val.t[0], gtuple.t[0]);
  assert ValInGrammar(val.t[1], gtuple.t[1]);
  assert ValInGrammar(val.t[2], gtuple.t[2]);
  assert ValidVal(val.t[0]);
  assert ValidVal(val.t[1]);
  assert ValidVal(val.t[2]);
}


lemma {:timeLimitMultiplier 2} lemma_VoteValValid(c:CVote, val:V)
  requires ValInGrammar(val, CVote_grammar())
  requires ValidVote(c)
  requires parse_Vote(val) == c
  ensures ValidVal(val)
{
  lemma_SeqSum2(val);
  assert ValInGrammar(val.t[0], CBallot_grammar());    // OBSERVE
  assert ValInGrammar(val.t[1], CRequestBatch_grammar());    // OBSERVE
  lemma_BallotBound(c.max_value_bal, val.t[0]);
  lemma_CRequestBatchBound(c.max_val, val.t[1]);

  ghost var garray := GArray(CRequest_grammar());
  assert ValInGrammar(val.t[1], garray);
  ghost var gtuple := GTuple([EndPoint_grammar(), GUint64, GByteArray]);
  forall i, v | 0 <= i < |val.t[1].a|&& v == val.t[1].a[i]
    ensures ValidVal(v)
  {
    assert ValInGrammar(v, gtuple);
    assert ValInGrammar(v.t[0], gtuple.t[0]);
    assert ValInGrammar(v.t[1], gtuple.t[1]);
    assert ValInGrammar(v.t[2], gtuple.t[2]);
    assert ValidVal(v.t[0]);
    assert ValidVal(v.t[1]);
    assert c.max_val[i] in c.max_val; // OBSERVE antecedent to determine that ValidRequest(c.max_val[i])
    assert ValidVal(v.t[2]);
    assert ValidVal(v);
  }
  assert |val.t[1].a| == |c.max_val|;
  assert ValidVote(c);
  assert ValidRequestBatch(c.max_val);
  assert |c.max_val| < 0x1_0000_0000;
  assert |val.t[1].a| < 0x1_0000_0000_0000_0000;
  assert forall v :: v in val.t[1].a ==> ValidVal(v);

  calc ==> {
    true;
    ValidVal(val.t[0]); 
    ValidVal(val.t[0]) && ValidVal(val.t[1]);
    ValidVal(val);
  }
}

lemma lemma_VoteBound(c:CVote, val:V)
  requires ValInGrammar(val, CVote_grammar())
  requires ValInGrammar(val.t[1], CRequestBatch_grammar())
  requires ValidVal(val)
  requires ValidVote(c)
  requires parse_Vote(val) == c
  ensures  SizeOfV(val) <= (8 + 8) + 8 + ((24 + MaxAppRequestSize())*|val.t[1].a|)
{
  lemma_SeqSum2(val);
  assert ValInGrammar(val.t[0], CBallot_grammar());    // OBSERVE
  assert ValInGrammar(val.t[1], CRequestBatch_grammar());    // OBSERVE

  lemma_BallotBound(c.max_value_bal, val.t[0]);
  lemma_CRequestBatchBound(c.max_val, val.t[1]);
}

lemma lemma_MarshallableBound(c:CMessage, val:V)
  requires Marshallable(c)
  requires ValInGrammar(val, CMessage_grammar())
  requires ValidVal(val)
  requires parse_Message(val) == c
  ensures  !c.CMessage_1b? && !c.CMessage_AppStateSupply? ==> 0 <= SizeOfV(val) < MaxPacketSize()
{
  assert !c.CMessage_Invalid?;
  if c.CMessage_Request? {
    lemma_SeqSum2(val.val);
    assert ValInGrammar(val.val.t[0], GUint64);             // OBSERVE
    assert ValInGrammar(val.val.t[1], GByteArray);    // OBSERVE
  } else if c.CMessage_1a? {
    assert ValInGrammar(val.val, CMessage_1a_grammar());    // OBSERVE
    assert ValInGrammar(val.val, CBallot_grammar());        // OBSERVE
    lemma_BallotBound(c.bal_1a, val.val);
    assert SizeOfV(val) == 24;
/*  We prove this case during marshalling
  } else if c.CMessage_1b? {
*/
  } else if c.CMessage_2a? {
    lemma_SeqSum3(val.val);
    lemma_BallotBound(c.bal_2a, val.val.t[0]);
    assert SizeOfV(val.val.t[0]) == 16;
    assert ValInGrammar(val.val.t[1], GUint64);             // OBSERVE
    assert SizeOfV(val.val.t[1]) == 8;
    assert ValInGrammar(val.val.t[2], CRequestBatch_grammar());    // OBSERVE
    //assert SizeOfV(val.val.t[2]) == 8 + |val.val.t[2].b| == 8 + |c.val_2a.v|;
    lemma_CRequestBatchBound(c.val_2a, val.val.t[2]);
    assert |val.val.t[2].a| == |c.val_2a|;
    assert |c.val_2a| <= RequestBatchSizeLimit();
        
    calc {
      SizeOfV(val.val.t[2]);
      8 + SeqSum(val.val.t[2].a);
      <=
      8 + (24 + MaxAppRequestSize())*|val.val.t[2].a|;
      <= { lemma_mul_is_commutative(|val.val.t[2].a|, RequestBatchSizeLimit());
          lemma_mul_is_commutative(|val.val.t[2].a|, 24 + MaxAppRequestSize());
          lemma_mul_inequality(|val.val.t[2].a|, RequestBatchSizeLimit(), 24 + MaxAppRequestSize());
        }
      8 + (24 + MaxAppRequestSize())*RequestBatchSizeLimit();
    }
  } else if c.CMessage_2b? {
    lemma_SeqSum3(val.val);
    lemma_BallotBound(c.bal_2b, val.val.t[0]);
    assert SizeOfV(val.val.t[0]) == 16;
    assert ValInGrammar(val.val.t[1], GUint64);             // OBSERVE
    assert SizeOfV(val.val.t[1]) == 8;
    assert ValInGrammar(val.val.t[2], CRequestBatch_grammar());    // OBSERVE
    //assert SizeOfV(val.val.t[2]) == 8 + |val.val.t[2].b| == 8 + |c.val_2b.v|;
    lemma_CRequestBatchBound(c.val_2b, val.val.t[2]);
    calc {
      SizeOfV(val.val.t[2]);
      8 + SeqSum(val.val.t[2].a);
      <=
      8 + (24 + MaxAppRequestSize())*|val.val.t[2].a|;
      <= { lemma_mul_is_commutative(|val.val.t[2].a|, RequestBatchSizeLimit());
          lemma_mul_is_commutative(|val.val.t[2].a|, 24 + MaxAppRequestSize());
          lemma_mul_inequality(|val.val.t[2].a|, RequestBatchSizeLimit(), 24 + MaxAppRequestSize());
        }
      8 + (24 + MaxAppRequestSize())*RequestBatchSizeLimit();
    }
  } else if c.CMessage_Heartbeat? {
    lemma_SeqSum3(val.val);
    assert ValInGrammar(val.val.t[0], CBallot_grammar());   // OBSERVE
    assert ValInGrammar(val.val.t[1], GUint64);             // OBSERVE
    assert ValInGrammar(val.val.t[2], COperationNumber_grammar());  // OBSERVE
    lemma_BallotBound(c.bal_heartbeat, val.val.t[0]);
  } else if c.CMessage_Reply? {
    lemma_SeqSum2(val.val);
    assert ValInGrammar(val.val.t[0], GUint64);     // OBSERVE
    assert ValInGrammar(val.val.t[1], GByteArray);  // OBSERVE
  } else if c.CMessage_AppStateRequest? {
    lemma_SeqSum2(val.val);
    assert ValInGrammar(val.val.t[0], CBallot_grammar());           // OBSERVE
    assert ValInGrammar(val.val.t[1], COperationNumber_grammar());  // OBSERVE
    lemma_BallotBound(c.bal_state_req, val.val.t[0]);
    assert 0 <= SizeOfV(val) < MaxPacketSize();
    // assert SizeOfV(val.val.t[0]) == 8;
/*  We prove this case during marshalling
  } else if c.CMessage_AppStateSupply? {
*/
  } else if c.CMessage_StartingPhase2? {
    lemma_SeqSum2(val.val);
    assert ValInGrammar(val.val.t[0], CBallot_grammar());   // OBSERVE
    assert ValInGrammar(val.val.t[1], COperationNumber_grammar());  // OBSERVE
    lemma_BallotBound(c.bal_2, val.val.t[0]);
  }
}

////////////////////////////////////////////////////////////////////////
// These functions need to be here, rather than CMessageRefinements.i.dfy,
// since they depend on PaxosDemarshallData
////////////////////////////////////////////////////////////////////////
function AbstractifyBufferToRslPacket(src:EndPoint, dst:EndPoint, data:seq<byte>) : RslPacket
  requires EndPointIsValidIPV4(src)
  requires EndPointIsValidIPV4(dst)
{
  LPacket(AbstractifyEndPointToNodeIdentity(dst),
          AbstractifyEndPointToNodeIdentity(src),
          AbstractifyCMessageToRslMessage(PaxosDemarshallData(data)))
}

predicate BufferRefinementAgreesWithMessageRefinement(msg:CMessage, marshalled:seq<byte>)
  requires CMessageIsAbstractable(msg)
  requires CMessageIsAbstractable(msg)
{
  forall src, dst :: (EndPointIsValidIPV4(src) && EndPointIsValidIPV4(dst)) ==>

            (AbstractifyBufferToRslPacket(src, dst, marshalled)
            == LPacket(AbstractifyEndPointToNodeIdentity(dst), AbstractifyEndPointToNodeIdentity(src), AbstractifyCMessageToRslMessage(msg)))
}

function AbstractifyUdpPacketToRslPacket(udp:UdpPacket) : RslPacket
  requires UdpPacketIsAbstractable(udp)
{
  AbstractifyBufferToRslPacket(udp.src, udp.dst, udp.msg)
}

predicate UdpPacketIsAbstractable(udp:UdpPacket)
{
  && EndPointIsValidIPV4(udp.src)
  && EndPointIsValidIPV4(udp.dst)
}

predicate UdpPacketsIsAbstractable(udpps:set<UdpPacket>)
{
  forall p :: p in udpps ==> UdpPacketIsAbstractable(p)
}

lemma lemma_CMessageGrammarValid()
  ensures ValidGrammar(CMessage_grammar())
{
  var g := CMessage_grammar();
  assert |g.cases| < 0x1_0000_0000_0000_0000;
  assert ValidGrammar(CMessage_Request_grammar());
  assert ValidGrammar(CMessage_1a_grammar());
  assert ValidGrammar(CMessage_1b_grammar());
  assert ValidGrammar(CMessage_2a_grammar());
  assert ValidGrammar(CMessage_2b_grammar());
  assert ValidGrammar(CMessage_Heartbeat_grammar());
  assert ValidGrammar(CMessage_Reply_grammar());
  assert ValidGrammar(CMessage_AppStateRequest_grammar());
  assert ValidGrammar(CMessage_AppStateSupply_grammar());
  assert ValidGrammar(CMessage_StartingPhase2_grammar());
}

method PaxosMarshall(msg:CMessage) returns (data:array<byte>)
  requires CMessageIsAbstractable(msg)
  requires Marshallable(msg)
  ensures fresh(data)
  ensures UdpPacketBound(data[..])
  ensures Marshallable(PaxosDemarshallData(data[..]))
  ensures BufferRefinementAgreesWithMessageRefinement(msg, data[..])
{
  var marshall_start_time := Time.GetDebugTimeTicks();
  var val := MarshallMessage(msg);
  var marshall_end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("PaxosMarshall_MarshallMessage", marshall_start_time, marshall_end_time);
  lemma_MarshallableBound(msg, val);
  lemma_CMessageGrammarValid();
  var generic_marshall_start_time := Time.GetDebugTimeTicks();
  data := Marshall(val, CMessage_grammar());
  var generic_marshall_end_time := Time.GetDebugTimeTicks();

  assert !msg.CMessage_Invalid?;
  if msg.CMessage_Request? {
    RecordTimingSeq("GenericMarshallMessage_Request", generic_marshall_start_time, generic_marshall_end_time);
  } else if msg.CMessage_1a? {
    RecordTimingSeq("GenericMarshallMessage_1a", generic_marshall_start_time, generic_marshall_end_time);
  } else if msg.CMessage_1b? {
    RecordTimingSeq("GenericMarshallMessage_1b", generic_marshall_start_time, generic_marshall_end_time);
  } else if msg.CMessage_2a? {
    RecordTimingSeq("GenericMarshallMessage_2a", generic_marshall_start_time, generic_marshall_end_time);
  } else if msg.CMessage_2b? {
    RecordTimingSeq("GenericMarshallMessage_2b", generic_marshall_start_time, generic_marshall_end_time);
  } else if msg.CMessage_Heartbeat? {
    RecordTimingSeq("GenericMarshallMessage_Heartbeat", generic_marshall_start_time, generic_marshall_end_time);
  } else if msg.CMessage_Reply? {
    RecordTimingSeq("GenericMarshallMessage_Reply", generic_marshall_start_time, generic_marshall_end_time);
  } else if msg.CMessage_AppStateRequest? {
    RecordTimingSeq("GenericMarshallMessage_AppStateRequest", generic_marshall_start_time, generic_marshall_end_time);
  } else if msg.CMessage_AppStateSupply? {
    RecordTimingSeq("GenericMarshallMessage_AppStateSupply", generic_marshall_start_time, generic_marshall_end_time);
  } else if msg.CMessage_StartingPhase2? {
    RecordTimingSeq("GenericMarshallMessage_StartingPhase2", generic_marshall_start_time, generic_marshall_end_time);
  }

  forall src, dst | EndPointIsValidIPV4(src) && EndPointIsValidIPV4(dst) 
    ensures AbstractifyBufferToRslPacket(src, dst, data[..])
              == LPacket(AbstractifyEndPointToNodeIdentity(dst), AbstractifyEndPointToNodeIdentity(src), AbstractifyCMessageToRslMessage(msg));
  {
    calc {
      AbstractifyBufferToRslPacket(src, dst, data[..]);
      LPacket(AbstractifyEndPointToNodeIdentity(dst),
              AbstractifyEndPointToNodeIdentity(src),
              AbstractifyCMessageToRslMessage(PaxosDemarshallData(data[..])));
      LPacket(AbstractifyEndPointToNodeIdentity(dst),
              AbstractifyEndPointToNodeIdentity(src),
              AbstractifyCMessageToRslMessage(PaxosDemarshallData(data[..])));
      LPacket(AbstractifyEndPointToNodeIdentity(dst), AbstractifyEndPointToNodeIdentity(src), AbstractifyCMessageToRslMessage(msg));
    }
  }
}

//////////////////////////////////////////////////////////////////////////////
// Sendable predicates

predicate CPacketIsSendable(cpacket:CPacket)
{
  && CMessageIsValid(cpacket.msg) 
  && CPacketIsAbstractable(cpacket)
  && EndPointIsValidIPV4(cpacket.src)
}

predicate CPacketSetIsSendable(cps:set<CPacket>)
{
  forall p :: p in cps ==> CPacketIsSendable(p)
}

predicate CPacketSeqIsValid(cps:seq<CPacket>)
{
  && CPacketSeqIsAbstractable(cps)
  && |cps| < 0xFFFF_FFFF_FFFF_FFFF
  && forall i :: 0<=i<|cps| ==> CPacketIsSendable(cps[i])
}

predicate CBroadcastIsValid(broadcast:CBroadcast) 
{
  && CBroadcastIsAbstractable(broadcast)
  && (broadcast.CBroadcast? ==>
      && Marshallable(broadcast.msg)
      && 0 <= |broadcast.dsts| < 0xFFFF_FFFF_FFFF_FFFF)
}

predicate OutboundPacketsIsValid(out:OutboundPackets)
{
  match out
    case Broadcast(broadcast) => CBroadcastIsValid(broadcast)
    case OutboundPacket(p) => p.Some? ==> CPacketIsSendable(p.v)
    case PacketSequence(s) => |s| < 0xFFFF_FFFF_FFFF_FFFF 
                              && (forall p :: p in s ==> CPacketIsSendable(p))
//        case OutboundPacket(Some(p)) => CPacketIsSendable(p)
//        case OutboundPacket(None) => true
}

}
