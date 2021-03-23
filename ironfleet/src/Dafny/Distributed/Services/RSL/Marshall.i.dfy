include "AbstractService.s.dfy"
include "../../Protocol/RSL/Message.i.dfy"
include "../../Impl/RSL/PacketParsing.i.dfy"

module MarshallProof_i {
import opened Native__NativeTypes_s
import opened AppStateMachine_i
import opened AbstractServiceRSL_s 
import opened LiveRSL__AppInterface_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__Message_i
import opened LiveRSL__PacketParsing_i
import opened Common__GenericMarshalling_i
import opened Common__Util_i
import opened Math__power2_i

lemma lemma_ParseValCorrectVCase(data:seq<byte>, v:V, g:G) returns (caseId:uint64, val:V, rest:seq<byte>)
  requires ValInGrammar(v, g)
  requires |data| < 0x1_0000_0000_0000_0000
  requires ValidGrammar(g)
  requires parse_Val(data, g).0.Some?
  requires parse_Val(data, g).0.v == v
  requires g.GTaggedUnion?
  ensures  parse_Uint64(data).0.Some?
  ensures  caseId == parse_Uint64(data).0.v.u
  ensures  0 <= caseId as int < |g.cases|
  ensures  rest == parse_Uint64(data).1
  ensures         parse_Val(rest, g.cases[caseId]).0.Some?
  ensures  val == parse_Val(rest, g.cases[caseId]).0.v
  ensures  v == VCase(caseId, val)
  ensures  ValInGrammar(val, g.cases[caseId])
{
  reveal parse_Val();
  caseId := parse_Uint64(data).0.v.u;
  var tuple := parse_Val(parse_Uint64(data).1, g.cases[caseId]);
  val := tuple.0.v;
  rest := parse_Uint64(data).1;
}

lemma {:fuel ValInGrammar,3} lemma_ParseValCorrectTuple2(data:seq<byte>, v:V, g:G) returns (val0:V, val1:V, rest:seq<byte>)
  requires ValInGrammar(v, g)
  requires |data| < 0x1_0000_0000_0000_0000
  requires ValidGrammar(g)
  requires parse_Val(data, g).0.Some?
  requires parse_Val(data, g).0.v == v
  requires g.GTuple?
  requires |g.t| == 2

  ensures         parse_Val(data, g.t[0]).0.Some?
  ensures val0 == parse_Val(data, g.t[0]).0.v
  ensures ValInGrammar(val0, g.t[0])

  ensures rest == parse_Val(data, g.t[0]).1
  ensures         parse_Val(rest, g.t[1]).0.Some?
  ensures val1 == parse_Val(rest, g.t[1]).0.v
  ensures ValInGrammar(val1, g.t[1])

  ensures v == VTuple([val0, val1])
{
  reveal parse_Val();
  reveal parse_Tuple_contents();

  // Prove that v == VTuple([val0, val1]);
  assert parse_Val(data, g).0.v == parse_Tuple(data, g.t).0.v == VTuple(parse_Tuple_contents(data, g.t).0.v);

  assert parse_Tuple_contents(data, g.t).0.v == [parse_Val(data, g.t[0]).0.v] 
                                                + parse_Tuple_contents(parse_Val(data, g.t[0]).1, g.t[1..]).0.v;

  assert [parse_Val(data, g.t[0]).0.v] + parse_Tuple_contents(parse_Val(data, g.t[0]).1, g.t[1..]).0.v
         == [parse_Val(data, g.t[0]).0.v] + [parse_Val(parse_Val(data, g.t[0]).1, g.t[1]).0.v];

  assert [parse_Val(data, g.t[0]).0.v] + [parse_Val(parse_Val(data, g.t[0]).1, g.t[1]).0.v]
         == [parse_Val(data, g.t[0]).0.v, parse_Val(parse_Val(data, g.t[0]).1, g.t[1]).0.v];
  assert |v.t| == 2;
  var tuple0 := parse_Val(data, g.t[0]);
  assert tuple0.0.Some?;
  val0,rest := tuple0.0.v, tuple0.1;
  var tuple1 := parse_Val(rest, g.t[1]);
  var foo;
  val1,foo := tuple1.0.v, tuple1.1;

  // Prove that rest is set correctly
  assert parse_Val(data, g).1 == parse_Tuple(data, g.t).1 == parse_Tuple_contents(data, g.t).1;
  assert parse_Tuple_contents(data, g.t).1 == parse_Tuple_contents(parse_Val(data, g.t[0]).1, g.t[1..]).1;
  //assert parse_Tuple_contents(parse_Val(data, g.t[0]).1, g.t[1..]).1 == rest;
}

lemma lemma_ParseValCorrectVUint64(data:seq<byte>, v:V, g:G) returns (u:uint64, rest:seq<byte>)
  requires ValInGrammar(v, g)
  requires |data| < 0x1_0000_0000_0000_0000
  requires ValidGrammar(g)
  requires parse_Val(data, g).0.Some?
  requires parse_Val(data, g).0.v == v
  requires g.GUint64?
  ensures  parse_Uint64(data).0.Some?
  ensures  u == parse_Uint64(data).0.v.u
  ensures  v == VUint64(u)
  ensures  rest == parse_Val(data, g).1
{
  reveal parse_Val();
  u := parse_Uint64(data).0.v.u;
  rest := parse_Uint64(data).1;
}

lemma {:fuel ValInGrammar,3} {:fuel SizeOfV,3} lemma_SizeOfCMessageRequest1(v:V)
  requires ValInGrammar(v, CMessage_grammar())
  requires ValInGrammar(v.val, CMessage_Request_grammar())
  requires v.val.t[1].c == 1
  ensures  SizeOfV(v) == 32
{
  lemma_SeqSum2(v.val);
  reveal SeqSum();
}

lemma {:fuel ValInGrammar,3} {:fuel SizeOfV,3} lemma_SizeOfCMessageRequest(v:V)
  requires ValInGrammar(v, CMessage_grammar())
  requires ValInGrammar(v.val, CMessage_Request_grammar())
  requires v.val.t[1].c == 0 || v.val.t[1].c == 2
  ensures  SizeOfV(v) == 24
{
  lemma_SeqSum2(v.val);
  reveal SeqSum();
}

lemma ByteArrayOf8(bytes:seq<byte>, b:byte)
  requires |bytes| == 8
  requires SeqByteToUint64(bytes) == b as uint64
  ensures bytes == [ 0, 0, 0, 0, 0, 0, 0, b]
{
}

lemma ByteConcat24(bytes:seq<byte>)
  requires |bytes| >= 24
  ensures bytes[0..24] == bytes[0..8] + bytes[8..16] + bytes[16..24]
{
}

lemma ByteConcat32(bytes:seq<byte>)
  requires |bytes| >= 32
  ensures bytes[0..32] == bytes[0..8] + bytes[8..16] + bytes[16..24] + bytes[24..32]
{
}

lemma {:timeLimitMultiplier 5} {:fuel ValInGrammar,3} lemma_ParseMarshallRequest(bytes:seq<byte>, msg:RslMessage)
  requires msg.RslMessage_Request?
  requires CMessageIsAbstractable(PaxosDemarshallData(bytes))
  requires AbstractifyCMessageToRslMessage(PaxosDemarshallData(bytes)) == msg
  ensures  bytes == MarshallServiceRequest(msg.seqno_req, msg.val)
{
  var cmsg := PaxosDemarshallData(bytes);
  assert cmsg.CMessage_Request?;
  assert cmsg.seqno as int == msg.seqno_req;
  assert AbstractifyCAppMessageToAppMessage(cmsg.val) == msg.val;

  var data := bytes;
  var g := CMessage_grammar();
  var v := DemarshallFunc(data, g);

  // Walk through the generic parsing process
  var msgCaseId, msgCaseVal, rest0 := lemma_ParseValCorrectVCase(data, v, g);
  var seqnoVal, appVal, rest1 := lemma_ParseValCorrectTuple2(rest0, msgCaseVal, g.cases[msgCaseId]);
  var appCaseId, appCaseVal, rest2 := lemma_ParseValCorrectVCase(rest1, appVal, g.cases[msgCaseId].t[1]);

  // Prove that the first 8 bytes are correct
  assert msgCaseId == 0;
  assert 0 == SeqByteToUint64(bytes[0..8]);
  ByteArrayOf8(bytes[0..8], 0);
  // Prove that the next 8 bytes are correct
  var u, rest := lemma_ParseValCorrectVUint64(rest0, seqnoVal, GUint64);
  assert msg.seqno_req == u as int;
  assert SeqByteToUint64(rest0[0..8]) == u;
  assert Uint64ToSeqByte(u) == AbstractServiceRSL_s.Uint64ToBytes(u);
  lemma_BEByteSeqToInt_BEUintToSeqByte_invertability();
  assert rest0[0..8] == Uint64ToSeqByte(msg.seqno_req as uint64);
  assert data[8..16] == rest0[0..8];
  reveal parse_Val();
  if cmsg.val.CAppIncrement? {
    assert appCaseId == 0;
    assert 0 == SeqByteToUint64(rest1[0..8]);
            
    ByteArrayOf8(rest1[0..8], 0);
    calc { 
      data[0..24];
        { assert |data| >= 24; ByteConcat24(data); }
      data[0..8] + data[8..16] + data[16..24];
      [ 0, 0, 0, 0, 0, 0, 0, 0] + Uint64ToSeqByte(msg.seqno_req as uint64) + [ 0, 0, 0, 0, 0, 0, 0, 0]; 
    }
    lemma_SizeOfCMessageRequest(v);
    assert SizeOfV(v) == 24;
    if |data| > 24 {
      assert data[0..|data|] == data[..];
      lemma_parse_Val_view_specific_size(data, v, CMessage_grammar(), 0, |data|);
      lemma_parse_Val_view_specific(data, v, CMessage_grammar(), 0, |data|);
      assert false;
    }
  } else if cmsg.val.CAppReply? {
    // Prove that the next 8 bytes are correct
    var u_app, rest_app := lemma_ParseValCorrectVUint64(rest2, appCaseVal, GUint64);

    assert appCaseId == 1;
    assert 1 == SeqByteToUint64(rest1[0..8]);
            
    ByteArrayOf8(rest1[0..8], 1);
    assert msg.val.response == u_app;
    assert SeqByteToUint64(rest2[..8]) == u_app;
    assert Uint64ToSeqByte(u_app) == AbstractServiceRSL_s.Uint64ToBytes(u_app);
    lemma_BEByteSeqToInt_BEUintToSeqByte_invertability();
    assert rest2[..8] == Uint64ToSeqByte(msg.val.response as uint64);
    assert data[16..24] == rest0[8..16];
    calc {
      data[16..24];
      rest0[8..16];
      rest1[..8];
    }
    assert data[24..32] == rest0[16..24];
    calc {
      data[24..32];
      rest0[16..24];
      rest1[8..16];
      rest2[..8];
    }
    calc { 
      data[0..32];
        { assert |data| >= 32; ByteConcat32(data); }
      data[0..8] + data[8..16] + data[16..24] + data[24..32];
      [ 0, 0, 0, 0, 0, 0, 0, 0] + Uint64ToSeqByte(msg.seqno_req as uint64) + [ 0, 0, 0, 0, 0, 0, 0, 1] + Uint64ToSeqByte(msg.val.response as uint64); 
    }
    //assert data[0..32] == [ 0, 0, 0, 0, 0, 0, 0, 0] + Uint64ToSeqByte(msg.seqno_req as uint64) + [ 0, 0, 0, 0, 0, 0, 0, 1] + Uint64ToSeqByte(msg.val.response as uint64);
    lemma_SizeOfCMessageRequest1(v);
    if |data| > 32 {
      assert data[0..|data|] == data[..];
      lemma_parse_Val_view_specific_size(data, v, CMessage_grammar(), 0, |data|);
      lemma_parse_Val_view_specific(data, v, CMessage_grammar(), 0, |data|);
      assert false;
    }
    assert |data| == 32;
    assert data == MarshallServiceRequest(msg.seqno_req, msg.val);
  } else {
    assert cmsg.val.CAppInvalid?;
    assert appCaseId == 2;
    assert 2 == SeqByteToUint64(rest1[0..8]);
    ByteArrayOf8(rest1[0..8], 2);
    assert rest1[0..8] == [ 0, 0, 0, 0, 0, 0, 0, 2];
    calc { 
      data[0..24];
        { assert |data| >= 24; ByteConcat24(data); }
      data[0..8] + data[8..16] + data[16..24];
      [ 0, 0, 0, 0, 0, 0, 0, 0] + Uint64ToSeqByte(msg.seqno_req as uint64) + [ 0, 0, 0, 0, 0, 0, 0, 2]; 
    }
    assert data[0..24] == [ 0, 0, 0, 0, 0, 0, 0, 0] + Uint64ToSeqByte(msg.seqno_req as uint64) + [ 0, 0, 0, 0, 0, 0, 0, 2]; 
    lemma_SizeOfCMessageRequest(v);
    assert SizeOfV(v) == 24;
    if |data| > 24 {
      assert data[0..|data|] == data[..];
      lemma_parse_Val_view_specific_size(data, v, CMessage_grammar(), 0, |data|);
      lemma_parse_Val_view_specific(data, v, CMessage_grammar(), 0, |data|);
      assert false;
    }
  }
  
}

lemma {:timeLimitMultiplier 5} {:fuel ValInGrammar,3} lemma_ParseMarshallReply(bytes:seq<byte>, seqno:int, reply:AppMessage, msg:RslMessage)
  requires CMessageIsAbstractable(PaxosDemarshallData(bytes))
  requires AbstractifyCMessageToRslMessage(PaxosDemarshallData(bytes)) == msg
  requires Marshallable(PaxosDemarshallData(bytes))
  requires bytes == MarshallServiceReply(seqno, reply)
  ensures  msg.RslMessage_Reply?
  ensures  msg.seqno_reply == seqno
  ensures  msg.reply == reply
{
  var marshalled_bytes := MarshallServiceReply(seqno, reply);
  var g := CMessage_grammar();
  if 0 <= seqno < 0x1_0000_0000_0000_0000 {
    assert marshalled_bytes == [ 0, 0, 0, 0, 0, 0, 0, 6] + AbstractServiceRSL_s.Uint64ToBytes(seqno as uint64) + MarshallAppMessage(reply);
    var cmsg := PaxosDemarshallData(bytes);
    var data := bytes;
    var v := DemarshallFunc(data, g);

    // Walk through the generic parsing process
    var msgCaseId, msgCaseVal, rest0 := lemma_ParseValCorrectVCase(data, v, g);
    assert msgCaseId == 6;
    var seqnoVal, appVal, rest1 := lemma_ParseValCorrectTuple2(rest0, msgCaseVal, g.cases[msgCaseId]);
    var appCaseId, appCaseVal, rest2 := lemma_ParseValCorrectVCase(rest1, appVal, g.cases[msgCaseId].t[1]);

    // Prove that the first 8 bytes are correct
    assert msgCaseId == SeqByteToUint64(bytes[..8]) == 6;
    assert cmsg.CMessage_Reply?;

    // Prove the seqno is parsed correctly
    assert rest0 == AbstractServiceRSL_s.Uint64ToBytes(seqno as uint64) + MarshallAppMessage(reply);
    var u, rest := lemma_ParseValCorrectVUint64(rest0, seqnoVal, GUint64);
    lemma_2toX();
    calc {
      u;
      parse_Uint64(rest0).0.v.u;
      SeqByteToUint64(rest0[..8]);
      SeqByteToUint64(AbstractServiceRSL_s.Uint64ToBytes(seqno as uint64));
      SeqByteToUint64(Uint64ToSeqByte(seqno as uint64));
      SeqByteToUint64(BEUintToSeqByte(seqno as uint64 as int, 8));
        { lemma_BEByteSeqToInt_BEUintToSeqByte_invertability(); }
      seqno as uint64;
    }
    assert cmsg.seqno_reply as int == msg.seqno_reply;

    // Prove the app bytes are parsed correctly
    calc {
      MarshallAppMessage(reply);
      data[16..];
      rest0[8..];
        { reveal parse_Val(); }
      rest1;
    }
            
    if reply.AppIncrementReply? {
      lemma_BEByteSeqToInt_BEUintToSeqByte_invertability(); 

      var u_app, rest_app := lemma_ParseValCorrectVUint64(rest2, appCaseVal, GUint64);
      assert appCaseId == 1;

      calc {
        u_app;
        parse_Uint64(rest2).0.v.u;
        SeqByteToUint64(rest2[..8]);
        SeqByteToUint64(AbstractServiceRSL_s.Uint64ToBytes(reply.response as uint64));
        SeqByteToUint64(Uint64ToSeqByte(reply.response as uint64));
        SeqByteToUint64(BEUintToSeqByte(reply.response as uint64 as int, 8));
          { lemma_BEByteSeqToInt_BEUintToSeqByte_invertability(); }
        reply.response as uint64;
      }
    } else {
    } 
  } else {
    assert bytes == [1];
    reveal parse_Val();
    assert parse_Val(bytes, g).0.None?;
    assert false;
  }
}

}
