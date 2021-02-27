
include "AbstractService.s.dfy"
include "../../Protocol/SHT/Message.i.dfy"
include "../../Impl/SHT/PacketParsing.i.dfy"
include "../../Impl/SHT/AppInterfaceConcrete.i.dfy"
include "AppInterface.i.dfy"

module MarshallProof_i {
    import opened Native__NativeTypes_s
    import opened Bytes_s
    import opened Math__power2_i
    import opened AbstractServiceSHT_s`All
    import opened SHT__Message_i
    import opened SHT__PacketParsing_i
    import opened SHT__SingleMessage_i
    import opened SHT__CMessage_i
    import opened Impl__AppInterfaceConcrete_i`All
    import opened AppInterface_i`All
    import opened Common__Util_i
    import opened Common__GenericMarshalling_i

    lemma lemma_ParseValCorrectVByteArray(data:seq<byte>, v:V, g:G) returns (len:uint64, val:V, rest:seq<byte>)
        requires ValInGrammar(v, g);
        requires |data| < 0x1_0000_0000_0000_0000;
        requires ValidGrammar(g);
        requires parse_Val(data, g).0.Some?;
        requires parse_Val(data, g).0.v == v;
        requires g.GByteArray?;
        ensures  parse_Uint64(data).0.Some?;
        ensures  len == parse_Uint64(data).0.v.u;
        ensures  rest == parse_Uint64(data).1;
        ensures  |rest| >= len as int;
        ensures  val == VByteArray(rest[0..len]);
    {
        reveal_parse_Val();
        len := parse_Uint64(data).0.v.u;
        rest := parse_Uint64(data).1;
        val := VByteArray(rest[0..len]);
    }

    lemma lemma_ParseValCorrectVCase(data:seq<byte>, v:V, g:G) returns (caseId:uint64, val:V, rest:seq<byte>)
        requires ValInGrammar(v, g);
        requires |data| < 0x1_0000_0000_0000_0000;
        requires ValidGrammar(g);
        requires parse_Val(data, g).0.Some?;
        requires parse_Val(data, g).0.v == v;
        requires g.GTaggedUnion?;
        ensures  parse_Uint64(data).0.Some?;
        ensures  caseId == parse_Uint64(data).0.v.u;
        ensures  0 <= caseId as int < |g.cases|;
        ensures  rest == parse_Uint64(data).1;
        ensures         parse_Val(rest, g.cases[caseId]).0.Some?;
        ensures  val == parse_Val(rest, g.cases[caseId]).0.v
        ensures  v == VCase(caseId, val);
        ensures  ValInGrammar(val, g.cases[caseId]);
    {
        reveal_parse_Val();
        caseId := parse_Uint64(data).0.v.u;
        var tuple := parse_Val(parse_Uint64(data).1, g.cases[caseId]);
        val := tuple.0.v;
        rest := parse_Uint64(data).1;
    }

    lemma {:fuel ValInGrammar,3} lemma_ParseValCorrectTuple2(data:seq<byte>, v:V, g:G) returns (val0:V, val1:V, rest:seq<byte>)
        requires ValInGrammar(v, g);
        requires |data| < 0x1_0000_0000_0000_0000;
        requires ValidGrammar(g);
        requires parse_Val(data, g).0.Some?;
        requires parse_Val(data, g).0.v == v;
        requires g.GTuple?;
        requires |g.t| == 2;

        ensures         parse_Val(data, g.t[0]).0.Some?;
        ensures val0 == parse_Val(data, g.t[0]).0.v;
        ensures ValInGrammar(val0, g.t[0]);

        ensures rest == parse_Val(data, g.t[0]).1;
        ensures         parse_Val(rest, g.t[1]).0.Some?;
        ensures val1 == parse_Val(rest, g.t[1]).0.v;
        ensures ValInGrammar(val1, g.t[1]);

        ensures v == VTuple([val0, val1]);
    {
        reveal_parse_Val();
        reveal_parse_Tuple_contents();

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

    lemma {:fuel ValInGrammar,3} lemma_ParseValCorrectTuple3(data:seq<byte>, v:V, g:G) returns (val0:V, val1:V, val2:V, rest1:seq<byte>, rest2:seq<byte>)
        requires ValInGrammar(v, g);
        requires |data| < 0x1_0000_0000_0000_0000;
        requires ValidGrammar(g);
        requires parse_Val(data, g).0.Some?;
        requires parse_Val(data, g).0.v == v;
        requires g.GTuple?;
        requires |g.t| == 3;

        ensures         parse_Val(data, g.t[0]).0.Some?;
        ensures val0 == parse_Val(data, g.t[0]).0.v;
        ensures ValInGrammar(val0, g.t[0]);

        ensures rest1 == parse_Val(data, g.t[0]).1;
        ensures          parse_Val(rest1, g.t[1]).0.Some?
        ensures  val1 == parse_Val(rest1, g.t[1]).0.v;
        ensures ValInGrammar(val1, g.t[1]);

        ensures rest2 == parse_Val(rest1, g.t[1]).1;
        ensures          parse_Val(rest2, g.t[2]).0.Some?;
        ensures  val2 == parse_Val(rest2, g.t[2]).0.v;
        ensures ValInGrammar(val2, g.t[2]);

        ensures v == VTuple([val0, val1, val2]);
    {
        reveal_parse_Val();
        reveal_parse_Tuple_contents();

        // Prove that v == VTuple([val0, val1, val2]);
        assert parse_Val(data, g).0.v == parse_Tuple(data, g.t).0.v == VTuple(parse_Tuple_contents(data, g.t).0.v);

        assert parse_Tuple_contents(data, g.t).0.v == [parse_Val(data, g.t[0]).0.v] 
                                                    + parse_Tuple_contents(parse_Val(data, g.t[0]).1, g.t[1..]).0.v;

        var interm_rest := parse_Val(data, g.t[0]).1;
        assert [parse_Val(data, g.t[0]).0.v] + parse_Tuple_contents(interm_rest, g.t[1..]).0.v
            == [parse_Val(data, g.t[0]).0.v] + [parse_Val(interm_rest, g.t[1]).0.v]
             + parse_Tuple_contents(parse_Val(interm_rest, g.t[1]).1, g.t[2..]).0.v
            == [parse_Val(data, g.t[0]).0.v] + [parse_Val(interm_rest, g.t[1]).0.v]
             + [parse_Val(parse_Val(interm_rest, g.t[1]).1, g.t[2]).0.v];

        assert [parse_Val(data, g.t[0]).0.v] 
             + [parse_Val(interm_rest, g.t[1]).0.v]
             + [parse_Val(parse_Val(interm_rest, g.t[1]).1, g.t[2]).0.v]
            == [parse_Val(data, g.t[0]).0.v, 
                parse_Val(interm_rest, g.t[1]).0.v,
                parse_Val(parse_Val(interm_rest, g.t[1]).1, g.t[2]).0.v];

        assert |v.t| == 3;
        var foo;
        var tuple0 := parse_Val(data, g.t[0]);
        assert tuple0.0.Some?;
        val0,rest1 := tuple0.0.v, tuple0.1;
        var tuple1 := parse_Val(interm_rest, g.t[1]);
        val1,rest2 := tuple1.0.v, tuple1.1;
        var tuple2 := parse_Val(rest2, g.t[2]);
        val2,foo :=  tuple2.0.v, tuple2.1;

        // Prove that rest is set correctly
        assert parse_Val(data, g).1 == parse_Tuple(data, g.t).1 == parse_Tuple_contents(data, g.t).1;
        assert parse_Tuple_contents(data, g.t).1 == parse_Tuple_contents(parse_Val(data, g.t[0]).1, g.t[1..]).1;
        //assert parse_Tuple_contents(parse_Val(data, g.t[0]).1, g.t[1..]).1 == rest;
    }

    lemma lemma_ParseValCorrectVUint64(data:seq<byte>, v:V, g:G) returns (u:uint64, rest:seq<byte>)
        requires ValInGrammar(v, g);
        requires |data| < 0x1_0000_0000_0000_0000;
        requires ValidGrammar(g);
        requires parse_Val(data, g).0.Some?;
        requires parse_Val(data, g).0.v == v;
        requires g.GUint64?;
        ensures  parse_Uint64(data).0.Some?;
        ensures  u == parse_Uint64(data).0.v.u;
        ensures  v == VUint64(u);
        ensures  rest == parse_Val(data, g).1;
    {
        reveal_parse_Val();
        u := parse_Uint64(data).0.v.u;
        rest := parse_Uint64(data).1;
    }

    lemma {:fuel ValInGrammar,3} {:fuel SizeOfV,4} lemma_SizeOfGetRequest(v:V)
        requires ValInGrammar(v, CSingleMessage_grammar());
        requires ValInGrammar(v.val, GTuple([GUint64, EndPoint_grammar(), CMessage_grammar()]));
        requires ValInGrammar(v.val.t[2].val, CMessage_GetRequest_grammar());
        ensures  SizeOfV(v) == 40;
    {
        lemma_SeqSum_3(v.val);
        reveal_SeqSum();
    }

    lemma {:fuel ValInGrammar,4} {:fuel SizeOfV,5} lemma_SizeOfSetRequest(v:V, cmsg:CSingleMessage)
        requires ValInGrammar(v, CSingleMessage_grammar());
        requires ValInGrammar(v.val, GTuple([GUint64, EndPoint_grammar(), CMessage_grammar()]));
        requires ValInGrammar(v.val.t[2].val, CMessage_SetRequest_grammar());
        requires parse_CSingleMessage(v) == cmsg;
        requires cmsg.m.CSetRequest?;
        ensures  SizeOfV(v) == if cmsg.m.v_setrequest.ValuePresent? then 56 + |cmsg.m.v_setrequest.v| else 48;
    {
        lemma_SeqSum_2(v.val.t[2].val);
        lemma_SeqSum_3(v.val);
        reveal_SeqSum();
        calc {
            SizeOfV(v);
            8 + SizeOfV(v.val);
            8 + 8 + 8 + SizeOfV(v.val.t[2]);
            8 + 8 + 8 + 8 + SizeOfV(v.val.t[2].val);
            8 + 8 + 8 + 8 + 8 + SizeOfV(v.val.t[2].val.t[1]);
            8 + 8 + 8 + 8 + 8 + 8 + SizeOfV(v.val.t[2].val.t[1].val);
            48 + SizeOfV(v.val.t[2].val.t[1].val);
        }
        if cmsg.m.v_setrequest.ValueAbsent? {
            assert SizeOfV(v.val.t[2].val.t[1].val) == 0;
        } else {
            assert SizeOfV(v.val.t[2].val.t[1].val) == 8 + |v.val.t[2].val.t[1].val.b|;
        }   

    }

    lemma {:fuel ValInGrammar,4} {:fuel SizeOfV,5} lemma_SizeOfReply(v:V, cmsg:CSingleMessage)
        requires ValInGrammar(v, CSingleMessage_grammar());
        requires ValInGrammar(v.val, GTuple([GUint64, EndPoint_grammar(), CMessage_grammar()]));
        requires ValInGrammar(v.val.t[2].val, CMessage_Reply_grammar());
        requires parse_CSingleMessage(v) == cmsg;
        requires cmsg.m.CReply?;
        ensures  SizeOfV(v) == if cmsg.m.v.ValuePresent? then 56 + |cmsg.m.v.v| else 48;
    {
        lemma_SeqSum_2(v.val.t[2].val);
        lemma_SeqSum_3(v.val);
        reveal_SeqSum();
        calc {
            SizeOfV(v);
            8 + SizeOfV(v.val);
            8 + 8 + 8 + SizeOfV(v.val.t[2]);
            8 + 8 + 8 + 8 + SizeOfV(v.val.t[2].val);
            8 + 8 + 8 + 8 + 8 + SizeOfV(v.val.t[2].val.t[1]);
            8 + 8 + 8 + 8 + 8 + 8 + SizeOfV(v.val.t[2].val.t[1].val);
            48 + SizeOfV(v.val.t[2].val.t[1].val);
        }
        if cmsg.m.v.ValueAbsent? {
            assert SizeOfV(v.val.t[2].val.t[1].val) == 0;
        } else {
            assert SizeOfV(v.val.t[2].val.t[1].val) == 8 + |v.val.t[2].val.t[1].val.b|;
        }   

    }
/*
    lemma {:fuel ValInGrammar,3} {:fuel SizeOfV,3} lemma_SizeOfCMessageRequest1(v:V)
        requires ValInGrammar(v, CMessage_grammar());
        requires ValInGrammar(v.val, CMessage_Request_grammar());
        requires v.val.t[1].c == 1;
        ensures  SizeOfV(v) == 32;
    {
        lemma_SeqSum2(v.val);
        reveal_SeqSum();
    }

    lemma {:fuel ValInGrammar,3} {:fuel SizeOfV,3} lemma_SizeOfCMessageRequest(v:V)
        requires ValInGrammar(v, CMessage_grammar());
        requires ValInGrammar(v.val, CMessage_Request_grammar());
        requires v.val.t[1].c == 0 || v.val.t[1].c == 2;
        ensures  SizeOfV(v) == 24;
    {
        lemma_SeqSum2(v.val);
        reveal_SeqSum();
    }
*/

    lemma lemma_ParseUint64Offset(s1:seq<byte>, s2:seq<byte>, i:int, j:int)
        requires 0 <= i < j <= |s2|;
        requires |s1| < 0x1_0000_0000_0000_0000;
        requires s2 == parse_Val(s1, GUint64).1;
        ensures  j+8 <= |s1|;
        ensures  s2[i..j] == s1[i+8..j+8];
    {
        reveal_parse_Val();
    }

    lemma {:fuel ValInGrammar,3} lemma_ParseMarshallGetRequest(bytes:seq<byte>, msg:SingleMessage<Message>) returns (reserved_bytes:seq<byte>)
        requires msg.SingleMessage? && msg.m.GetRequest?;
        requires CSingleMessageIsAbstractable(SHTDemarshallData(bytes));
        requires AbstractifyCSingleMessageToSingleMessage(SHTDemarshallData(bytes)) == msg;
        ensures  |reserved_bytes| == 8;
        ensures  bytes == MarshallServiceGetRequest(AppGetRequest(msg.seqno, msg.m.k_getrequest), reserved_bytes);
    {
        var cmsg := SHTDemarshallData(bytes);
        assert cmsg.CSingleMessage?;
        var data := bytes;
        var g := CSingleMessage_grammar();
        var v := DemarshallFunc(data, g);

        lemma_SizeOfGetRequest(v);
        assert SizeOfV(v) == 40;

        // Walk through the generic parsing process
        var msgCaseId, msgCaseVal, rest0 := lemma_ParseValCorrectVCase(data, v, g);
        var seqnoVal, dstVal, msgVal, rest1, rest2 := lemma_ParseValCorrectTuple3(rest0, msgCaseVal, g.cases[msgCaseId]);
        var mCaseId, mCaseVal, rest3 := lemma_ParseValCorrectVCase(rest2, msgVal, g.cases[msgCaseId].t[2]);

        // Prove that the first 8 bytes are correct
        assert msgCaseId == 0;
        assert 0 == SeqByteToUint64(bytes[..8]);
        assert bytes[..8] == [ 0, 0, 0, 0, 0, 0, 0, 0];

        // Prove that the next 8 bytes of seqno are correct
        var u, rest := lemma_ParseValCorrectVUint64(rest0, seqnoVal, GUint64);
        assert msg.seqno == u as int;
        assert SeqByteToUint64(rest0[..8]) == u;
        assert Uint64ToSeqByte(u) == Uint64ToBytes(u);
        lemma_BEByteSeqToInt_BEUintToSeqByte_invertability();
        assert rest0[..8] == Uint64ToSeqByte(msg.seqno as uint64);
        assert data[8..16] == rest0[..8];

        // Prove that the 8 bytes of dst are correct
        var u_dst, rest_dst := lemma_ParseValCorrectVUint64(rest1, dstVal, GUint64);

        assert SeqByteToUint64(rest1[..8]) == u_dst;
        assert Uint64ToSeqByte(u_dst) == Uint64ToBytes(u_dst);
        lemma_BEByteSeqToInt_BEUintToSeqByte_invertability();
        assert rest1[..8] == Uint64ToSeqByte(u_dst);
        reveal_parse_Val();
        calc {
            data[16..24];
            rest0[8..16];
                { assert rest1 == parse_Val(rest0, GUint64).1; reveal_parse_Val(); }
            rest1[..8];
        }
        reserved_bytes := data[16..24];
        //lemma_ParseEndPoint(msg.dst, u_dst, data[16..24]);

        // Prove that the 8 bytes of the case ID for CMessage is handled correctly
        assert mCaseId == 0;
        calc {
            SeqByteToUint64(bytes[24..32]);
                { lemma_ParseUint64Offset(data, rest0, 16, 24); }
            SeqByteToUint64(rest0[16..24]);
                { assert rest0[16..24] == rest1[8..16]; }
            SeqByteToUint64(rest1[8..16]);
            SeqByteToUint64(rest2[..8]);
            0;
        }
        //assert bytes[24..32] == [ 0, 0, 0, 0, 0, 0, 0, 0];
        
        var key, rest_key := lemma_ParseValCorrectVUint64(rest3, mCaseVal, GUint64);

        assert data[..40] == [ 0, 0, 0, 0, 0, 0, 0, 0] 
                           + Uint64ToSeqByte(msg.seqno as uint64)
                           + reserved_bytes
                           + [ 0, 0, 0, 0, 0, 0, 0, 0]
                           + Uint64ToSeqByte(msg.m.k_getrequest);

        assert Uint64ToSeqByte(msg.m.k_getrequest) == MarshallSHTKey(msg.m.k_getrequest);
        if |data| > 40 {
            assert data[0..|data|] == data[..];
            lemma_parse_Val_view_specific_size(data, v, CSingleMessage_grammar(), 0, |data|);
            lemma_parse_Val_view_specific(data, v, CSingleMessage_grammar(), 0, |data|);
            assert false;
        }
        assert |data| == 40;
    }

    lemma {:fuel ValInGrammar,5} lemma_ParseMarshallSetRequest(bytes:seq<byte>, msg:SingleMessage<Message>) returns (reserved_bytes:seq<byte>)
        requires msg.SingleMessage? && msg.m.SetRequest?;
        requires CSingleMessageIsAbstractable(SHTDemarshallData(bytes));
        requires AbstractifyCSingleMessageToSingleMessage(SHTDemarshallData(bytes)) == msg;
        ensures  |reserved_bytes| == 8;
        ensures  bytes == MarshallServiceSetRequest(AppSetRequest(msg.seqno, msg.m.k_setrequest, msg.m.v_setrequest), reserved_bytes);
    {
        var cmsg := SHTDemarshallData(bytes);
        assert cmsg.CSingleMessage?;
        var data := bytes;
        var g := CSingleMessage_grammar();
        var v := DemarshallFunc(data, g);

        lemma_SizeOfSetRequest(v, cmsg);
        assert SizeOfV(v) >= 48;

        // Walk through the generic parsing process
        var msgCaseId, msgCaseVal, rest0 := lemma_ParseValCorrectVCase(data, v, g);
        var seqnoVal, dstVal, msgVal, rest1, rest2 := lemma_ParseValCorrectTuple3(rest0, msgCaseVal, g.cases[msgCaseId]);
        var mCaseId, mCaseVal, rest3 := lemma_ParseValCorrectVCase(rest2, msgVal, g.cases[msgCaseId].t[2]);
        var keyVal, optValueVal, rest4 := lemma_ParseValCorrectTuple2(rest3, mCaseVal, g.cases[msgCaseId].t[2].cases[mCaseId]);
        var valCaseId, valCaseVal, rest5 := lemma_ParseValCorrectVCase(rest4, optValueVal, OptionalValue_grammar());

        // Prove that the first 8 bytes are correct
        assert msgCaseId == 0;
        assert 0 == SeqByteToUint64(bytes[..8]);
        assert bytes[..8] == [ 0, 0, 0, 0, 0, 0, 0, 0];

        // Prove that the next 8 bytes of seqno are correct
        var u, rest := lemma_ParseValCorrectVUint64(rest0, seqnoVal, GUint64);
        assert msg.seqno == u as int;
        assert SeqByteToUint64(rest0[..8]) == u;
        assert Uint64ToSeqByte(u) == Uint64ToBytes(u);
        lemma_BEByteSeqToInt_BEUintToSeqByte_invertability();
        assert rest0[..8] == Uint64ToSeqByte(msg.seqno as uint64);
        assert data[8..16] == rest0[..8];

        // Prove that the 8 bytes of dst are correct
        var u_dst, rest_dst := lemma_ParseValCorrectVUint64(rest1, dstVal, GUint64);

        assert SeqByteToUint64(rest1[..8]) == u_dst;
        assert Uint64ToSeqByte(u_dst) == Uint64ToBytes(u_dst);
        lemma_BEByteSeqToInt_BEUintToSeqByte_invertability();
        assert rest1[..8] == Uint64ToSeqByte(u_dst);
        reveal_parse_Val();
        calc {
            data[16..24];
            rest0[8..16];
                { assert rest1 == parse_Val(rest0, GUint64).1; reveal_parse_Val(); }
            rest1[..8];
        }
        reserved_bytes := data[16..24];

        // Prove some length relationships to show that our indices are within bounds
        calc ==> {
           true;
           rest0 == parse_Uint64(data).1;
           |rest0| == |data| - 8;
        }
        calc ==> {
           true;
           rest1 == parse_Uint64(rest0).1;
           |rest1| == |rest0| - 8;
        }
        calc ==> {
           true;
           rest2 == parse_Uint64(rest1).1;
           |rest2| == |rest1| - 8;
        }
        calc ==> {
           true;
           rest3 == parse_Uint64(rest2).1;
           |rest3| == |rest2| - 8;
        }

        // Prove that the 8 bytes of the case ID for CMessage is handled correctly
        assert mCaseId == 1;
        calc {
            SeqByteToUint64(bytes[24..32]);
                { reveal_parse_Val(); lemma_ParseUint64Offset(data, rest0, 16, 24); }
            SeqByteToUint64(rest0[16..24]);
            SeqByteToUint64(rest1[8..16]);
            SeqByteToUint64(rest2[..8]);
            1;
        }
       
        // Prove that the key is handled correctly
        var key, rest_key := lemma_ParseValCorrectVUint64(rest3, keyVal, GUint64);

        assert data[..40] == [ 0, 0, 0, 0, 0, 0, 0, 0] 
                           + Uint64ToSeqByte(msg.seqno as uint64)
                           + reserved_bytes
                           + [ 0, 0, 0, 0, 0, 0, 0, 1]
                           + Uint64ToSeqByte(msg.m.k_setrequest);

        assert Uint64ToSeqByte(msg.m.k_setrequest) == MarshallSHTKey(msg.m.k_setrequest);

        // Handle the two subcases of OptionalValue
        if cmsg.m.v_setrequest.ValuePresent? {
            assert valCaseId == 0;
            assert 0 == SeqByteToUint64(rest4[..8]);
            assert rest4[..8] == [ 0, 0, 0, 0, 0, 0, 0, 0];
            calc {
                rest4[..8];
                rest3[8..16];
                rest2[16..24];
                rest1[24..32];
                rest0[32..40];
                data[40..48];
            }
            var byteLen, bytesVal, rest6 := lemma_ParseValCorrectVByteArray(rest5, valCaseVal, GByteArray);
            assert data[..56+byteLen] == 
                                 [ 0, 0, 0, 0, 0, 0, 0, 0] 
                               + Uint64ToSeqByte(msg.seqno as uint64)
                               + reserved_bytes
                               + [ 0, 0, 0, 0, 0, 0, 0, 1]
                               + Uint64ToSeqByte(msg.m.k_setrequest)
                               + [ 0, 0, 0, 0, 0, 0, 0, 0] 
                               + Uint64ToSeqByte(byteLen) 
                               + bytesVal.b;
            assert SizeOfV(v) == 56 + byteLen as int;
            if |data| > 56 + byteLen as int {
                assert data[0..|data|] == data[..];
                lemma_parse_Val_view_specific_size(data, v, CSingleMessage_grammar(), 0, |data|);
                lemma_parse_Val_view_specific(data, v, CSingleMessage_grammar(), 0, |data|);
                assert false;
            }
            assert |data| == 56 + byteLen as int;
        } else {
            assert cmsg.m.v_setrequest.ValueAbsent?;
            assert valCaseId == 1;
            assert 1 == SeqByteToUint64(rest4[..8]);
            assert rest4[..8] == [ 0, 0, 0, 0, 0, 0, 0, 1];
            assert data[..48] == [ 0, 0, 0, 0, 0, 0, 0, 0] 
                               + Uint64ToSeqByte(msg.seqno as uint64)
                               + reserved_bytes
                               + [ 0, 0, 0, 0, 0, 0, 0, 1]
                               + Uint64ToSeqByte(msg.m.k_setrequest)
                               + [ 0, 0, 0, 0, 0, 0, 0, 1];

            if |data| > 48 {
                assert data[0..|data|] == data[..];
                lemma_parse_Val_view_specific_size(data, v, CSingleMessage_grammar(), 0, |data|);
                lemma_parse_Val_view_specific(data, v, CSingleMessage_grammar(), 0, |data|);
                assert false;
            }
            assert |data| == 48;
        }
    }

    lemma {:fuel ValInGrammar,5} lemma_ParseMarshallReply(bytes:seq<byte>, reply:AppReply, msg:SingleMessage<Message>, reserved_bytes:seq<byte>) 
        requires CSingleMessageIsAbstractable(SHTDemarshallData(bytes));
        requires AbstractifyCSingleMessageToSingleMessage(SHTDemarshallData(bytes)) == msg;
        requires CSingleMessageMarshallable(SHTDemarshallData(bytes));
        requires bytes == MarshallServiceReply(reply, reserved_bytes);
        requires |reserved_bytes| == 8;
        ensures  msg.SingleMessage?;
        ensures  msg.seqno     == reply.seqno;
        ensures  msg.m.Reply?;
        ensures  msg.m.k_reply == reply.k;
        ensures  msg.m.v       == reply.ov;
    {
        var marshalled_bytes := MarshallServiceReply(reply, reserved_bytes);
        var g := CSingleMessage_grammar();
        if 0 <= reply.seqno < 0x1_0000_0000_0000_0000 {
            var cmsg := SHTDemarshallData(bytes);
            var data := bytes;
            var v := DemarshallFunc(data, g);

            // Walk through the generic parsing process
            var msgCaseId, msgCaseVal, rest0 := lemma_ParseValCorrectVCase(data, v, g);
            var seqnoVal, dstVal, msgVal, rest1, rest2 := lemma_ParseValCorrectTuple3(rest0, msgCaseVal, g.cases[msgCaseId]);
            var mCaseId, mCaseVal, rest3 := lemma_ParseValCorrectVCase(rest2, msgVal, g.cases[msgCaseId].t[2]);

            // Prove that the first 8 bytes are correct
            assert msgCaseId == 0;
            assert 0 == SeqByteToUint64(bytes[..8]);
            assert bytes[..8] == [ 0, 0, 0, 0, 0, 0, 0, 0];

            // Prove that the next 8 bytes of seqno are correct
            var u, rest := lemma_ParseValCorrectVUint64(rest0, seqnoVal, GUint64);
            lemma_2toX();
            calc {
                u;
                parse_Uint64(rest0).0.v.u;
                SeqByteToUint64(rest0[..8]);
                SeqByteToUint64(Uint64ToBytes(reply.seqno as uint64));
                SeqByteToUint64(Uint64ToSeqByte(reply.seqno as uint64));
                SeqByteToUint64(BEUintToSeqByte(reply.seqno as uint64 as int, 8));
                    { lemma_BEByteSeqToInt_BEUintToSeqByte_invertability(); }
                reply.seqno as uint64;
            }
            assert msg.seqno == u as int;
            assert reply.seqno == msg.seqno;

            // Prove some length relationships to show that our indices are within bounds
            reveal_parse_Val();
            calc ==> {
               true;
               rest0 == parse_Uint64(data).1;
               |rest0| == |data| - 8;
            }
            calc ==> {
               true;
               rest1 == parse_Uint64(rest0).1;
               |rest1| == |rest0| - 8;
            }
            calc ==> {
               true;
               rest2 == parse_Uint64(rest1).1;
               |rest2| == |rest1| - 8;
            }
            calc ==> {
               true;
               rest3 == parse_Uint64(rest2).1;
               |rest3| == |rest2| - 8;
            }

            // Prove that the 8 bytes of the case ID for CMessage is handled correctly
            calc {
                SeqByteToUint64(bytes[24..32]);
                    { reveal_parse_Val(); lemma_ParseUint64Offset(data, rest0, 16, 24); }
                SeqByteToUint64(rest0[16..24]);
                    { reveal_parse_Val(); lemma_ParseUint64Offset(rest0, rest1, 8, 16); }
                SeqByteToUint64(rest1[8..16]);
                SeqByteToUint64(rest2[..8]);
                2;
            }
            assert mCaseId == 2;
           
            var keyVal, optValueVal, rest4 := lemma_ParseValCorrectTuple2(rest3, mCaseVal, g.cases[msgCaseId].t[2].cases[mCaseId]);
            var valCaseId, valCaseVal, rest5 := lemma_ParseValCorrectVCase(rest4, optValueVal, OptionalValue_grammar());

            // Prove that the key is handled correctly
            var key, rest_key := lemma_ParseValCorrectVUint64(rest3, keyVal, GUint64);
            calc {
                msg.m.k_reply;
                key;
                parse_Uint64(rest3).0.v.u;
                parse_Uint64(MarshallSHTKey(reply.k)).0.v.u;
                SeqByteToUint64(MarshallSHTKey(reply.k));
                SeqByteToUint64(Uint64ToBytes(reply.k));
                SeqByteToUint64(Uint64ToSeqByte(reply.k));
                SeqByteToUint64(BEUintToSeqByte(reply.k as int, 8));
                    { lemma_BEByteSeqToInt_BEUintToSeqByte_invertability(); }
                reply.k;
            }

            // Handle the two subcases of OptionalValue
            if reply.ov.ValuePresent? {
                assert rest4[..8] == [ 0, 0, 0, 0, 0, 0, 0, 0];
                calc {
                    rest4[..8];
                    rest3[8..16];
                    rest2[16..24];
                    rest1[24..32];
                    rest0[32..40];
                    data[40..48];
                }
                var byteLen, bytesVal, rest6 := lemma_ParseValCorrectVByteArray(rest5, valCaseVal, GByteArray);
                calc {
                    byteLen;
                    parse_Uint64(rest5).0.v.u;
                    SeqByteToUint64(rest5[..8]);
                    SeqByteToUint64(Uint64ToBytes(|reply.ov.v| as uint64));
                    SeqByteToUint64(Uint64ToSeqByte(|reply.ov.v| as uint64));
                    SeqByteToUint64(BEUintToSeqByte(|reply.ov.v| as uint64 as int, 8));
                        { lemma_BEByteSeqToInt_BEUintToSeqByte_invertability(); }
                    |reply.ov.v| as uint64;
                }
                assert |bytesVal.b| == |msg.m.v.v|;
                assert bytesVal.b == msg.m.v.v;

                assert |bytesVal.b| == |reply.ov.v|;
                assert bytesVal.b == reply.ov.v;

                assert msg.m.v == reply.ov;
            } else {
                assert rest4[..8] == [ 0, 0, 0, 0, 0, 0, 0, 1];
            }

        } else {
            assert bytes == [1];
            reveal_parse_Val();
            assert parse_Val(bytes, g).0.None?;
            assert false;
        }
    }
}
