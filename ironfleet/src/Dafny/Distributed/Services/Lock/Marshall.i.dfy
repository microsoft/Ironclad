include "AbstractService.s.dfy"
include "../../Protocol/Lock/Types.i.dfy"
include "../../Impl/Lock/PacketParsing.i.dfy"

module MarshallProof_i {
import opened Native__NativeTypes_s
    import opened AbstractServiceLock_s`All
    import opened Types_i 
    import opened Math__power2_i
    import opened Common__Util_i
    import opened Common__GenericMarshalling_i
    import opened Message_i
    import opened PacketParsing_i

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

    lemma lemma_SizeOfCMessageLocked(v:V)
        requires ValInGrammar(v, CMessageGrammar());
        requires ValInGrammar(v.val, CMessageLockedGrammar());
        ensures  SizeOfV(v) == 16;
    {
    }

    lemma lemma_ParseMarshallLockedAbstract(bytes:seq<byte>, epoch:int, msg:LockMessage)
        requires AbstractifyCMessage(DemarshallData(bytes)) == msg;
        requires bytes == MarshallLockMsg(epoch);
        requires Demarshallable(bytes, CMessageGrammar());
        ensures  msg.Locked?;
        ensures  msg.locked_epoch == epoch;
    {
        var marshalled_bytes := MarshallLockMsg(epoch);
        var g := CMessageGrammar();
        if 0 <= epoch < 0x1_0000_0000_0000_0000 {
            var cmsg := DemarshallData(bytes);
            var data := bytes;
            var v := DemarshallFunc(data, g);

            // Walk through the generic parsing process
            var msgCaseId, msgCaseVal, rest0 := lemma_ParseValCorrectVCase(data, v, g);

            // Prove that the first 8 bytes are correct
            assert msgCaseId == 1;
            assert 1 == SeqByteToUint64(bytes[..8]);
            assert bytes[..8] == [ 0, 0, 0, 0, 0, 0, 0, 1];

            // Prove that the next 8 bytes of seqno are correct
            var u, rest := lemma_ParseValCorrectVUint64(rest0, msgCaseVal, GUint64);
            lemma_2toX();
            calc {
                u;
                parse_Uint64(rest0).0.v.u;
                SeqByteToUint64(rest0[..8]);
                SeqByteToUint64(Uint64ToBytes(epoch as uint64));
                SeqByteToUint64(Uint64ToSeqByte(epoch as uint64));
                SeqByteToUint64(BEUintToSeqByte(epoch as uint64 as int, 8));
                    { lemma_BEByteSeqToInt_BEUintToSeqByte_invertability(); }
                epoch as uint64;
            }
            assert msg.locked_epoch == u as int;
            assert epoch == msg.locked_epoch;
        } else {
            reveal_parse_Val();
            assert false;
        }
    }

}
