include "CMessage.i.dfy"
include "AppInterfaceConcrete.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../Common/GenericMarshalling.i.dfy"
include "../../Protocol/LiveSHT/RefinementProof/Environment.i.dfy"
include "../../Protocol/SHT/Host.i.dfy"

module {:fuel ValInGrammar,4} SHT__PacketParsing_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened Collections__Maps_i
import opened Math__mul_i
import opened Environment_s
import opened Impl__AppInterfaceConcrete_i`Spec
import opened Common__GenericMarshalling_i
import opened Common__NodeIdentity_i
import opened LiveSHT__Environment_i
import opened SHT__HT_s
import opened SHT__Keys_i
import opened SHT__CMessage_i
import opened SHT__Network_i
import opened SHT__Host_i
import opened Impl_Parameters_i
import opened AppInterface_i`All
import opened Common__UdpClient_i

////////////////////////////////////////////////////////////////////
//    Grammars for the basic types
////////////////////////////////////////////////////////////////////
function method OptionalValue_grammar() : G { GTaggedUnion([Value_grammar(), GTuple([])]) }
function method KeyPlus_grammar() : G { GTaggedUnion([Key_grammar(), GUint64]) }
function method KeyRange_grammar() : G { GTuple([KeyPlus_grammar(), KeyPlus_grammar()]) }
function method Hashtable_grammar() : G { GArray(GTuple([Key_grammar(), Value_grammar()])) }
function method EndPoint_grammar() : G { GUint64 }

////////////////////////////////////////////////////////////////////
//    Grammars for the SHT messages 
////////////////////////////////////////////////////////////////////
function method CMessage_GetRequest_grammar() : G { Key_grammar() }
function method CMessage_SetRequest_grammar() : G { GTuple([Key_grammar(), OptionalValue_grammar()]) }
function method CMessage_Reply_grammar() : G      { GTuple([Key_grammar(), OptionalValue_grammar()]) }
function method CMessage_Redirect_grammar() : G   { GTuple([Key_grammar(), EndPoint_grammar()]) }
function method CMessage_Shard_grammar() : G      { GTuple([KeyRange_grammar(), EndPoint_grammar()]) }
function method CMessage_Delegate_grammar() : G   { GTuple([KeyRange_grammar(), Hashtable_grammar()]) }

function method CMessage_grammar() : G { GTaggedUnion([
        CMessage_GetRequest_grammar(),
        CMessage_SetRequest_grammar(),
        CMessage_Reply_grammar(),
        CMessage_Redirect_grammar(),
        CMessage_Shard_grammar(),
        CMessage_Delegate_grammar()
        ]) }

function method CSingleMessage_grammar() : G { 
    GTaggedUnion( [ GTuple([GUint64, EndPoint_grammar(), CMessage_grammar()]),  // CSingleMessage
                    GUint64])                                                   // Ack
}

predicate UdpPacketBound(data:seq<byte>) 
{
    |data| < MaxPacketSize()
}

lemma lemma_CMessageGrammarValid()
    ensures ValidGrammar(CMessage_grammar());
{
    var g := CMessage_grammar();
    assert |g.cases| < 0x1_0000_0000_0000_0000;
    lemma_ValidKey_grammer();
    lemma_ValidValue_grammer();
    assert ValidGrammar(CMessage_GetRequest_grammar());
    assert ValidGrammar(CMessage_SetRequest_grammar());
    assert ValidGrammar(CMessage_Reply_grammar());
    assert ValidGrammar(CMessage_Redirect_grammar());
    assert ValidGrammar(CMessage_Shard_grammar());
    assert ValidGrammar(CMessage_Delegate_grammar());
}
//function {:opaque} SHTDemarshallable(data:seq<byte>) : bool
//{
//        |data| < 0x1_0000_0000_0000_0000
//    && Demarshallable(data, CSingleMessage_grammar()) 
//    && !parse_Val(data, CSingleMessage_grammar()).0.None?
//    && (var v := DemarshallFunc(data, CSingleMessage_grammar());
//        CSingleMessageIsAbstractable(parse_CSingleMessage(v)) && CSingleMessageMarshallable(parse_CSingleMessage(v)))
//}

////////////////////////////////////////////////////////////////////
//    Parsing
////////////////////////////////////////////////////////////////////

function method parse_OptionalValue(val:V) : OptionalValue
    requires ValInGrammar(val, OptionalValue_grammar());
{
    if val.c == 0 then
        ValuePresent(parse_Value(val.val))
    else 
        ValueAbsent()
}

function method parse_KeyPlus(val:V) : KeyPlus
    requires ValInGrammar(val, KeyPlus_grammar());
{
    if val.c == 0 then
        KeyPlus(parse_Key(val.val))
    else if val.c == 1 then
        if val.val.u == 0 then
            KeyZero()
        else 
            KeyInf()
    else
        assert false;       // Should never get here
        KeyInf()
}

function method parse_KeyRange(val:V) : KeyRange
    requires ValInGrammar(val, KeyRange_grammar());
{
    KeyRange(parse_KeyPlus(val.t[0]), parse_KeyPlus(val.t[1]))
}

function method parse_Hashtable(val:V) : Hashtable 
    requires ValInGrammar(val, Hashtable_grammar());
    ensures  |parse_Hashtable(val)| <= |val.a|;
    ensures  ValidVal(val) ==> HashtableIs64Bit(parse_Hashtable(val));
    decreases |val.a|;
{
    if |val.a| == 0 then
        map []
    else 
        var tuple := val.a[0];
        assert ValInGrammar(tuple, Hashtable_grammar().elt);        // OBSERVE: Still needed despite fuel boost.  Odd.
        var key := parse_Key(tuple.t[0]);
        var value := parse_Value(tuple.t[1]);
        var others := parse_Hashtable(VArray(val.a[1..]));
        var m := others[key := value];
        m
}

function method parse_EndPoint(val:V) : EndPoint
    requires ValInGrammar(val, EndPoint_grammar());
    ensures  EndPointIsAbstractable(parse_EndPoint(val));
{
    if val.u <= 0xffffffffffff then
        ConvertUint64ToEndPoint(val.u)
    else
        EndPoint([0,0,0,0], 0)
}

function method parse_Message_GetRequest(val:V) : CMessage
    requires ValInGrammar(val, CMessage_GetRequest_grammar());
    ensures  CMessageIsAbstractable(parse_Message_GetRequest(val));
{
    CGetRequest(parse_Key(val))
}

function method parse_Message_SetRequest(val:V) : CMessage
    requires ValInGrammar(val, CMessage_SetRequest_grammar());
    ensures  CMessageIsAbstractable(parse_Message_SetRequest(val));
{
    CSetRequest(parse_Key(val.t[0]), parse_OptionalValue(val.t[1]))
}

function method parse_Message_Reply(val:V) : CMessage
    requires ValInGrammar(val, CMessage_Reply_grammar());
    ensures  CMessageIsAbstractable(parse_Message_Reply(val));
{
    CReply(parse_Key(val.t[0]), parse_OptionalValue(val.t[1]))
}

function method parse_Message_Redirect(val:V) : CMessage
    requires ValInGrammar(val, CMessage_Redirect_grammar());
    ensures  CMessageIsAbstractable(parse_Message_Redirect(val));
{
    CRedirect(parse_Key(val.t[0]), parse_EndPoint(val.t[1]))
}

function method parse_Message_Shard(val:V) : CMessage
    requires ValInGrammar(val, CMessage_Shard_grammar());
    ensures  CMessageIsAbstractable(parse_Message_Shard(val));
{
    CShard(parse_KeyRange(val.t[0]), parse_EndPoint(val.t[1]))
}

function method parse_Message_Delegate(val:V) : CMessage
    requires ValInGrammar(val, CMessage_Delegate_grammar());
    ensures  CMessageIsAbstractable(parse_Message_Delegate(val));
    ensures  parse_Message_Delegate(val).CDelegate?;
    ensures  ValidVal(val) ==> HashtableIs64Bit(parse_Message_Delegate(val).h);
{
    CDelegate(parse_KeyRange(val.t[0]), parse_Hashtable(val.t[1]))
}

function method parse_Message(val:V) : CMessage
    requires ValInGrammar(val, CMessage_grammar());
    ensures  CMessageIsAbstractable(parse_Message(val));
    ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message(val)); 
{
    if val.c == 0 then
        parse_Message_GetRequest(val.val)
    else if val.c == 1 then
        parse_Message_SetRequest(val.val)
    else if val.c == 2 then
        parse_Message_Reply(val.val)
    else if val.c == 3 then
        parse_Message_Redirect(val.val)
    else if val.c == 4 then
        parse_Message_Shard(val.val)
    else if val.c == 5 then
        parse_Message_Delegate(val.val)
    else
        assert false;       // Should never get here
        parse_Message_GetRequest(val.val)
}

function method {:fuel ValidVal,2} parse_CSingleMessage(val:V) : CSingleMessage
    requires ValInGrammar(val, CSingleMessage_grammar());
    ensures  CSingleMessageIsAbstractable(parse_CSingleMessage(val));
    ensures  ValidVal(val) ==> CSingleMessageIs64Bit(parse_CSingleMessage(val)); 
{
    if val.c == 0 then
        CSingleMessage(val.val.t[0].u, parse_EndPoint(val.val.t[1]), parse_Message(val.val.t[2]))
    else
        CAck(val.val.u)
}

function SHTDemarshallData(data:seq<byte>) : CSingleMessage
{
    if Demarshallable(data, CSingleMessage_grammar()) then
    var val := DemarshallFunc(data, CSingleMessage_grammar());
    parse_CSingleMessage(val)
    else
        CInvalidMessage()
}

method SHTDemarshallDataMethod(data:array<byte>) returns (msg:CSingleMessage)
    requires data.Length < 0x1_0000_0000_0000_0000;
    ensures  CSingleMessageIs64Bit(msg); 
    ensures  if Demarshallable(data[..], CSingleMessage_grammar()) then
                msg == SHTDemarshallData(data[..])
             else
                msg.CInvalidMessage?;
{
    lemma_CSingleMessage_grammar_valid();
    var success, val := Demarshall(data, CSingleMessage_grammar());
    if success {
        assert ValInGrammar(val, CSingleMessage_grammar());
        msg := parse_CSingleMessage(val);
        assert !msg.CInvalidMessage?;
    } else {
        msg := CInvalidMessage();
    }
}

///////////////////////////////////////////////////////////////////
//    64-bit Limits
////////////////////////////////////////////////////////////////////

predicate HashtableIs64Bit(h:Hashtable) { |h| < 0x1_0000_0000_0000_0000 }

predicate CMessageIs64Bit(m:CMessage)
{
    m.CDelegate? ==> HashtableIs64Bit(m.h)
}

predicate CSingleMessageIs64Bit(msg:CSingleMessage) 
{
    msg.CSingleMessage? ==> CMessageIs64Bit(msg.m)
}

////////////////////////////////////////////////////////////////////
//    Marshalling 
////////////////////////////////////////////////////////////////////


predicate ValidHashtable(h:Hashtable)
{
    |h| < max_hashtable_size()
    && (forall k :: k in h ==> ValidKey(k) && ValidValue(h[k]))
}
 
predicate MessageMarshallable(msg:CMessage) 
{
    match msg
        case CGetRequest(k) => ValidKey(k)
        case CSetRequest(k, v) => ValidKey(k) && ValidOptionalValue(v) 
        case CReply(k, v) => ValidKey(k) && ValidOptionalValue(v) 
        case CRedirect(k, id) => ValidKey(k) && EndPointIsAbstractable(id)
        case CShard(kr, id) => ValidKeyRange(kr) && EndPointIsAbstractable(id) && !EmptyKeyRange(msg.kr)
        case CDelegate(kr, h) => ValidKeyRange(kr) && ValidHashtable(h) && !EmptyKeyRange(msg.range)
}

predicate CSingleMessageMarshallable(msg:CSingleMessage) 
{
    msg.CAck? || (msg.CSingleMessage? && EndPointIsAbstractable(msg.dst) && MessageMarshallable(msg.m))
}

method IsValidKeyPlus(kp:KeyPlus) returns (b:bool)
    ensures b == ValidKeyPlus(kp);
{
    if kp.KeyZero? || kp.KeyInf? {
        b := true;
    } else {
        b := IsKeyValid(kp.k);
    }
}

method IsValidKeyRange(kr:KeyRange) returns (b:bool)
    ensures b == ValidKeyRange(kr);
{
    b := IsValidKeyPlus(kr.klo);
    if b {
        b := IsValidKeyPlus(kr.khi);
    }
}

method IsEmptyKeyRange(kr:KeyRange) returns (b:bool)
    ensures b == EmptyKeyRange(kr);
{
    if kr.khi == kr.klo {
        b := true;
    } else {
        match kr.khi {
            case KeyZero => b := true;
            case KeyInf  => b := false;
            case KeyPlus(k) =>
                match kr.klo {
                    case KeyZero => b := false;
                    case KeyInf  => b := true;
                    case KeyPlus(k') => b := IsKeyLt(k, k');
                }
        }
    }
}

method IsValidHashtable(h:Hashtable) returns (b:bool)
    requires HashtableIs64Bit(h);
    ensures  b == ValidHashtable(h);
{
    b := |h| as uint64 < 62;  // max_hashtable_size

    if !b { return; }

    var keys := domain(h);
    lemma_MapSizeIsDomainSize(keys, h);

    while |keys| as uint64 > 0
        invariant |keys| < max_hashtable_size();
        invariant forall k :: k in keys ==> k in h;
        invariant forall k :: k in h ==> k in keys || (ValidKey(k) && ValidValue(h[k]));
        decreases |keys|;
    {
        var k :| k in keys;
        keys := keys - {k};
        b := IsKeyValid(k);
        if !b {
            return;
        }
        b := IsValueValid(h[k]);
        if !b {
            return;
        }
    }
}

method IsMessageMarshallable(msg:CMessage) returns (b:bool)
    requires CMessageIs64Bit(msg);
    requires CMessageIsAbstractable(msg);
    ensures  b == MessageMarshallable(msg);
{
    match msg 
        case CGetRequest(k) => b := IsKeyValid(k);
        case CSetRequest(k, v) =>
            b := IsKeyValid(k);
            if b && v.ValuePresent? {
                b := IsValueValid(v.v);
            }
        case CReply(k, v) => 
            b := IsKeyValid(k);
            if b && v.ValuePresent? {
                b := IsValueValid(v.v);
            }
        case CRedirect(k, id) => 
            b := IsKeyValid(k);
            b := b && (|id.addr| as uint64 == 4 && 0 <= id.port <= 65535);
        case CShard(kr, id) => 
            b := IsValidKeyRange(kr);
            b := b && (|id.addr| as uint64 == 4 && 0 <= id.port <= 65535);
            if b {
                b := IsEmptyKeyRange(kr);
                b := !b;
            }
        case CDelegate(kr, h) => 
            b := IsValidKeyRange(kr);
            if b {
                b := IsValidHashtable(h);
                if b {
                    b := IsEmptyKeyRange(kr);
                    b := !b;
                }
            }
}

method IsCSingleMessageMarshallable(msg:CSingleMessage) returns (b:bool)
    requires CSingleMessageIsAbstractable(msg);
    requires CSingleMessageIs64Bit(msg);
    ensures  b == CSingleMessageMarshallable(msg);
{
    if msg.CAck? {
        b := true;
    } else if msg.CInvalidMessage? {
        b := false;
    } else {
        assert msg.CSingleMessage?;

        if !(|msg.dst.addr| as uint64 == 4 && 0 <= msg.dst.port <= 65535) {
            b := false;
            return;
        }

        b := IsMessageMarshallable(msg.m);
    }

}


function CMessageIsValid(msg:CMessage) : bool
{
    MessageMarshallable(msg)
}

predicate CPacketIsMarshallable(cp:CPacket)
{
    EndPointIsAbstractable(cp.src) && EndPointIsAbstractable(cp.dst) && CSingleMessageMarshallable(cp.msg) && (cp.msg.CSingleMessage? && cp.msg.m.CShard? ==> cp.msg.m.recipient != cp.dst)
}

predicate CPacketsIsMarshallable(cps:set<CPacket>)
{
    forall cp :: cp in cps ==> CPacketIsMarshallable(cp)
}


method MarshallOptionalValue(c:OptionalValue) returns (val:V)
    requires ValidOptionalValue(c);
    ensures  ValInGrammar(val, OptionalValue_grammar());
    ensures  ValidVal(val);
    ensures  parse_OptionalValue(val) == c;
    ensures  0 <= SizeOfV(val) < 16 + max_val_len();
{
    if c.ValuePresent? {
        var v := MarshallValue(c.v);
        val := VCase(0, v);
    } else {
        reveal_SeqSum();
        val := VCase(1, VTuple([]));
    }
}

method MarshallKeyPlus(c:KeyPlus) returns (val:V)
    requires ValidKeyPlus(c);
    ensures  ValInGrammar(val, KeyPlus_grammar());
    ensures  ValidVal(val);
    ensures  parse_KeyPlus(val) == c;
    ensures  0 <= SizeOfV(val) < 16 + max_key_len();
{
    if c.KeyPlus? {
        var key := MarshallKey(c.k);
        val := VCase(0, key);
    } else if c.KeyZero? {
        val := VCase(1, VUint64(0));
    } else {
        val := VCase(1, VUint64(42));
    }
}

method MarshallKeyRange(c:KeyRange) returns (val:V)
    requires ValidKeyRange(c);
    ensures  ValInGrammar(val, KeyRange_grammar());
    ensures  ValidVal(val);
    ensures  parse_KeyRange(val) == c;
    ensures  0 <= SizeOfV(val) < (16 + max_key_len()) + (16 + max_key_len());
{
    var klo := MarshallKeyPlus(c.klo);
    var khi := MarshallKeyPlus(c.khi);
    val := VTuple([klo, khi]);
    lemma_SeqSum_2(val);
}

// TODO: Refactor this and Paxos' version to put them in a common location
lemma lemma_SeqSum_2(val:V)
    requires val.VTuple?;
    requires |val.t| == 2;
    ensures  SizeOfV(val) == SizeOfV(val.t[0]) + SizeOfV(val.t[1]);
{
    calc {
        SeqSum(val.t);
            { reveal_SeqSum(); }
        SizeOfV(val.t[0]) + SeqSum(val.t[1..]);
            { reveal_SeqSum(); }
        SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SeqSum(val.t[2..]);
            { assert val.t[2..] == []; }        // OBSERVE
        SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SeqSum([]);
            { reveal_SeqSum(); }
        SizeOfV(val.t[0]) + SizeOfV(val.t[1]);
    }
}

lemma lemma_SeqSum_3(val:V)
    requires val.VTuple?;
    requires |val.t| == 3;
    ensures  SizeOfV(val) == SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]);
{
    calc {
        SeqSum(val.t);
            { reveal_SeqSum(); }
        SizeOfV(val.t[0]) + SeqSum(val.t[1..]);
            { reveal_SeqSum(); }
        SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SeqSum(val.t[2..]);
            { reveal_SeqSum(); }
        SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SeqSum(val.t[3..]);
            { assert val.t[3..] == []; }        // OBSERVE
        SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SeqSum([]);
            { reveal_SeqSum(); }
        SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]);
    }

}

method MarshallHashtable(c:Hashtable) returns (val:V)
    requires ValidHashtable(c);
    ensures  ValInGrammar(val, Hashtable_grammar());
    ensures  ValidVal(val);
    ensures  parse_Hashtable(val) == c;
    ensures  |c| == |val.a|;
    ensures SeqSum(val.a) <= |c| * ((8 + max_key_len()) + (8 + max_val_len()));
{
    if |c| == 0 {
        val := VArray([]);
        reveal_SeqSum();
    } else {
        lemma_non_empty_map_has_elements(c);
        var key := 0;
        key :| key in c;
        var marshalled_key := MarshallKey(key);
        var marshalled_value := MarshallValue(c[key]);
        var remainder := RemoveElt(c, key);
        var marshalled_remainder := MarshallHashtable(remainder);
        assert parse_Hashtable(marshalled_remainder) == remainder;
        val := VArray([VTuple([marshalled_key, marshalled_value])] + marshalled_remainder.a);

        // OBSERVE (everything below; not sure which bit is critical to proving the final ensures)
        ghost var tuple := val.a[0];
        ghost var rest := val.a[1..];
        ghost var key' := parse_Key(tuple.t[0]);
        ghost var value' := parse_Value(tuple.t[1]);
        ghost var others' := parse_Hashtable(VArray(val.a[1..]));
        ghost var m' := others'[key' := value'];
        assert key' == key;
        assert value' == c[key];
        assert others' == remainder;
        assert m' == c;

        // Prove the SeqSum ensures
        calc {
            SeqSum(val.a);
                { reveal_SeqSum(); }
            SizeOfV(val.a[0]) + SeqSum(val.a[1..]);
            <=  
            SizeOfV(val.a[0]) + |remainder| * ((8 + max_key_len()) + (8 + max_val_len()));
                { lemma_SeqSum_2(val.a[0]); }
            SizeOfV(val.a[0].t[0]) + SizeOfV(val.a[0].t[1]) + |remainder| * ((8 + max_key_len()) + (8 + max_val_len()));
            <   //{ lemma_Vote_Val_Valid(c[op], val.a[0].t[1]); lemma_Vote_bound(c[op], val.a[0].t[1]); }
            ((8 + max_key_len()) + (8 + max_val_len())) + |remainder| * ((8 + max_key_len()) + (8 + max_val_len()));
            1*((8 + max_key_len()) + (8 + max_val_len())) + |remainder| * ((8 + max_key_len()) + (8 + max_val_len()));
                { lemma_mul_is_distributive(((8 + max_key_len()) + (8 + max_val_len())), 1, |remainder|); }
            (1+|remainder|) * ((8 + max_key_len()) + (8 + max_val_len()));
            |c| * ((8 + max_key_len()) + (8 + max_val_len()));
        }
    }
}

method MarshallEndPoint(c:EndPoint) returns (val:V)
    requires EndPointIsAbstractable(c);
    ensures  ValInGrammar(val, EndPoint_grammar());
    ensures  ValidVal(val);
    ensures  parse_EndPoint(val) == c;
{
    val := VUint64(ConvertEndPointToUint64(c));
    Uint64EndPointRelationships();
}

method MarshallMessage_GetRequest(c:CMessage) returns (val:V)
    requires MessageMarshallable(c);
    requires c.CGetRequest?;
    ensures  ValInGrammar(val, CMessage_GetRequest_grammar());
    ensures  ValidVal(val);
    ensures  parse_Message_GetRequest(val) == c;
    ensures  0 <= SizeOfV(val) < MaxPacketSize() - 32;
{
    val := MarshallKey(c.k_getrequest);
}

method MarshallMessage_SetRequest(c:CMessage) returns (val:V)
    requires MessageMarshallable(c);
    requires c.CSetRequest?;
    ensures  ValInGrammar(val, CMessage_SetRequest_grammar());
    ensures  ValidVal(val);
    ensures  parse_Message_SetRequest(val) == c;
    ensures  0 <= SizeOfV(val) < MaxPacketSize() - 32;
{
    var k_setrequest := MarshallKey(c.k_setrequest);
    var v_setrequest := MarshallOptionalValue(c.v_setrequest);
    val := VTuple([k_setrequest, v_setrequest]);
    lemma_SeqSum_2(val);
}

method MarshallMessage_Reply(c:CMessage) returns (val:V)
    requires MessageMarshallable(c);
    requires c.CReply?;
    ensures  ValInGrammar(val, CMessage_Reply_grammar());
    ensures  ValidVal(val);
    ensures  parse_Message_Reply(val) == c;
    ensures  0 <= SizeOfV(val) < MaxPacketSize() - 32;
{
    var k_reply := MarshallKey(c.k_reply);
    var v := MarshallOptionalValue(c.v);
    val := VTuple([k_reply, v]);
    lemma_SeqSum_2(val);
}

method MarshallMessage_Redirect(c:CMessage) returns (val:V)
    requires MessageMarshallable(c);
    requires c.CRedirect?;
    ensures  ValInGrammar(val, CMessage_Redirect_grammar());
    ensures  ValidVal(val);
    ensures  parse_Message_Redirect(val) == c;
    ensures  0 <= SizeOfV(val) < MaxPacketSize() - 32;
{
    var k_redirect := MarshallKey(c.k_redirect);
    var ep := MarshallEndPoint(c.id);
    val := VTuple([k_redirect, ep]);
    lemma_SeqSum_2(val);
}

method MarshallMessage_Shard(c:CMessage) returns (val:V)
    requires MessageMarshallable(c);
    requires c.CShard?;
    ensures  ValInGrammar(val, CMessage_Shard_grammar());
    ensures  ValidVal(val);
    ensures  parse_Message_Shard(val) == c;
    ensures  0 <= SizeOfV(val) < MaxPacketSize() - 32;
{
    var k_redirect := MarshallKeyRange(c.kr);
    var ep := MarshallEndPoint(c.recipient);
    val := VTuple([k_redirect, ep]);
    lemma_SeqSum_2(val);
}

method MarshallMessage_Delegate(c:CMessage) returns (val:V)
    requires MessageMarshallable(c);
    requires c.CDelegate?;
    ensures  ValInGrammar(val, CMessage_Delegate_grammar());
    ensures  ValidVal(val);
    ensures  parse_Message_Delegate(val) == c;
    ensures  0 <= SizeOfV(val) < MaxPacketSize() - 32;
{
    var range := MarshallKeyRange(c.range);
    var h := MarshallHashtable(c.h);
    val := VTuple([range, h]);

    calc {
        SizeOfV(val);
            { lemma_SeqSum_2(val); }
        SizeOfV(val.t[0]) + SizeOfV(val.t[1]);
        < 
        (16 + max_key_len()) + (16 + max_key_len()) + SizeOfV(val.t[1]);
        <=
        (16 + max_key_len()) + (16 + max_key_len()) + 8 + |c.h| * ((8 + max_key_len()) + (8 + max_val_len()));
            { lemma_mul_is_distributive_add_forall(); } 
        (16 + max_key_len()) + (16 + max_key_len()) + 8 + |c.h| * (8 + max_key_len()) + |c.h| * (8 + max_val_len());
            { lemma_mul_is_distributive_add_forall(); } 
        (16 + max_key_len()) + (16 + max_key_len()) + 8 + |c.h| * 8 + |c.h| * max_key_len() + |c.h| * 8 + |c.h| * max_val_len();
        <
        MaxPacketSize() - 32;
    }

}

method MarshallMessage(c:CMessage) returns (val:V)
    requires MessageMarshallable(c);
    ensures  ValInGrammar(val, CMessage_grammar());
    ensures  ValidVal(val);
    ensures  parse_Message(val) == c;
    ensures  0 <= SizeOfV(val) < MaxPacketSize() - 24;
{
    if c.CGetRequest? {
        var msg := MarshallMessage_GetRequest(c);  
        val := VCase(0, msg); 
    } else if c.CSetRequest? {
        var msg := MarshallMessage_SetRequest(c);  
        val := VCase(1, msg); 
    } else if c.CReply? {
        var msg := MarshallMessage_Reply(c);  
        val := VCase(2, msg); 
    } else if c.CRedirect? {
        var msg := MarshallMessage_Redirect(c);  
        val := VCase(3, msg); 
    } else if c.CShard? {
        var msg := MarshallMessage_Shard(c);  
        val := VCase(4, msg); 
    } else if c.CDelegate? {
        var msg := MarshallMessage_Delegate(c);  
        val := VCase(5, msg); 
    } else {
        assert false;
    }
}

method MarshallCSingleMessage(c:CSingleMessage) returns (val:V)
    requires CSingleMessageMarshallable(c);
    ensures  ValInGrammar(val, CSingleMessage_grammar());
    ensures  ValidVal(val);
    ensures  parse_CSingleMessage(val) == c;
    ensures  0 <= SizeOfV(val) < MaxPacketSize();
{
    if c.CSingleMessage? {
        var ep := MarshallEndPoint(c.dst);
        var msg := MarshallMessage(c.m);

        var tuple := VTuple([VUint64(c.seqno), ep, msg]);
        lemma_SeqSum_3(tuple);
        assert ValidVal(tuple);     // OBSERVE
        val := VCase(0, tuple);
    } else {
        val := VCase(1, VUint64(c.ack_seqno));
    }
}

////////////////////////////////////////////////////////////////////////
// These functions need to be here, rather than CMessageRefinements.i.dfy,
// since they depend on SHTDemarshallData
////////////////////////////////////////////////////////////////////////

function AbstractifyBufferToLSHTPacket(src:EndPoint, dst:EndPoint, data:seq<byte>) : LSHTPacket
    requires EndPointIsValidIPV4(src);
    requires EndPointIsValidIPV4(dst);
{
    LPacket(AbstractifyEndPointToNodeIdentity(dst),
           AbstractifyEndPointToNodeIdentity(src),
           AbstractifyCSingleMessageToSingleMessage(SHTDemarshallData(data)))
}

predicate BufferRefinementAgreesWithMessageRefinement(msg:CSingleMessage, marshalled:seq<byte>)
    requires CSingleMessageIsAbstractable(msg);
    requires CSingleMessageIsAbstractable(msg);
{
    forall src, dst :: (EndPointIsValidIPV4(src) && EndPointIsValidIPV4(dst)) ==>

            (AbstractifyBufferToLSHTPacket(src, dst, marshalled)
            == LPacket(AbstractifyEndPointToNodeIdentity(dst), AbstractifyEndPointToNodeIdentity(src), AbstractifyCSingleMessageToSingleMessage(msg)))
}

function AbstractifyCPacketToLSHTPacket(cp:CPacket) : LSHTPacket
    requires CPacketIsAbstractable(cp);
{
    LPacket(AbstractifyEndPointToNodeIdentity(cp.dst), AbstractifyEndPointToNodeIdentity(cp.src), AbstractifyCSingleMessageToSingleMessage(cp.msg))
}


function AbstractifyUdpPacketToLSHTPacket(udp:UdpPacket) : LSHTPacket
    requires UdpPacketIsAbstractable(udp);
{
    AbstractifyBufferToLSHTPacket(udp.src, udp.dst, udp.msg)
}

function AbstractifyUdpPacketToShtPacket(udp:UdpPacket) : Packet
    requires UdpPacketIsAbstractable(udp);
{
    var lp:= AbstractifyUdpPacketToLSHTPacket(udp);
    Packet(lp.dst, lp.src, lp.msg)
}

predicate UdpPacketIsAbstractable(udp:UdpPacket)
{
      EndPointIsValidIPV4(udp.src)
    && EndPointIsValidIPV4(udp.dst)
}

predicate UdpPacketsIsAbstractable(udpps:set<UdpPacket>)
{
    forall p :: p in udpps ==> UdpPacketIsAbstractable(p)
}

lemma lemma_CSingleMessage_grammar_valid()
    ensures ValidGrammar(CSingleMessage_grammar());
{
    var g := CSingleMessage_grammar();
    assert |g.cases| < 0x1_0000_0000_0000_0000;
    
    lemma_ValidKey_grammer();
    lemma_ValidValue_grammer();

    assert ValidGrammar(Key_grammar());
    assert ValidGrammar(Value_grammar());
    assert ValidGrammar(OptionalValue_grammar());
    assert ValidGrammar(CMessage_GetRequest_grammar());
    assert ValidGrammar(CMessage_SetRequest_grammar());
    assert ValidGrammar(CMessage_Reply_grammar());
    assert ValidGrammar(CMessage_Redirect_grammar());
    assert ValidGrammar(CMessage_Shard_grammar());
    assert ValidGrammar(CMessage_Delegate_grammar());
}

method SHTMarshall(msg:CSingleMessage) returns (data:array<byte>)
    requires CSingleMessageIsAbstractable(msg);
    requires CSingleMessageMarshallable(msg);
    ensures fresh(data);
    ensures UdpPacketBound(data[..]);
    ensures BufferRefinementAgreesWithMessageRefinement(msg, data[..]);
{
    var val := MarshallCSingleMessage(msg);
    lemma_CSingleMessage_grammar_valid();
    data := Marshall(val, CSingleMessage_grammar());

    forall src, dst | EndPointIsValidIPV4(src) && EndPointIsValidIPV4(dst) 
        ensures AbstractifyBufferToLSHTPacket(src, 
                                     dst, 
                                     data[..])
                == LPacket(AbstractifyEndPointToNodeIdentity(dst), AbstractifyEndPointToNodeIdentity(src), AbstractifyCSingleMessageToSingleMessage(msg));
    {
        calc {
            AbstractifyBufferToLSHTPacket(src, 
                                 dst, 
                                 data[..]);
            LPacket(AbstractifyEndPointToNodeIdentity(dst),
                   AbstractifyEndPointToNodeIdentity(src),
                   AbstractifyCSingleMessageToSingleMessage(SHTDemarshallData(data[..])));
                //{ lemma_NodeIdentityToEndPoint(dst); lemma_NodeIdentityToEndPoint(src); }
            LPacket(AbstractifyEndPointToNodeIdentity(dst), AbstractifyEndPointToNodeIdentity(src), AbstractifyCSingleMessageToSingleMessage(SHTDemarshallData(data[..])));
            LPacket(AbstractifyEndPointToNodeIdentity(dst), AbstractifyEndPointToNodeIdentity(src), AbstractifyCSingleMessageToSingleMessage(msg));
        }
    }
}


//////////////////////////////////////////////////////////////////////////////
// Sendable predicates

predicate CPacketIsValid(cpacket:CPacket, params:CParameters)
{
    CPacketIsAbstractable(cpacket) && CSingleMessageIsValid(cpacket.msg, params) && CSingleMessageMarshallable(cpacket.msg)
}

predicate CPacketIsSendable(cpacket:CPacket)
{
    CPacketIsAbstractable(cpacket) && CSingleMessageMarshallable(cpacket.msg)
}

predicate CPacketSetIsSendable(cps:set<CPacket>)
{
    forall p :: p in cps ==> CPacketIsSendable(p)
}

predicate CPacketSeqIsSendable(cps:seq<CPacket>)
{
    forall i :: 0<=i<|cps| ==> CPacketIsSendable(cps[i])
}

predicate OutboundPacketsIsValid(out:CPacket)
{
    CPacketIsSendable(out) && (out.msg.CSingleMessage? || out.msg.CAck?) && CSingleMessageMarshallable(out.msg)
}

predicate OutboundPacketsSeqIsValid(cpackets:seq<CPacket>)
{
    forall i :: 0 <= i < |cpackets| ==> OutboundPacketsIsValid(cpackets[i])
}

predicate OutboundPacketsIsAbstractable(out:CPacket)
{
   CPacketIsAbstractable(out)
}

function AbstractifyOutboundPacketsToLSHTPacket(out:CPacket) : LSHTPacket
    requires OutboundPacketsIsAbstractable(out);
{
    AbstractifyCPacketToLSHTPacket(out)
}

function {:opaque} AbstractifyOutboundPacketsToSeqOfLSHTPackets(out:seq<CPacket>) : seq<LSHTPacket>
    requires forall i :: 0 <= i < |out| ==> CPacketIsAbstractable(out[i]);
    ensures |AbstractifyOutboundPacketsToSeqOfLSHTPackets(out)| == |out|;
    ensures forall i :: 0 <= i < |out| ==> AbstractifyOutboundPacketsToSeqOfLSHTPackets(out)[i] == AbstractifyCPacketToLSHTPacket(out[i]);
{
    if out == [] then
        []
    else if |out| == 1 then
        [AbstractifyCPacketToLSHTPacket(out[0])]
    else
        [AbstractifyCPacketToLSHTPacket(out[0])] + AbstractifyOutboundPacketsToSeqOfLSHTPackets(out[1..])
        
}

predicate OutboundPacketsHasCorrectSrc(out:CPacket, me:EndPoint)
{
    out.src == me
}

predicate OutboundPacketsSeqHasCorrectSrc(cpackets:seq<CPacket>, me:EndPoint)
{
    forall cpacket :: cpacket in cpackets ==> OutboundPacketsHasCorrectSrc(cpacket, me)
}
} 
