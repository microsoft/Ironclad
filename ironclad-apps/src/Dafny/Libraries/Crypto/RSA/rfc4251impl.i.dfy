//-<NuBuild BasmEnableSymdiff true />
//-<NuBuild AddDafnyFlag /z3opt:ARITH_RANDOM_SEED=2 />
include "../../BigNum/BigNum.i.dfy"
include "rfc4251.s.dfy"
include "RSASpec.s.dfy"
include "../../Util/seqs_simple.i.dfy"
include "BlockEncoding.i.dfy"
include "KeyImpl.i.dfy"
include "../../FatNat/FatNatModesty.i.dfy"

static function method{:CompiledSpec} CompiledSpec_STR_SSH_RSA() : seq<int>

static method rfc4251_encode_word32(w:int) returns (msg:seq<int>)
    requires Word32(w);    //- redundant; falls out of definition.
    ensures IsByteSeq(msg);
    ensures msg == rfc4251_word32_encoding(w);
    ensures |msg|==4;
{
    var wordseq := [w];
    msg := BEWordSeqToByteSeq_impl(wordseq);
}

static method rfc4251_encode_string(s:seq<int>) returns (msg:seq<int>)
    requires IsByteSeq(s);
    requires Word32(|s|);
    ensures IsByteSeq(msg);
    ensures msg == rfc4251_string_encoding(s);
{
    var l := rfc4251_encode_word32(|s|);
    msg := l + s;

    assert msg[0..4] == l;
}

static lemma lemma_rfc4251_positive_to_twoscomplement(s:seq<int>)
    requires IsByteSeq(s);
    ensures |rfc4251_positive_to_twoscomplement(s)| <= |s|+1;
    ensures IsByteSeq(rfc4251_positive_to_twoscomplement(s));
{
}

static function rfc4251_positive_to_twoscomplement_premium(s:seq<int>) : seq<int>
    requires IsByteSeq(s);
    ensures |rfc4251_positive_to_twoscomplement(s)| <= |s|+1;
    ensures IsByteSeq(rfc4251_positive_to_twoscomplement(s));
    ensures rfc4251_positive_to_twoscomplement_premium(s)
        == rfc4251_positive_to_twoscomplement(s);
{
    lemma_rfc4251_positive_to_twoscomplement(s);
    rfc4251_positive_to_twoscomplement(s)
}

static lemma lemma_BEIntToByteSeq_length_bound(v:int)
    requires 0 <= v < power2(power2(34));   
    ensures |BEIntToByteSeq(v)| < power2(32)-1;
{
    lemma_2toX();
    var vs := BEIntToByteSeq(v);
    if (v==0)
    {
        reveal_BEIntToDigitSeq_private();
        assert |vs| == 0;
    }
    else
    {
        if (power2(32)-1 <= |vs|) {
            lemma_2to32();
            lemma_power2_add8(24);
            lemma_power2_add8(32);
            calc {
                v;
                <   //- { requires assumption }
                power2(power2(34));
                power2(8 * power2(31));
                    { lemma_mul_is_mul_boogie(8, power2(31)); }
//-dafnycc                power2(mul(8,power2(31)));
                    { lemma_power2_is_power_2(mul(8,power2(31))); }
                power(2, mul(8,power2(31)));
                    { lemma_power_multiplies(2, 8, power2(31)); }
                power(power(2,8), power2(31));
                    { lemma_power2_is_power_2(8); }
                power(256, power2(31));
                <=  { lemma_power_increases(256, power2(31), power2(32)-2); }
                power(256, power2(32)-2);
                <=  { lemma_power_increases(256, power2(32)-2, |vs|-1); } //- contradiction hyp
                power(256, |vs|-1);
                power(power2(8), |vs|-1);
                <=  { lemma_BEIntToDigitSeq_properties(power2(8), 0, v); }
                v;
            }
            assert false;
        }
    }

    lemma_2toX();
    assert 0 <= |vs| < power2(32)-1;
}

static lemma lemma_TwosComplement_length_bound(x:int)
    requires 0 <= x < power2(power2(34));   
    ensures |rfc4251_positive_to_twoscomplement(BEIntToByteSeq(x))| < power2(32);
{
    lemma_BEIntToByteSeq_length_bound(x);
}

static lemma lemma_rfc4251_mpint_encoding_premium(v:nat)
    requires v < power2(power2(34));
    ensures |rfc4251_positive_to_twoscomplement(BEIntToByteSeq(v))| < power2(32);
    ensures IsByteSeq(rfc4251_mpint_encoding(v));
{
    lemma_2toX();
    lemma_TwosComplement_length_bound(v);

    lemma_BEIntToByteSeq_decoding(v);
    var vs := BEIntToByteSeq(v);
    lemma_BEIntToDigitSeq_properties(power2(8), 0, v);
    assert v>0 ==> power(power2(8), |vs|-1) <= v;
    
    var tc := rfc4251_positive_to_twoscomplement(vs);
    assert |tc| <= |vs|+1;

    assert 0 <= |tc| < power2(32);

    lemma_BEInt_decoding_general(power2(8), 4, |tc|);

    assert IsDigitSeq(power2(8), BEIntToDigitSeq(power2(8), 4, |tc|));
    assert IsByteSeq(BEIntToDigitSeq(power2(8), 4, |tc|));

    assert IsDigitSeq(power2(32), [|tc|]);
    lemma_BEDigitSeqToInt_bound(power2(32), [|tc|]);
    lemma_BEIntToDigitSeq_produces_DigitSeq(power2(8), 4, BEDigitSeqToInt(power2(32), [|tc|]));
    assert IsDigitSeq(power2(8), BEIntToDigitSeq(power2(8), 4, BEDigitSeqToInt(power2(32), [|tc|])));
    assert IsByteSeq(BEIntToDigitSeq(power2(8), 4, BEDigitSeqToInt(power2(32), [|tc|])));

    calc {
        BEIntToDigitSeq(power2(8), 4, BEDigitSeqToInt(power2(32), [|tc|]));
        BEIntToDigitSeq(power2(8), |[|tc|]|*4, BEDigitSeqToInt(power2(32), [|tc|]));
        BEWordSeqToByteSeq([|tc|]);
        rfc4251_word32_encoding(|tc|);
    }

    assert IsByteSeq(rfc4251_word32_encoding(|tc|));
    assert IsByteSeq(tc);
    assert IsByteSeq(rfc4251_mpint_encoding(v));
}

static function rfc4251_mpint_encoding_premium(v:nat) : seq<int>
    requires v < power2(power2(34));
    ensures IsByteSeq(BEIntToByteSeq(v));
    ensures IsByteSeq(rfc4251_mpint_encoding_premium(v));
    ensures IsDigitSeq(power2(32), [|rfc4251_positive_to_twoscomplement(BEIntToByteSeq(v))|]);
    ensures rfc4251_mpint_encoding_premium(v) == rfc4251_mpint_encoding(v);
{
    lemma_BEIntToByteSeq_decoding(v);
    var tc := rfc4251_positive_to_twoscomplement(BEIntToByteSeq(v));
    assert 0<=|tc|;
    
    lemma_rfc4251_mpint_encoding_premium(v);
    assert IsDigitSeq(power2(32), [|tc|]);
    rfc4251_word32_encoding(|tc|) + tc
}

lemma lemma_rfc4251_modesty_suffices_for_encoding(V:array<int>)
    requires ModestFatNatValue(V);
    ensures J(V) < power2(power2(34));
{
    lemma_power2_strictly_increases(31, 34);
    lemma_power2_strictly_increases(power2(31), power2(34));
}

method {:dafnycc_conservative_seq_triggers} rfc4251_encode_mpint(V:array<int>) returns (msg:seq<int>)
    requires ModestFatNatValue(V);
    ensures J(V) < power2(power2(34));
    ensures IsByteSeq(msg);
    ensures msg == rfc4251_mpint_encoding_premium(J(V));
{
    lemma_rfc4251_modesty_suffices_for_encoding(V);

    
    var v_bytes := IntegerToBESeq(V);

    lemma_2to32();

    assert J(V) < power2(power2(31));
    if (|v_bytes|>2)
    {
        assert power2(8*(|v_bytes|-2)) <= BigEndianIntegerValue(v_bytes);

        lemma_2to32();
        lemma_power2_add8(0);
        lemma_power2_add8(24);
        calc ==> {
            power2(8*(|v_bytes|-2)) <= power2(power2(31));
                { lemma_power2_increases_converse(8*(|v_bytes|-2), power2(31)); }
            8*(|v_bytes|-2) <= power2(31);
            |v_bytes|-2 <= power2(28);
            |v_bytes| < Width();
        }
        assert Word32(|v_bytes|);
    }
    else
    {
        assert |v_bytes| <= 2;
        assert Word32(|v_bytes|);
    }
    assert Word32(|v_bytes|);

    if (|v_bytes|>=2 && v_bytes[1]<128)
    {
        ghost var old_v_bytes := v_bytes;
        v_bytes := v_bytes[1..];
        lemma_BigEndianIntegerValue_zero_prefix(old_v_bytes, v_bytes);
    }
    else if (|v_bytes|==1)
    {
        ghost var old_v_bytes := v_bytes;
        assert v_bytes[0]==0;
        v_bytes := [];
    }

    assert Word32(|v_bytes|);
    var v_seq := v_bytes;
    var len_bits := rfc4251_encode_word32(|v_seq|);
    msg := len_bits + v_seq;

    assert msg[0..4] == len_bits;
}

static lemma lemma_rfc4251_modest_twoscomplement(v:nat)
    requires 0 <= v < power2(power2(34));
    ensures |rfc4251_positive_to_twoscomplement(BEIntToByteSeq(v))| < power2(32);
{
    lemma_BEIntToByteSeq_length_bound(v);
    assert |BEIntToByteSeq(v)| < power2(32)-1;
}

static lemma lemma_rfc4251_word32_encoding(w:int)
    requires 0 <= w < power2(32);
    ensures IsByteSeq(rfc4251_word32_encoding(w));
{
    lemma_2toX();
    lemma_BEDigitSeqToInt_bound(power2(32), [w]);
    lemma_BEIntToDigitSeq_produces_DigitSeq(power2(8), 4, BEWordSeqToInt([w]));
}

static function rfc4251_word32_encoding_premium(w:int) : seq<int>
    requires 0 <= w < power2(32);
    ensures rfc4251_word32_encoding(w) == rfc4251_word32_encoding_premium(w);
    ensures IsByteSeq(rfc4251_word32_encoding(w));
{
    lemma_rfc4251_word32_encoding(w);
    rfc4251_word32_encoding(w)
}

static lemma lemma_rfc4251_string_encoding(s:seq<int>)
    requires IsByteSeq(s);
    requires |s| < power2(32);
    ensures IsByteSeq(rfc4251_string_encoding(s));
{
    assert rfc4251_string_encoding(s) == rfc4251_word32_encoding_premium(|s|) + s;
}

static function rfc4251_string_encoding_premium(s:seq<int>) : seq<int>
    requires IsByteSeq(s);
    requires |s| < power2(32);
    ensures rfc4251_string_encoding(s) == rfc4251_string_encoding_premium(s);
    ensures IsByteSeq(rfc4251_string_encoding(s));
{
    lemma_rfc4251_string_encoding(s);
    rfc4251_string_encoding(s)
}

static lemma lemma_rfc4251_sshrsa_encoding_premium(e:nat, n:nat)
    requires e < power2(power2(34));
    requires n < power2(power2(34));
    ensures IsWordSeq([|STR_SSH_RSA()|]);
    ensures IsWordSeq([|rfc4251_positive_to_twoscomplement(BEIntToByteSeq(e))|]);
    ensures IsWordSeq([|rfc4251_positive_to_twoscomplement(BEIntToByteSeq(n))|]);
    ensures IsByteSeq(rfc4251_sshrsa_encoding(e,n));
{
    lemma_2toX();
    lemma_rfc4251_modest_twoscomplement(e);
    lemma_rfc4251_modest_twoscomplement(n);
    assert IsByteSeq(rfc4251_string_encoding_premium(STR_SSH_RSA()));
    lemma_rfc4251_mpint_encoding_premium(e);
    assert rfc4251_mpint_encoding(e) == rfc4251_mpint_encoding_premium(e);
    assert IsByteSeq(rfc4251_mpint_encoding_premium(e));
    lemma_rfc4251_mpint_encoding_premium(n);
    assert rfc4251_mpint_encoding(n) == rfc4251_mpint_encoding_premium(n);
    assert IsByteSeq(rfc4251_mpint_encoding(n));
}

static function rfc4251_sshrsa_encoding_premium(e:nat, n:nat) : seq<int>
    requires e < power2(power2(34));
    requires n < power2(power2(34));
    ensures IsWordSeq([|STR_SSH_RSA()|]);
    ensures IsWordSeq([|rfc4251_positive_to_twoscomplement(BEIntToByteSeq(e))|]);
    ensures IsWordSeq([|rfc4251_positive_to_twoscomplement(BEIntToByteSeq(n))|]);
    ensures rfc4251_sshrsa_encoding_premium(e,n) == rfc4251_sshrsa_encoding(e,n);
{
    lemma_rfc4251_sshrsa_encoding_premium(e,n);
    rfc4251_sshrsa_encoding(e,n)
}

static function rfc4251_sshrsa_pubkey_encoding_premium(pubkey:RSAPubKeySpec) : seq<int>
    requires WellformedRSAPubKeySpec(pubkey);
    requires pubkey.e < power2(power2(34));
    requires pubkey.n < power2(power2(34));
    ensures IsWordSeq([|STR_SSH_RSA()|]);
    ensures IsWordSeq([|rfc4251_positive_to_twoscomplement(BEIntToByteSeq(pubkey.e))|]);
    ensures IsWordSeq([|rfc4251_positive_to_twoscomplement(BEIntToByteSeq(pubkey.n))|]);
    ensures rfc4251_sshrsa_pubkey_encoding_premium(pubkey) == rfc4251_sshrsa_pubkey_encoding(pubkey);
{
    lemma_rfc4251_sshrsa_encoding_premium(pubkey.e, pubkey.n);
    rfc4251_sshrsa_pubkey_encoding(pubkey)
}

method rfc4251_encode_sshrsa_inner(E:array<int>, N:array<int>) returns (msg:seq<int>)
    requires ModestFatNatValue(E);
    requires ModestFatNatValue(N);
    ensures IsByteSeq(msg);
    ensures J(E) < power2(power2(34));
    ensures J(N) < power2(power2(34));
    ensures msg == rfc4251_sshrsa_encoding_premium(J(E), J(N));
{
    lemma_rfc4251_modesty_suffices_for_encoding(E);
    lemma_rfc4251_modesty_suffices_for_encoding(N);

    lemma_2to32();
    //-    reveal_rfc4251_sshrsa_encoding();
    assert |STR_SSH_RSA()| < power2(32);

    var enc_s := rfc4251_encode_string(STR_SSH_RSA());
    var enc_e := rfc4251_encode_mpint(E);
    var enc_n := rfc4251_encode_mpint(N);

    msg := enc_s + enc_e + enc_n;

    assert IsByteSeq(enc_s);
    assert IsByteSeq(enc_e);
    assert IsByteSeq(enc_n);
    assert IsByteSeq(msg);
    assert enc_s == rfc4251_string_encoding(STR_SSH_RSA());
    assert enc_e == rfc4251_mpint_encoding_premium(J(E));
    assert enc_n == rfc4251_mpint_encoding_premium(J(N));
    assert msg == rfc4251_sshrsa_encoding_premium(J(E), J(N));
}

method rfc4251_encode_sshrsa_pubkey_internal(pubkey:RSAPubKeyImpl_internal) returns (msg:seq<int>)
    requires ModestFatNatValue(pubkey.e);
    requires ModestFatNatValue(pubkey.n);
    requires WellformedRSAPubKeyImpl_internal(pubkey);
    ensures IsByteSeq(msg);
    ensures PubKeyImplToSpec_internal(pubkey).e < power2(power2(34));
    ensures PubKeyImplToSpec_internal(pubkey).n < power2(power2(34));
    ensures msg == rfc4251_sshrsa_pubkey_encoding_premium(PubKeyImplToSpec_internal(pubkey));
{
    lemma_power2_increases(30, 34);
    lemma_power2_increases(power2(30), power2(34));
//-    lemma_frumpy_is_modest(pubkey.e);
//-    lemma_modesty_word_value_equivalence(pubkey.e);
//-    lemma_frumpy_is_modest(pubkey.n);
//-    lemma_modesty_word_value_equivalence(pubkey.n);
    msg := rfc4251_encode_sshrsa_inner(pubkey.e, pubkey.n);
}

//-////////////////////////////////////////////////////////////////////////////
//- decoding

method rfc4251_decode_word32(msg:seq<int>) returns (success:bool, w:int, bytes_consumed:int)
    requires IsByteSeq(msg);
    requires public(msg);
    ensures Word32(w);
    ensures 0 <= bytes_consumed <= 4;
    ensures success ==> 4<=|msg|;
    ensures success ==> (msg[..bytes_consumed] == rfc4251_word32_encoding(w));
    ensures public(success);
    ensures public(w);
    ensures public(bytes_consumed);
{
    if (|msg|<4)
    {
        success := false;
        w := 0;
        bytes_consumed := 0;
        return;
    }
    else
    {
        var wordseq,padbytes := BEByteSeqToWordSeq_impl(msg[..4]);
//-        assert |wordseq| == 1;
//-        assert |padbytes| == 0;
        success := true;
        w := wordseq[0];
        assert wordseq == [w];  //- hint required
        bytes_consumed := 4;
    }
}

method rfc4251_decode_string(msg:seq<int>) returns (success:bool, s:seq<int>, bytes_consumed:int)
    requires IsByteSeq(msg);
    requires Word32(|msg|);
    requires public(msg);
    ensures IsByteSeq(s);
    ensures Word32(|s|);
    ensures 0 <= bytes_consumed <= |msg|;
    ensures success ==> (msg[..bytes_consumed] == rfc4251_string_encoding(s));
    ensures public(success);
    ensures public(s);
    ensures public(bytes_consumed);
{
    //- failure case return values
    success := false;
    bytes_consumed := 0;
    s := [];

    var subrc,l,sub_bytes_consumed := rfc4251_decode_word32(msg);
    if (!subrc || !(0 <= l <= |msg|-sub_bytes_consumed))
    {
        return;
    }

    s := msg[sub_bytes_consumed .. sub_bytes_consumed + l];
    bytes_consumed := sub_bytes_consumed + l;
    success := true;    // fixed liveness bug
}

lemma lemma_rfc4251_modesty_helper()
    ensures 0 < power2(power2(31));
    ensures 0 < power2(power2(34));
    ensures power2(power2(31)) < power2(power2(34));
{
    calc {
        0;
        <   { lemma_power2_0_is_1(); }
        power2(0);
        <=  { lemma_power2_increases(0, power2(31)); }
        power2(power2(31));
    }
    lemma_power2_strictly_increases(31, 34);
    lemma_power2_strictly_increases(power2(31), power2(34));
}

method rfc4251_decode_mpint(msg:seq<int>) returns (success:bool,V:array<int>,bytes_consumed:int)
    requires IsByteSeq(msg);
    requires public(msg);
    ensures ModestFatNatValue(V);
    ensures J(V) < power2(power2(34));
    ensures 0 <= bytes_consumed <= |msg|;
    ensures success ==> (msg[..bytes_consumed] == rfc4251_mpint_encoding_premium(J(V)));
    ensures public(success);
    ensures public(J(V));
    ensures public(bytes_consumed);
{
    lemma_2toX32();

    success := false;
    V := FatNatZero();
    bytes_consumed := 0;
    lemma_rfc4251_modesty_helper();

    var subrc,l,sub_bytes_consumed := rfc4251_decode_word32(msg);
    if (!subrc || !(0 <= l <= |msg|-sub_bytes_consumed))
    {
        return;
    }

    var S := msg[sub_bytes_consumed .. sub_bytes_consumed + l];
    bytes_consumed := sub_bytes_consumed + l;

    var power2_28 := 0x10000000;
    if (|S| >= power2_28)
    {
        //- encoded integer too big
        return;
    }
    if (|S|>0 && S[0] >= 128)
    {
        //- msg encodes negative integer
        return;
    }

    if (|S|>0 && S[0]==0)
    {
        if (|S|-1==0 || S[1]<128)
        {
            //- message has an improper number of leading zeros.
            return;
        }
    }

    success := true;
    V := rfc4251_decode_mpint_common_case(msg, l, sub_bytes_consumed, S, bytes_consumed);
}

method {:dafnycc_conservative_seq_triggers} rfc4251_decode_mpint_common_case(msg:seq<int>, w:int, sub_bytes_consumed:int, S:seq<int>, bytes_consumed:int) returns (V:array<int>)
    requires IsByteSeq(msg);
    requires Word32(w);
    requires 4 <= |msg|;
    requires 0 <= w <= |msg|-sub_bytes_consumed;
    requires 0 <= sub_bytes_consumed;
    requires msg[..sub_bytes_consumed] == rfc4251_word32_encoding(w);
    requires bytes_consumed == sub_bytes_consumed + w;
    requires 0 <= bytes_consumed <= |msg|;
    requires S == msg[sub_bytes_consumed .. bytes_consumed];
    requires |S| < 0x10000000;
    requires |S| == 0 || S[0] < 128;
    requires |S|>0 && S[0] == 0 ==> |S| > 1 && S[1] >= 128;

    requires public(msg);
    requires public(w);
    requires public(sub_bytes_consumed);
    requires public(bytes_consumed);
    requires public(S);

    ensures ModestFatNatValue(V);
    ensures J(V) < power2(power2(34));
    ensures msg[..bytes_consumed] == rfc4251_mpint_encoding_premium(J(V));
    ensures public(J(V));
{
    lemma_2toX32();

    var V_seq,padding := BEByteSeqToWordSeq_impl(S);
    V := SeqToArray(V_seq);

    if (|S|>0 && S[0]==0)
    {
        lemma_LeadingZeros(power2(8), S[1..], S);
        lemma_BEDigitSeqToInt_invertibility_tight(power2(8), J(V), S[1..]);
        assert S == rfc4251_positive_to_twoscomplement(BEIntToByteSeq_premium(J(V)));
    }
    else
    {
        lemma_BEDigitSeqToInt_invertibility_tight(power2(8), J(V), S);
        assert S == rfc4251_positive_to_twoscomplement(BEIntToByteSeq_premium(J(V)));
    }

    //- The nesting of the calc below is for dafnycc's sake

    calc {
        J(V);
        <
        calc {
            J(V);
            BEByteSeqToInt(S);
            <   { lemma_BEByteSeqToInt_bound(S); }
            power2(8*|S|);
            power2(|S|*8);
//-dafnycc        power2(|S|*8);
            <   { lemma_mul_is_mul_boogie(|S|, 8);
                  lemma_mul_strict_inequality(|S|,power2(28),8);
                  lemma_power2_strictly_increases(|S|*8, power2(28)*8); }
            power2(power2(28)*8);
                { lemma_mul_is_commutative(power2(28), 8); }
            power2(8*power2(28));
            power2(power2(3)*power2(28));
                { lemma_power2_adds(3,28); }
            power2(power2(31));
        }
        power2(power2(31));
    }

    calc {
        power2(power2(31));
        <= { lemma_power2_increases(31, 34); lemma_power2_increases(power2(31), power2(34)); }
        power2(power2(34));
    }
}

method {:dafnycc_conservative_seq_triggers} {:timeLimitMultiplier 3} rfc4251_decode_sshrsa_inner(msg:seq<int>) returns (success:bool, E:array<int>, N:array<int>)
    requires IsByteSeq(msg);
    requires Word32(|msg|);
    requires public(msg);
    ensures ModestFatNatValue(E);
    ensures ModestFatNatValue(N);
    ensures J(N) < power2(power2(29));
    ensures J(E) < power2(power2(30));
    ensures J(N) < power2(power2(30));
    ensures J(E) < power2(power2(34));
    ensures J(N) < power2(power2(34));
    ensures success ==> J(N) != 0;
    ensures success ==> (msg == rfc4251_sshrsa_encoding_premium(J(E), J(N)));
    ensures public(success);
    ensures public(J(E));
    ensures public(J(N));
{
    lemma_power2_increases(30, 34);
    lemma_power2_increases(power2(30), power2(34));

    lemma_2toX32();
    var power2_29 := 0x20000000;
    var power2_30 := 0x40000000;
    //-    reveal_rfc4251_sshrsa_encoding();
    assert |STR_SSH_RSA()| < power2(32);

    success := false;
    E := FatNatZero();
    N := FatNatZero();
    lemma_rfc4251_modesty_helper();

    lemma_rfc4251_modesty_suffices_for_encoding(E);
    lemma_rfc4251_modesty_suffices_for_encoding(N);

    var subrc,dec_s,bytes_consumed := rfc4251_decode_string(msg);
    if (!subrc || dec_s != STR_SSH_RSA())
    {
        return;
    }

    var enc_s := msg[..bytes_consumed];
    var msg2 := msg[bytes_consumed..];
    var subrc2,dec_e,bytes_consumed2 := rfc4251_decode_mpint(msg2);
    if (!subrc2)
    {
        return;
    }
//-    lemma_modesty_word_value_equivalence(dec_e);
    assert BEWordSeqToInt_premium(dec_e[..]) == J(dec_e);
    var e_size := FatNatCountBits(dec_e);
    if (e_size >= power2_29)
    {
        return;
    }
    lemma_power2_increases(e_size, power2(30));

    var enc_e := msg2[..bytes_consumed2];
    var msg3 := msg2[bytes_consumed2..];
    var subrc3,dec_n,bytes_consumed3 := rfc4251_decode_mpint(msg3);
    if (!subrc3 || bytes_consumed3!=|msg3|)
    {
        return;
    }
//-    lemma_modesty_word_value_equivalence(dec_n);
    assert BEWordSeqToInt_premium(dec_n[..]) == J(dec_n);
    var n_size := FatNatCountBits(dec_n);
    if (n_size >= power2_29)
    {
        return;
    }
    lemma_power2_increases(n_size, power2(29));
    lemma_power2_increases(n_size, power2(30));

    var enc_n := msg3[..bytes_consumed3];

    E := dec_e;
    N := dec_n;
    assert IsZeroValue(N[..]) == (J(N) == 0);
    var nz := FatNatIsZero(N);
    if (nz)
    {
        return;
    }

    lemma_rfc4251_modesty_suffices_for_encoding(E);
    lemma_rfc4251_modesty_suffices_for_encoding(N);

    calc {
        msg2;
        msg2[..bytes_consumed2] + msg2[bytes_consumed2..];
        enc_e + msg3;
    }
    calc {
        msg;
        enc_s + msg2;
        enc_s + (enc_e + msg3);
        enc_s + (enc_e + enc_n);
            { lemma_seq_concatenation_associative(enc_s, enc_e, enc_n); }
        enc_s + enc_e + enc_n;
    }
    assert IsByteSeq(enc_s);
    assert IsByteSeq(enc_e);
    assert IsByteSeq(enc_n);
    assert IsByteSeq(msg);
    assert enc_s == rfc4251_string_encoding(STR_SSH_RSA());
    assert enc_e == rfc4251_mpint_encoding_premium(J(E));
    assert enc_n == rfc4251_mpint_encoding_premium(J(N));
    assert msg == rfc4251_sshrsa_encoding_premium(J(E), J(N));
    success := true;
}

