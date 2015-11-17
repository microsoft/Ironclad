include "../../BigNum/BigNum.i.dfy"
include "../../Util/seqs_reverse.i.dfy"
include "RSASpec.s.dfy"
include "ByteSequences.i.dfy"
include "../../../Drivers/TPM/tpm-wrapper.i.dfy"
include "../../FatNat/FatNatCommon.i.dfy"
include "../../FatNat/Transforms.i.dfy"

static function method{:CompiledSpec} CompiledSpec_BlockType(pad_mode:PadMode) : int
static function method{:CompiledSpec} CompiledSpec_SignaturePadByte() : int

//-////////////////////////////////////////////////////////////////////////////
//- octet-string to octet-string encoding

method PadMessage(msg:seq<int>, keysize_octets:nat, pad_mode:PadMode)
    returns (padded_msg:seq<int>)
    requires IsByteSeq(msg);
    requires |msg| <= keysize_octets - 11;
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures pad_mode==PadModeSign() ==> TPM == old(TPM);
    ensures pad_mode==PadModeSign() ==> IoMemPerm == old(IoMemPerm);
    ensures TPM_ready();
    ensures IsByteSeq(padded_msg);
    ensures |padded_msg| == keysize_octets;
    ensures PKCS15_PaddingRelation(padded_msg, msg, pad_mode);
    ensures pad_mode==PadModeSign()
        ==> PKCS15_SignaturePad(msg, keysize_octets) == padded_msg;
{
    var ps_len:int := keysize_octets - |msg| - 3;
    assert ps_len>=8;
    var ps := MakePaddingString(ps_len, pad_mode);
    padded_msg := [0, BlockType(pad_mode)] + ps + [0] + msg;
    assert |padded_msg| == keysize_octets;

    var i := ps_len + 3;

    //- PaddedMessageStartIndex conjuncts
    lemma_2toX();
    assert IsByteSeq(padded_msg);
    assert 0 < i <= |padded_msg|;
    assert 2 <= |padded_msg|;
    var padding := ps;
    assert IsByteSeq(padding);
    assert (forall j :: 0 <= j < |padding| ==> padding[j]!=0);
    assert padded_msg[0]==0;
    assert padded_msg[1]==BlockType(pad_mode);
    assert 2<i;
    assert padded_msg[2..i-1] == padding;
    assert padded_msg[i-1]==0;

//-    assert i <= |padded_msg|;
//-    assert 2 <= |padded_msg|;
//-    assert padded_msg[0]==0;
//-    assert padded_msg[1]==BlockType(pad_mode);
//-    assert forall j :: 2 <= j < i-1 ==> padded_msg[j]!=0;
//-    assert padded_msg[i-1]==0;
    assert PaddedMessageStartIndex(padded_msg, i, pad_mode, ps);

    assert i >= 11;
    assert padded_msg[i..] == msg;

    assert PKCS15_PaddingRelationWith(padded_msg, msg, pad_mode, ps);
}

method RandomNonzeroOctet() returns (octet:int)
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_ready();
    ensures IsByte(octet);
    ensures 0!=octet;
{
    lemma_2toX();
    var byte_seq := get_random(1);
    octet := byte_seq[0];
    if (octet==0)
    {
        octet:=42;    // a popular value.
    }
}


static lemma lemma_RepeatDigit_for_ByteSeq(digit:int, count:int)
    decreases count;
    requires 0<=digit<power2(8);
    requires 0<=count;
    ensures |RepeatDigit(digit, count)| == count;
    ensures forall i :: 0<=i<count ==> RepeatDigit(digit, count)[i] == digit;
    ensures IsByteSeq(RepeatDigit(digit, count));
{
    if (count>0)
    {
        lemma_RepeatDigit_for_ByteSeq(digit, count-1);
    }
}

method MakePaddingString(ps_len:nat, pad_mode:PadMode) returns (os:seq<int>)
    requires 8 <= ps_len;    
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures pad_mode==PadModeSign() ==> TPM == old(TPM);
    ensures pad_mode==PadModeSign() ==> IoMemPerm == old(IoMemPerm);
    ensures TPM_ready();
    ensures IsByteSeq(os);
    ensures |os| == ps_len;
    ensures forall octet :: 0 <= octet < |os| ==> os[octet] != 0;
    ensures pad_mode==PadModeSign()
        ==> os == RepeatDigit(SignaturePadByte(), |os|);
{
    os := [];
    while (|os|<ps_len)
        invariant |os| <= ps_len;
        invariant forall octet :: 0 <= octet < |os| ==> IsByte(os[octet]);
        invariant forall octet :: 0 <= octet < |os| ==> os[octet] != 0;
        invariant pad_mode==PadModeSign()
            ==> forall i :: 0<=i<|os| ==> os[i] == SignaturePadByte();
        invariant TPM_ready();
        invariant pad_mode==PadModeSign() ==> TPM == old(TPM);
        invariant pad_mode==PadModeSign() ==> IoMemPerm == old(IoMemPerm);
    {
        var next_octet:int;
        assert pad_mode.PadModeSign? || pad_mode.PadModeEncrypt?;
        if (pad_mode.PadModeSign?)
        {
            next_octet := 0xff;
        }
        else //- if (pad_mode.PadModeEncrypt?)
        {
            next_octet := RandomNonzeroOctet();
        }
/*
        else
        {
            assert false;
        }
*/
        os := os + [next_octet];
    }

    lemma_2toX();
    lemma_RepeatDigit_for_ByteSeq(SignaturePadByte(), |os|);
    if (pad_mode.PadModeSign?)
    {
        ghost var obligation := RepeatDigit(SignaturePadByte(), |os|);
        assert |obligation| == |os|;
        forall (i | 0<=i<|os|)
            ensures obligation[i] == os[i];
        {
            assert obligation[i] == SignaturePadByte() == os[i];
        }
        assert obligation == os;
    }
}

static method UnpadMessage(padded_msg:seq<int>, pad_mode:PadMode) returns (msg:seq<int>)
    requires IsByteSeq(padded_msg);
    requires exists m :: IsByteSeq(m) && PKCS15_PaddingRelation(padded_msg, m, pad_mode);
    ensures IsByteSeq(msg);
    ensures PKCS15_PaddingRelation(padded_msg, msg, pad_mode);
{
    ghost var gm :| IsByteSeq(gm) && PKCS15_PaddingRelation(padded_msg, gm, pad_mode);
    ghost var padding :| PKCS15_PaddingRelationWith(padded_msg, gm, pad_mode, padding);
    ghost var pl := |padding|+3;
    assert pl <= |padded_msg|;

    assert padded_msg[0]==0;
    assert padded_msg[1]==BlockType(pad_mode);

    var pad_idx:int := 2;

    if (2<=pad_idx < pl-1) {
        assert padded_msg[pad_idx] == padding[0];
        assert padded_msg[pad_idx]!=0;
    }

    while (padded_msg[pad_idx]!=0)
        decreases pl - pad_idx;
        invariant forall j::2<=j<pad_idx && j <pl ==> padded_msg[j]!=0;
        invariant 2<=pad_idx < pl;
        invariant 2<=pad_idx < pl-1 ==> padded_msg[pad_idx]!=0;
    {
        pad_idx := pad_idx + 1;
        if (pad_idx >= pl)
        {
            assert padded_msg[pl-1] == 0;
            assert false;    //- violates invariant
        }
        if (2<=pad_idx < pl-1)
        {
            assert padded_msg[pad_idx] == padding[pad_idx-2];
        }
    }
    assert pad_idx == pl-1;

    pad_idx := pad_idx + 1;    //- skip the end-of-pad zero
    msg := padded_msg[pad_idx..];
    assert pad_idx==|padding|+3;
    assert padded_msg[|padding|+3..] == msg;

    assert PKCS15_PaddingRelationWith(padded_msg, msg, pad_mode, padding);
}

static method UnpadMessageOrFail(padded_msg:seq<int>, pad_mode:PadMode) returns (success:bool, msg:seq<int>)
    requires IsByteSeq(padded_msg);
    ensures IsByteSeq(msg);
    ensures (success <==> exists m :: (IsByteSeq(m) && PKCS15_PaddingRelation(padded_msg, m, pad_mode)));
    ensures (success ==> PKCS15_PaddingRelation(padded_msg, msg, pad_mode));
{
    msg := [];

    if (|padded_msg| < 11)
    {
        success := false;
        return;
    }

    //- must start with zero, BlockType
    if (padded_msg[0]!=0)
    {
        success := false;
        return;
    }
    if (padded_msg[1]!=BlockType(pad_mode))
    {
        success := false;
        return;
    }

    var pad_idx:int := 2;
    while (pad_idx < |padded_msg| && padded_msg[pad_idx]!=0)
        invariant pad_idx >= 2;
        invariant forall j::2<=j<pad_idx && j<|padded_msg|==> padded_msg[j]!=0;
    {
        pad_idx := pad_idx + 1;
    }

    if (pad_idx >= |padded_msg|)
    {
        success := false;
        return;

    }

    ghost var padding := padded_msg[2..pad_idx];
    assert padded_msg[pad_idx] == 0;
    pad_idx := pad_idx + 1;    //- skip the end-of-pad zero

    if (pad_idx < 11)
    {
        success := false;
        forall (m:seq<int> | IsByteSeq(m))
            ensures !PKCS15_PaddingRelation(padded_msg, m, pad_mode);
        {
            forall (padding:seq<int>)
                ensures !PKCS15_PaddingRelationWith(padded_msg, m, pad_mode, padding);
            {
                if (PKCS15_PaddingRelationWith(padded_msg, m, pad_mode, padding))
                {
                    assert |padding|>=8;
                    assert padded_msg[2..|padding|+3-1] == padding;
                    if (pad_idx >= 3)
                    {
                        calc {
                            0;
                            padded_msg[pad_idx-1];
                            padded_msg[2..|padding|+3-1][pad_idx-3];
                            padding[pad_idx-3];
                            != 0;
                        }
                        assert false;
                    }
                    else
                    {
                        assert false;
                    }
                }
            }
//-            assert !(exists padding:seq<int> :: PKCS15_PaddingRelationWith(padded_msg, m, pad_mode, padding));
//-            assert !PKCS15_PaddingRelation(padded_msg, m, pad_mode);
        }
//-        assert !exists m :: (IsByteSeq(m) && PKCS15_PaddingRelation(padded_msg, m, pad_mode));
        return;
    }

    success := true;
    msg := padded_msg[pad_idx..];

    assert PKCS15_PaddingRelationWith(padded_msg, msg, pad_mode, padding);
    assert PKCS15_PaddingRelation(padded_msg, msg, pad_mode);
}

//-////////////////////////////////////////////////////////////////////////////
//- encoding an octet string to integers

static function method LEBytesToWord(os:seq<int>) : int
    requires IsByteSeq(os);
    requires |os|==4;
    ensures Word32(LEBytesToWord(os));
{
    lemma_2to32();
    os[0] + 256*os[1] + 65536*os[2] + 16777216*os[3]
}

static lemma lemma_LEBytesToWord(os:seq<int>)
    requires IsByteSeq(os);
    requires |os|==4;
    ensures LittleEndianIntegerValue(os) == LEBytesToWord(os);
{
    calc {
        LittleEndianIntegerValue(os);
        LittleEndianIntegerValue(os[1..])*256 + os[0];
        (LittleEndianIntegerValue(os[1..][1..])*256 + os[1..][0])*256 + os[0];
            {
                assert os[1..][1..] == os[2..];
                assert os[1..][0] == os[1];
            }
        (LittleEndianIntegerValue(os[2..])*256 + os[1])*256 + os[0];
        ((LittleEndianIntegerValue(os[2..][1..])*256 + os[2..][0])*256 + os[1])*256 + os[0];
        ((LittleEndianIntegerValue(os[3..])*256 + os[2])*256 + os[1])*256 + os[0];
        (((LittleEndianIntegerValue(os[3..][1..])*256 + os[3..][0])*256 + os[2])*256 + os[1])*256 + os[0];
        (((LittleEndianIntegerValue(os[4..])*256 + os[3])*256 + os[2])*256 + os[1])*256 + os[0];
        (((LittleEndianIntegerValue([])*256 + os[3])*256 + os[2])*256 + os[1])*256 + os[0];
        (((0*256 + os[3])*256 + os[2])*256 + os[1])*256 + os[0];
        ((os[3]*256 + os[2])*256 + os[1])*256 + os[0];
        (os[3]*256*256 + os[2]*256 + os[1])*256 + os[0];
        os[3]*256*256*256 + os[2]*256*256 + os[1]*256 + os[0];
        LEBytesToWord(os);
    }
}

static lemma lemma_BEByteSeqToWordSeq_preserves_nonzero_prefix_property(bs:seq<int>, ws:seq<int>, padbytes:seq<int>)
    requires IsByteSeq(bs);
    requires IsWordSeq(ws);
    requires |bs|==0 || bs[0] > 0;
    requires |bs|>0 ==> |ws|>0;
    requires |ws| == (|bs|+3)/4;
    requires BEByteSeqToInt(bs) == BEWordSeqToInt(ws);
    requires |BEWordSeqToByteSeq(ws)| >= |bs|;
    requires padbytes == SequenceOfZeros(|ws|*4 - |bs|);
    requires IsByteSeq(padbytes);
    requires BEWordSeqToByteSeq(ws) == padbytes + bs;
    requires (|bs|%4)==0 ==> BEWordSeqToByteSeq(ws) == bs;

    ensures |ws| == 0 || ws[0] != 0;
{
    lemma_2toX();
    if (|bs|==0)
    {
        assert |ws| == 0;
    } else if (ws[0]==0) {
        var prefix := padbytes + bs[..4-|padbytes|];
        assert prefix[|padbytes|] != 0;
        var L4 := 4;
        calc {
            BEIntToDigitSeq(power2(8), 1*4, 0);
                { lemma_BEDigitSeqToInt_of_zeros(power2(32), [0]); }
            BEIntToDigitSeq(power2(8), |[0]|*4, BEDigitSeqToInt(power2(32), [0]));
            BEWordSeqToByteSeq([0]);
            BEWordSeqToByteSeq([ws[0]]);
                { assert [ws[0]] == ws[..1]; }
            BEWordSeqToByteSeq(ws[..1]);
//-            BEIntToDigitSeq(power2(8), |ws[..1]|*4, BEDigitSeqToInt(power2(32), ws[..1]));
            BEIntToDigitSeq(power2(8), |ws[..1]|*4, BEDigitSeqToInt(power2(32), ws[..1]));
                { lemma_mul_is_mul_boogie(|ws[..1]|, 4); }
            BEIntToDigitSeq(power2(8), |ws[..1]|*L4, BEDigitSeqToInt(power2(32), ws[..1]));
                {   lemma_mul_is_mul_boogie(8,4);
                    lemma_mul_is_mul_boogie(1,4);
                    lemma_select_from_transform(ws, ws[..1], ws[1..], 8, 4, 32, 4);
//-                    assert |ws[..1]| == 1;
                    lemma_mul_basics_forall();
//-                    assert |ws[..1]|*L4 == 4;
                    lemma_BEIntToDigitSeq_mp_min(power2(8), |ws|*L4, BEDigitSeqToInt_premium(power2(32), ws));
                    lemma_mul_is_mul_boogie(|ws|, 4);
//-                    assert 4 <= |ws|*L4;
//-                    assert 4 <= |BEIntToDigitSeq(power2(8), |ws|*L4, BEDigitSeqToInt(power2(32), ws))|;
                }
            BEIntToDigitSeq(power2(8), |ws|*L4, BEDigitSeqToInt(power2(32), ws))[..4];
                { lemma_mul_is_mul_boogie(|ws|, 4); }
            BEWordSeqToByteSeq(ws)[..4];
            prefix;
        }
//-        assert prefix == BEIntToDigitSeq(power2(8), 4, 0);
        lemma_BEIntToDigitSeq_of_zero(power2(8), prefix);
//-        assert prefix[|padbytes|] == 0;
        assert false;
    }
}

method BESeqToInteger(be_padded_msg:seq<int>) returns (M:array<int>)
    requires IsByteSeq(be_padded_msg);
//-    requires |be_padded_msg|%4==0;
    requires |be_padded_msg|>0;
//-    requires be_padded_msg[1] != 0;
    ensures WellformedFatNat(M);
    ensures J(M) == BigEndianIntegerValue(be_padded_msg);
    ensures J(M) == BEByteSeqToInt(be_padded_msg);
{
    lemma_2toX();
    var trimmed_be_byte_string := TrimLeadingZeros(256, be_padded_msg);
    assert |trimmed_be_byte_string|==0 || trimmed_be_byte_string[0] != 0;
    
    var big_endian_word_string,padbytes := BEByteSeqToWordSeq_impl(trimmed_be_byte_string);
    lemma_BEByteSeqToWordSeq_preserves_nonzero_prefix_property(trimmed_be_byte_string, big_endian_word_string, padbytes);

    M := SeqToArray(big_endian_word_string);
    calc {
        J(M);
        BEDigitSeqToInt(power2(32), big_endian_word_string);
        BEByteSeqToInt(trimmed_be_byte_string);
        BEByteSeqToInt(be_padded_msg);
            { lemma_BigEndianIntegerValue_equals_BEByteSeqToInt(be_padded_msg); }
        BigEndianIntegerValue(be_padded_msg);
    }
    lemma_BigEndianIntegerValue_equals_BEByteSeqToInt(be_padded_msg);
}

method MessageToInteger(msg:seq<int>, keysize_octets:nat, pad_mode:PadMode) returns (M:array<int>, ghost pm:seq<int>)
    requires IsByteSeq(msg);
//-    requires keysize_octets % 4 == 0;
    requires |msg| <= keysize_octets - 11;
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_ready();
    ensures pad_mode==PadModeSign() ==> TPM == old(TPM);
    ensures pad_mode==PadModeSign() ==> IoMemPerm == old(IoMemPerm);
    ensures WellformedFatNat(M);
    ensures IsByteSeq(pm);
    ensures PKCS15_PaddingRelation(pm, msg, pad_mode);
    ensures pad_mode==PadModeSign()
        ==> PKCS15_SignaturePad(msg, keysize_octets) == pm;
    ensures BigEndianIntegerValue(pm)==J(M);
    ensures BEByteSeqToInt(pm)==J(M);
    ensures 0 < J(M) < power2(8*(keysize_octets-1));
    ensures |pm|==keysize_octets;
    ensures fresh(M);
{
    var be_padded_msg:seq<int> := PadMessage(msg, keysize_octets, pad_mode);
    pm := be_padded_msg;

    var be_bytes := SeqToArray(be_padded_msg);
    M := BEByteArrayToWordArray(be_bytes);

    calc {
        BigEndianIntegerValue(be_padded_msg);
            { lemma_BigEndianIntegerValue_zero_prefix(be_padded_msg, be_padded_msg[1..]); }
        BigEndianIntegerValue(be_padded_msg[1..]);
        <    { lemma_BigEndianIntegerValue_bound(be_padded_msg[1..]); }
        power2(8*|be_padded_msg[1..]|);
        power2(8*(|be_padded_msg|-1));
        power2(8*(keysize_octets-1));
    }

    calc {
        BigEndianIntegerValue(be_padded_msg);
            { lemma_BigEndianIntegerValue_zero_prefix(be_padded_msg, be_padded_msg[1..]); }
        BigEndianIntegerValue(be_padded_msg[1..]);
        >=  { lemma_BigEndianIntegerValue_bound(be_padded_msg[1..]); }
        power2(8*(|be_padded_msg[1..]|-1))*be_padded_msg[1..][0];
            { assert be_padded_msg[1..][0] == BlockType(pad_mode); }
        mul(power2(8*(|be_padded_msg[1..]|-1)),BlockType(pad_mode));
        mul(power2(8*(|be_padded_msg|-2)),BlockType(pad_mode));
            { lemma_mul_is_commutative_forall(); }
        mul(BlockType(pad_mode),power2(8*(|be_padded_msg|-2)));
        >=  {
            assert 1 <= BlockType(pad_mode) <= 2;
            lemma_mul_increases(BlockType(pad_mode),power2(8*(|be_padded_msg|-2)));
            }
        power2(8*(|be_padded_msg|-2));
        power2(8*|be_padded_msg|-16);
        >=  {
                assert 11 <= keysize_octets;
                calc {
                    8*(|be_padded_msg|-2);
                    8*|be_padded_msg| - 16;
                    8*keysize_octets - 16;
                    >=
                    8*11 - 16;
                    88 - 16;
                    72;
                    > 0;
                }
                lemma_power2_increases(0, 8*(|be_padded_msg|-2));
            }
        power2(0);
            { lemma_power2_0_is_1(); }
        1;
        > 0;
    }

    lemma_2toX();
    calc {
        BEByteSeqToInt(pm);
        BEByteSeqToInt(be_bytes[..]);
        BEWordSeqToInt(M[..]);
        J(M);
    }
    lemma_BigEndianIntegerValue_equals_BEByteSeqToInt(pm);
}

static method LEWordToBytes(word:int) returns (os:seq<int>)
    requires Word32(word);
    ensures IsByteSeq(os);
    ensures |os|==4;
    ensures LEBytesToWord(os) == word;
{
    
    var r0 := word % 256;
    var q0 := word / 256;
    var r1 := q0 % 256;
    var q1 := q0 / 256;
    var r2 := q1 % 256;
    var q2 := q1 / 256;
    os := [ r0, r1, r2, q2 ];

    lemma_2to32();

    calc {
        LEBytesToWord(os);
        os[0] + 256*os[1] + 65536*os[2] + 16777216*os[3];
        r0 + 256*r1 + 65536*r2 + 16777216*q2;
        r0 + 256*(r1 + 256*r2 + 65536*q2);
        r0 + 256*(r1 + 256*(r2 + 256*q2));
            {
                lemma_mul_is_mul_boogie(256,q2);
                lemma_mul_is_mul_boogie(256,r2 + 256*q2);
                lemma_mul_is_mul_boogie(256,r1 + 256*(r2 + 256*q2));
            }
        r0 + mul(256,(r1 + mul(256,(r2 + mul(256,q2)))));
            {
                lemma_fundamental_div_mod(q1, 256);
                assert q1 == mul(256, div(q1, 256)) + mod(q1,256);
                assert div(q1,256) == q1/256 == q2;
                assert q1 == mul(256, q2) + r2;
            }
        r0 + mul(256,(r1 + mul(256,q1)));
            {
                lemma_fundamental_div_mod(q0, 256);
                assert q0 == mul(256, div(q0, 256)) + mod(q0,256);
                assert q0 == mul(256, q1) + r1;
            }
        r0 + mul(256,q0);
            {
                lemma_fundamental_div_mod(word, 256);
                assert word == mul(256, div(word, 256)) + mod(word,256);
                assert word == mul(256, q0) + r0;
            }
        word;
    }
}

static lemma lemma_LittleEndianIntegerValue_chomps_word(os:seq<int>)
    requires IsByteSeq(os);
    requires |os|>=4;
    ensures LittleEndianIntegerValue(os)
        == LEBytesToWord(os[0..4]) + Width()*LittleEndianIntegerValue(os[4..]);
{
    calc {
        LittleEndianIntegerValue(os);
        LittleEndianIntegerValue(os[1..])*256 + os[0];
        (LittleEndianIntegerValue(os[1..][1..])*256 + os[1..][0])*256 + os[0];
            {
                assert os[1..][1..] == os[2..];
                assert os[1..][0] == os[1];
            }
        (LittleEndianIntegerValue(os[2..])*256 + os[1])*256 + os[0];
        ((LittleEndianIntegerValue(os[2..][1..])*256 + os[2..][0])*256 + os[1])*256 + os[0];
            {
                assert os[2..][1..] == os[3..];
                assert os[2..][0] == os[2];
            }
        ((LittleEndianIntegerValue(os[3..])*256 + os[2])*256 + os[1])*256 + os[0];
        (((LittleEndianIntegerValue(os[3..][1..])*256 + os[3..][0])*256 + os[2])*256 + os[1])*256 + os[0];
            {
                assert os[3..][1..] == os[4..];
                assert os[3..][0] == os[3];
            }
        (((LittleEndianIntegerValue(os[4..])*256 + os[3])*256 + os[2])*256 + os[1])*256 + os[0];
        ((LittleEndianIntegerValue(os[4..])*256*256 + os[3]*256 + os[2])*256 + os[1])*256 + os[0];
        (LittleEndianIntegerValue(os[4..])*256*256*256 + os[3]*256*256 + os[2]*256 + os[1])*256 + os[0];
        LittleEndianIntegerValue(os[4..])*256*256*256*256 + os[3]*256*256*256 + os[2]*256*256 + os[1]*256 + os[0];
        calc {
            LittleEndianIntegerValue(os[4..])*256*256*256*256;
            { mul_associates256(LittleEndianIntegerValue(os[4..])); }
            LittleEndianIntegerValue(os[4..])*256*256*(256*256);
            { mul_associates256(LittleEndianIntegerValue(os[4..])); }
            LittleEndianIntegerValue(os[4..])*(256*256)*(256*256);
            { lemma_mul_is_associative(LittleEndianIntegerValue(os[4..]), (256*256), (256*256)); }
            LittleEndianIntegerValue(os[4..])*(256*256*256*256);
        }
            {
                lemma_2to32();              
                //-lemma_mul_is_mul_boogie(LittleEndianIntegerValue(os[4..]), Width());
            }
        LittleEndianIntegerValue(os[4..])*Width() + os[3]*256*256*256 + os[2]*256*256 + os[1]*256 + os[0];
        LittleEndianIntegerValue(os[4..])*Width() + os[0] + 256*os[1] + 65536*os[2] + 16777216*os[3];
            { lemma_mul_is_commutative(LittleEndianIntegerValue(os[4..]),Width()); }
        LEBytesToWord(os[0..4]) + Width()*LittleEndianIntegerValue(os[4..]);
    }
}

static lemma mul_associates256(x:int)
    ensures (x*256)*256 == x * (256 * 256);
{
    lemma_mul_is_associative(x, 256, 256);
}

static method WordsToOctets(ws:seq<int>) returns (os:seq<int>)
    requires IsWordSeq(ws);
    ensures IsByteSeq(os);
    ensures LittleEndianIntegerValue(os) == V(ws);
{
    os := [];
    var end_ptr := |ws|;

    calc {
        LittleEndianIntegerValue(os);
        0;
            { reveal_V(); }
        V([]);
            { assert ws[end_ptr..] == []; }
        V(ws[end_ptr..]);
    }

    while (end_ptr > 0)
        invariant 0 <= end_ptr <= |ws|;
        invariant IsByteSeq(os);
        invariant LittleEndianIntegerValue(os) == V(ws[end_ptr..]);
    {
        var word_os := LEWordToBytes(ws[end_ptr-1]);
        ghost var old_os := os;
        os := word_os + os;

        calc {
            LittleEndianIntegerValue(os);
                { lemma_LittleEndianIntegerValue_chomps_word(os); }
            LEBytesToWord(word_os) + Width()*LittleEndianIntegerValue(old_os);
            ws[end_ptr-1] + Width()*V(ws[end_ptr..]);
                { reveal_V(); }
            V([ws[end_ptr-1]] + ws[end_ptr..]);
                { assert [ws[end_ptr-1]] + ws[end_ptr..] == ws[end_ptr-1..]; }
            V(ws[end_ptr-1..]);
        }

        end_ptr := end_ptr - 1;
    }
    assert ws==ws[0..];
}

predicate {:heap} CanDecodeFatInteger(M:array<int>, keysize_octets:nat, pad_mode:PadMode)
    requires WellformedFatNat(M);
    reads M;
{
    exists pm:seq<int>, m:seq<int> ::
        IsByteSeq(pm)
        && IsByteSeq(m)
        && PKCS15_PaddingRelation(pm, m, pad_mode)
        && BigEndianIntegerValue(pm)==J(M)
        && |pm|==keysize_octets
}

static predicate CanDecodeInteger(M:BigNat, keysize_octets:nat, pad_mode:PadMode)
    requires WellformedBigNat(M);
{
    exists pm:seq<int>, m:seq<int> ::
        IsByteSeq(pm)
        && IsByteSeq(m)
        && PKCS15_PaddingRelation(pm, m, pad_mode)
        && BigEndianIntegerValue(pm)==I(M)
        && |pm|==keysize_octets
}

method IntegerToBESeq(M:array<int>) returns (be_padded_msg:seq<int>)
    requires WellformedFatNat(M);
    ensures IsByteSeq(be_padded_msg);
    ensures |be_padded_msg| > 0;
    ensures be_padded_msg[0] == 0;
    ensures (|be_padded_msg| > 1) ==> be_padded_msg[1] != 0;
    ensures J(M) == BigEndianIntegerValue(be_padded_msg);
    ensures |be_padded_msg| > 2 ==> power2(8*(|be_padded_msg|-2)) <= BigEndianIntegerValue(be_padded_msg);
    ensures [0] + BEIntToByteSeq(J(M)) == be_padded_msg;
{
    var wordy_be_padded_msg := BEWordArrayToByteArray(M);

    lemma_2toX();
    var stripped_be_padded_msg := StripLeadingZeros(256, wordy_be_padded_msg[..]);
        //- now no zeros.

    be_padded_msg := [0] + stripped_be_padded_msg;
        

    assert |stripped_be_padded_msg|>0 ==> stripped_be_padded_msg[0]!=0;
    assert |be_padded_msg|>1 ==> be_padded_msg[1]!=0;

    calc {
        BigEndianIntegerValue(be_padded_msg);
            { lemma_BigEndianIntegerValue_zero_prefix(be_padded_msg, stripped_be_padded_msg); }
        BigEndianIntegerValue(stripped_be_padded_msg);
            { lemma_BigEndianIntegerValue_zero_prefix(wordy_be_padded_msg[..], stripped_be_padded_msg); }
        BigEndianIntegerValue(wordy_be_padded_msg[..]);
            { lemma_BigEndianIntegerValue_equals_BEByteSeqToInt(wordy_be_padded_msg[..]); }
        BEByteSeqToInt(wordy_be_padded_msg[..]);
        J(M);
    }

    lemma_2toX();
    if (|be_padded_msg| == 0)
    {
        assert false;
    }
    if (|be_padded_msg| <= 2)
    {
        lemma_BigEndianIntegerValue_equals_BEByteSeqToInt(be_padded_msg);
    }
    else
    {
        assert |stripped_be_padded_msg| > 0;
        calc {
            power2(8*(|be_padded_msg|-2));
            power2(8*(|stripped_be_padded_msg|-1));
            power2(8*(|stripped_be_padded_msg|-1))*1;
                { lemma_mul_is_mul_boogie(power2(8*(|stripped_be_padded_msg|-1)),1); }
            mul(power2(8*(|stripped_be_padded_msg|-1)),1);
            <=  { lemma_mul_left_inequality(power2(8*(|stripped_be_padded_msg|-1)), 1, stripped_be_padded_msg[0]); }
            power2(8*(|stripped_be_padded_msg|-1))*stripped_be_padded_msg[0];
            <=  { lemma_BigEndianIntegerValue_bound(stripped_be_padded_msg); }
            BigEndianIntegerValue(stripped_be_padded_msg);
                { lemma_BigEndianIntegerValue_zero_prefix(be_padded_msg, stripped_be_padded_msg); }
            BigEndianIntegerValue(be_padded_msg);
        }
        lemma_BigEndianIntegerValue_equals_BEByteSeqToInt(be_padded_msg);
    }
    assert J(M) == BigEndianIntegerValue(be_padded_msg) == BEByteSeqToInt(be_padded_msg);

    ghost var beseq := BEIntToByteSeq(J(M));
    lemma_BEIntToByteSeq_decoding(J(M));
    assert IsByteSeq(beseq);

    calc {
        BigEndianIntegerValue(beseq);
            { lemma_BigEndianIntegerValue_equals_BEByteSeqToInt(beseq); }
        BEByteSeqToInt(beseq);
            { lemma_BEIntToByteSeq_decoding(J(M)); }
        J(M);
    }

    assert BigEndianIntegerValue(beseq) == J(M);

    assert BigEndianIntegerValue(beseq) == BigEndianIntegerValue(be_padded_msg);

    lemma_BEIntToByteSeq_form(J(M));
    assert |beseq|==0 || beseq[0] != 0;
    ghost var zbeseq := [0]+beseq;
    lemma_BigEndianIntegerValue_zero_prefix(zbeseq, beseq);
    assert BigEndianIntegerValue(zbeseq) == BigEndianIntegerValue(be_padded_msg);

//-    lemma_BigEndianIntegerValue_zero_prefix_converse_inner(s0:seq<int>, s1:seq<int>)
//-    requires IsByteSeq(s0);
//-    requires IsByteSeq(s1);
//-    requires |s0| >= |s1|;
//-    requires BigEndianIntegerValue(s0) == BigEndianIntegerValue(s1);
//-    ensures ZeroPrefix(s0, s1);

    assert IsByteSeq(zbeseq);
    assert |zbeseq| > 0;
    assert zbeseq[0] == 0;
    assert  |zbeseq|>1 ==> zbeseq[1] != 0;
    assert BigEndianIntegerValue(be_padded_msg) == BigEndianIntegerValue(zbeseq);
    lemma_SingleZeroPrefixedBigEndianIntegerValuesEqual(zbeseq, be_padded_msg);
    assert [0] + BEIntToByteSeq(J(M)) == zbeseq == be_padded_msg;
}

method IntegerToMessage(M:array<int>, keysize_octets:nat, pad_mode:PadMode) returns (success:bool, msg:seq<int>, ghost be_padded_msg:seq<int>)
    requires WellformedFatNat(M);
    ensures IsByteSeq(msg);
    ensures success <==> CanDecodeFatInteger(M, keysize_octets, pad_mode);
    ensures success ==>
        IsByteSeq(be_padded_msg)
        && PKCS15_PaddingRelation(be_padded_msg, msg, pad_mode)
        && BigEndianIntegerValue(be_padded_msg)==J(M)
        && |be_padded_msg| == keysize_octets;
{
    var be_padded_msg_real := IntegerToBESeq(M);
    be_padded_msg := be_padded_msg_real;

    if (|be_padded_msg_real| != keysize_octets)
    {
        success := false;
        msg := [];
        forall (pm:seq<int>, m:seq<int> |
            IsByteSeq(pm)
            && IsByteSeq(m)
            && PKCS15_PaddingRelation(pm, m, pad_mode)
            && BigEndianIntegerValue(pm)==J(M)
            && |pm|==keysize_octets)
            ensures false;
        {
            calc {
                keysize_octets;
                |pm|;
                {
                    calc {
                        BigEndianIntegerValue(be_padded_msg_real);
                        J(M);
                        BigEndianIntegerValue(pm);
                    }
                    lemma_SingleZeroPrefixedBigEndianIntegerValuesEqual(pm, be_padded_msg_real);
                }
                |be_padded_msg_real|;
                != keysize_octets;
            }
        }
        assert !CanDecodeFatInteger(M, keysize_octets, pad_mode);
    }
    else
    {
        success,msg := UnpadMessageOrFail(be_padded_msg_real, pad_mode);

        if (!success)
        {
            forall pm:seq<int>, m:seq<int>
                ensures !(IsByteSeq(pm)
                    && IsByteSeq(m)
                    && PKCS15_PaddingRelation(pm, m, pad_mode)
                    && BigEndianIntegerValue(pm)==J(M));
            {
                if (IsByteSeq(pm)
                    && IsByteSeq(m)
                    && BigEndianIntegerValue(pm)==J(M))
                {
                    lemma_BigEndianIntegerValue_zero_prefix_converse(pm, be_padded_msg);
                    if (pm == be_padded_msg)
                    {
                        assert !(exists m :: (IsByteSeq(m) && PKCS15_PaddingRelation(be_padded_msg, m, pad_mode)));
                        assert !PKCS15_PaddingRelation(pm, m, pad_mode);
                    }
                    else if (ZeroPrefix(pm, be_padded_msg))
                    {
                        assert |pm| >= |be_padded_msg|;
                        assert |pm| > |be_padded_msg|;
                        if (1 < |pm|-|be_padded_msg|)
                        {
                            assert pm[1]==0;
                        }
                        else if (1 == |pm|-|be_padded_msg|)
                        {
                            calc {
                                pm[1];
                                pm[ 1 .. ][0];
                                be_padded_msg[0];
                                0;
                            }
                        }
                        else
                        {
                            assert 0 == |pm|-|be_padded_msg|;
                            assert pm == be_padded_msg;
                            assert false;
                        }
                        assert !PKCS15_PaddingRelation(pm, m, pad_mode);
                    }
                    else
                    {
                        assert ZeroPrefix(be_padded_msg, pm);
                        if (0 == |be_padded_msg|-|pm|)
                        {
                            assert pm == be_padded_msg;
                            assert false;
                        }
                        else if (1 < |be_padded_msg|-|pm|)
                        {
                            assert be_padded_msg[1] == 0;
                            assert false;
                        }
                        else if (|pm| < 1)
                        {
                            assert !PKCS15_PaddingRelation(pm, m, pad_mode);
                        }
                        else if (|be_padded_msg| < 2)
                        {
                            assert |pm| <= |be_padded_msg|;
                            assert !PKCS15_PaddingRelation(pm, m, pad_mode);
                        }
                        else
                        {
                            assert 1 == |be_padded_msg|-|pm|;
                            calc {
                                be_padded_msg[1];
                                be_padded_msg[ 1.. ][0];
                                pm[0];
                            }
                            assert pm[0]!=0;
                            assert !PKCS15_PaddingRelation(pm, m, pad_mode);
                        }
                    }
                }
            }
        }
        else
        {
            assert IsByteSeq(be_padded_msg);
            assert PKCS15_PaddingRelation(be_padded_msg, msg, pad_mode);
        }
    }
}

static method BEWordToBytes(word:int) returns (os:seq<int>)
    requires Word32(word);
    ensures IsByteSeq(os);
    ensures |os|==4;
    ensures BigEndianIntegerValue(os) == word;
{
    var leseq := LEWordToBytes(word);
    os := ReverseOctetString(leseq);

    calc {
        BigEndianIntegerValue(os);
            { lemma_endian_reversal(os); }
        LittleEndianIntegerValue(Reverse(os));
            { lemma_Reverse_symmetry(os, leseq); }
        LittleEndianIntegerValue(leseq);
            { lemma_LEBytesToWord(leseq); }
        LEBytesToWord(leseq);
        word;
    }
}

