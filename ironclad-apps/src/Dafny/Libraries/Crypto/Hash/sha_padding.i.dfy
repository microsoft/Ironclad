include "sha_common.s.dfy"
include "sha_common.i.dfy"
include "../../Util/arrays_and_seqs.i.dfy"
include "../../Util/integer_sequences_premium.i.dfy"

static function {:opaque} Mul32_const(i:int):int { i * 32 }
static function {:opaque} Div32_const(i:int):int { i / 32 }
static function {:opaque} Mod32_const(i:int):int { i % 32 }
static lemma lemma_Mul32_const(i:int) ensures Mul32_const(i) == i * 32; { reveal_Mul32_const(); }
static lemma lemma_Div32_const(i:int) ensures Div32_const(i) == i / 32; { reveal_Div32_const(); }
static lemma lemma_Mod32_const(i:int) ensures Mod32_const(i) == i % 32; { reveal_Mod32_const(); }

//-///////////////////////////////////////////////////
//- Padding message
//-///////////////////////////////////////////////////

static function method {:opaque} PaddedLength(message_len: int) : int
{
    message_len + 1 + NumPaddingZeroes(message_len) + 64
}

static lemma lemma_PaddedLength_properties(message_len: int)
    ensures PaddedLength(message_len) == message_len + 65 + NumPaddingZeroes(message_len);
    ensures PaddedLength(message_len) == message_len + 65 + (959 - (message_len%512)) % 512;
    ensures PaddedLength(message_len) % 512 == 0;
{
    reveal_PaddedLength();
    reveal_NumPaddingZeroes();

    var padded_length := PaddedLength(message_len);
    var padding_zeroes := NumPaddingZeroes(message_len);

    var q := message_len/512;
    var r := message_len%512;
    calc {
        padded_length % 512;
        (message_len + 1 + padding_zeroes + 64) % 512;
        (message_len + 65 + padding_zeroes) % 512;
        { reveal_NumPaddingZeroes(); }
        (message_len + 65 + (959 - (message_len % 512)) % 512) % 512;
        (message_len + 65 + (959 - r) % 512) % 512;
        (q * 512 + r + 65 + (959 - r) % 512) % 512;
        (r + 65 + (959 - r) % 512) % 512;
        1024 % 512;
        0;
    }
}

static lemma{:dafnycc_conservative_seq_triggers} lemma_PadMessageForSHA_properties(m:seq<int>)
    requires IsBitSeq(m);
    requires |m| < power2(64);
    ensures IsBitSeq(PadMessageForSHA(m));
    ensures |PadMessageForSHA(m)| == PaddedLength(|m|);
    ensures |PadMessageForSHA(m)| == |m| + 1 + NumPaddingZeroes(|m|) + 64;
    ensures |PadMessageForSHA(m)| % 512 == 0;
    ensures forall i :: 0 <= i < |m| ==> PadMessageForSHA(m)[i] == m[i];
    ensures PadMessageForSHA(m)[|m|] == 1;
    ensures forall i :: |m| + 1 <= i <= |m| + NumPaddingZeroes(|m|) ==> PadMessageForSHA(m)[i] == 0;
    ensures PadMessageForSHA(m)[|m|+NumPaddingZeroes(|m|)+1..] == BEIntToDigitSeq(2, 64, |m|);
    ensures PadMessageForSHA(m) == PadMessageForSHA(m);
    ensures IsBitSeq(PadMessageForSHA(m));
{
    lemma_PaddedLength_properties(|m|);

    reveal_power2();
    assert 2 == power2(1);

    var paddedBits := PadMessageForSHA(m);
    var paddingZeroes := NumPaddingZeroes(|m|);
    Lemma_RepeatDigitProperties(0, paddingZeroes);

    calc {
        |PadMessageForSHA(m)|;
        |m + [1] + RepeatDigit(0, paddingZeroes) + BEIntToDigitSeq(2, 64, |m|)|;
        |m| + 1 + paddingZeroes + |BEIntToDigitSeq(2, 64, |m|)|;
        { lemma_power2_is_power_2(64); lemma_BEIntToDigitSeq_private_properties(2, 64, |m|); }
        |m| + 1 + paddingZeroes + 64;
    }

    forall i | 0 <= i < |paddedBits|
        ensures IsBit(paddedBits[i]);
        ensures 0 <= i < |m| ==> PadMessageForSHA(m)[i] == m[i];
        ensures |m| + 1 <= i <= |m| + NumPaddingZeroes(|m|) ==> PadMessageForSHA(m)[i] == 0;
    {
        if 0 <= i < |m| {
            assert paddedBits[i] == m[i];
        }
        else if i == |m| {
            assert paddedBits[i] == 1;
        }
        else if |m|+1 <= i <= |m| + paddingZeroes {
            calc {
                paddedBits[i];
                (m + [1] + RepeatDigit_premium(0, paddingZeroes) + BEIntToDigitSeq(2, 64, |m|))[i];
                ([1] + RepeatDigit_premium(0, paddingZeroes) + BEIntToDigitSeq(2, 64, |m|))[i - |m|];
                (RepeatDigit_premium(0, paddingZeroes) + BEIntToDigitSeq(2, 64, |m|))[i - |m| - 1];
                0;
            }
        }
        else {
            calc {
                i;
                < |paddedBits|;
                == |m + [1] + RepeatDigit_premium(0, paddingZeroes) + BEIntToDigitSeq(2, 64, |m|)|;
                == |m| + 1 + paddingZeroes + |BEIntToDigitSeq(2, 64, |m|)|;
            }
            calc {
                paddedBits[i];
                (m + [1] + RepeatDigit_premium(0, paddingZeroes) + BEIntToDigitSeq(2, 64, |m|))[i];
                ([1] + RepeatDigit_premium(0, paddingZeroes) + BEIntToDigitSeq(2, 64, |m|))[i - |m|];
                (RepeatDigit_premium(0, paddingZeroes) + BEIntToDigitSeq(2, 64, |m|))[i - |m| - 1];
                BEIntToDigitSeq(2, 64, |m|)[i - |m| - 1 - paddingZeroes];
            }
            lemma_BEIntToDigitSeq_produces_DigitSeq(2, 64, |m|);
            assert 0 <= BEIntToDigitSeq(2, 64, |m|)[i - |m| - 1 - paddingZeroes] < 2;
            assert 0 <= paddedBits[i] < 2;
        }
    }
}

static function PadMessageForSHA_premium(m:seq<int>) : seq<int>
    requires IsBitSeq(m);
    requires |m| < power2(64);
    ensures IsBitSeq(PadMessageForSHA_premium(m));
    ensures |PadMessageForSHA_premium(m)| == PaddedLength(|m|);
    ensures |PadMessageForSHA_premium(m)| == |m| + 1 + NumPaddingZeroes(|m|) + 64;
    ensures |PadMessageForSHA_premium(m)| % 512 == 0;
    ensures |m| < power2(64) ==> |PadMessageForSHA_premium(m)| == |m| + 1 + NumPaddingZeroes(|m|) + 64;
    ensures forall i :: 0 <= i < |m| ==> PadMessageForSHA_premium(m)[i] == m[i];
    ensures PadMessageForSHA_premium(m)[|m|] == 1;
    ensures forall i :: |m| + 1 <= i <= |m| + NumPaddingZeroes(|m|) ==> PadMessageForSHA_premium(m)[i] == 0;
    ensures PadMessageForSHA_premium(m)[|m|+NumPaddingZeroes(|m|)+1..] == BEIntToDigitSeq(2, 64, |m|);
    ensures PadMessageForSHA_premium(m) == PadMessageForSHA(m);
{
    lemma_PadMessageForSHA_properties(m);
    lemma_PaddedLength_properties(|m|);
    PadMessageForSHA(m)
}

static lemma {:timeLimitMultiplier 2} lemma_ExtractingWordFromArray(n1:int, n2:int, a:array<int>, b:int, s:seq<int>)
    requires Mod32_const(n1) == 0;
    requires n1 + 32 == n2;
    requires 0 <= n1 < n2 <= |s|;
    requires IsWordArray(a);
    requires n2 <= a.Length * 32;
    requires forall i :: n1 <= i < n2 ==> s[i] == GetArrayBit(a, i);
    requires a[n1 / 32] == b;
    ensures s[n1..n2] == BEWordToBitSeq(b);
{
    reveal_Mod32_const();
    reveal_GetArrayBit();
    assert IsBitSeq(BEWordToBitSeq_premium(b));
    assert |BEWordToBitSeq(b)| == 32;
    assert forall i :: n1 <= i < n2 ==> s[i] == BEWordToBitSeq_premium(b)[i - n1];
}

static lemma lemma_PaddedMessageLen(message_len: int)
    ensures Mod32_const(message_len + NumPaddingZeroes(message_len)) == 31;
{
    reveal_Mod32_const();
    reveal_NumPaddingZeroes();
}

static lemma lemma_mod32_fact(x:int)
    requires Mod32_const(x) == 31;
    ensures  Mod32_const(x + 1) == 0;
    ensures  Mod32_const(x + 33) == 0;
{
    reveal_Mod32_const();
}

static lemma lemma_LengthInPaddedMessageIsWordAligned(message_len: int)
    ensures Mod32_const(message_len + NumPaddingZeroes(message_len) + 1) == 0;
    ensures Mod32_const(message_len + NumPaddingZeroes(message_len) + 33) == 0;
{
    lemma_PaddedMessageLen(message_len);
    var x := message_len + NumPaddingZeroes(message_len);
    lemma_mod32_fact(x);
}

static lemma lemma_WhatHappensToMod512WhenYouAddOne(x:int)
    requires 0 <= x;
    ensures (x+1)%512 == x%512+1 || (x+1)%512 == x%512 - 511;
{
}

static lemma lemma_WhatHappensToPaddedLengthWhenYouAddOne(x:int)
    requires 0 <= x;
    ensures PaddedLength(x+1) == PaddedLength(x) || PaddedLength(x+1) == PaddedLength(x)+512;
{
    lemma_WhatHappensToMod512WhenYouAddOne(x);
    lemma_WhatHappensToMod512WhenYouAddOne(958 - x%512);
    if (x+1)%512 == x%512+1 {
        if (958 - x%512 + 1)%512 == (958 - x%512)%512 + 1 {
            calc {
                PaddedLength(x+1);
                { reveal_PaddedLength(); }
                x + 66 + NumPaddingZeroes(x+1);
                { reveal_NumPaddingZeroes(); }
                x + 66 + (959 - ((x+1)%512))%512;
                x + 66 + (959 - (x%512+1))%512;
                x + 66 + (958 - x%512)%512;
                x + 66 + (958 - x%512 + 1)%512 - 1;
                x + 65 + (959 - x%512)%512;
                { reveal_NumPaddingZeroes(); }
                x + 65 + NumPaddingZeroes(x);
                { reveal_PaddedLength(); }
                PaddedLength(x);
            }
        }
        else {
            assert (958 - x%512 + 1)%512 == (958 - x%512)%512 - 511;
            calc {
                PaddedLength(x+1);
                { reveal_PaddedLength(); }
                x + 66 + NumPaddingZeroes(x+1);
                { reveal_NumPaddingZeroes(); }
                x + 66 + (959 - ((x+1)%512))%512;
                x + 66 + (959 - (x%512+1))%512;
                x + 66 + (958 - x%512)%512;
                x + 66 + (958 - x%512 + 1)%512 + 511;
                x + 65 + (959 - x%512)%512 + 512;
                { reveal_NumPaddingZeroes(); }
                x + 65 + NumPaddingZeroes(x) + 512;
                { reveal_PaddedLength(); }
                PaddedLength(x) + 512;
            }
        }
    }
    else {
        assert (x+1)%512 == x%512-511;
        if (958 - x%512 + 1)%512 == (958 - x%512)%512 + 1 {
            calc {
                PaddedLength(x+1);
                { reveal_PaddedLength(); }
                x + 66 + NumPaddingZeroes(x+1);
                { reveal_NumPaddingZeroes(); }
                x + 66 + (959 - ((x+1)%512))%512;
                x + 66 + (959 - (x%512-511))%512;
                x + 66 + (959 + 511 - x%512)%512;
                x + 66 + (958 - x%512)%512;
                x + 66 + (958 - x%512 + 1)%512 - 1;
                x + 65 + (959 - x%512)%512;
                { reveal_NumPaddingZeroes(); }
                x + 65 + NumPaddingZeroes(x);
                { reveal_PaddedLength(); }
                PaddedLength(x);
            }
        }
        else {
            assert (958 - x%512 + 1)%512 == (958 - x%512)%512 - 511;
            calc {
                PaddedLength(x+1);
                { reveal_PaddedLength(); }
                x + 66 + NumPaddingZeroes(x+1);
                { reveal_NumPaddingZeroes(); }
                x + 66 + (959 - ((x+1)%512))%512;
                x + 66 + (959 - (x%512-511))%512;
                x + 66 + (959 + 511 - x%512)%512;
                x + 66 + (958 - x%512)%512;
                x + 66 + (958 - x%512 + 1)%512 + 511;
                x + 65 + (959 - x%512)%512 + 512;
                { reveal_NumPaddingZeroes(); }
                x + 65 + NumPaddingZeroes(x) + 512;
                { reveal_PaddedLength(); }
                PaddedLength(x) + 512;
            }
        }
    }
}

static lemma lemma_PaddedLengthMonotonic(a:int, b:int)
    requires 0 <= a <= b;
    decreases b;
    ensures PaddedLength(a) <= PaddedLength(b);
{
    if a < b {
        lemma_PaddedLengthMonotonic(a, b-1);
        lemma_WhatHappensToPaddedLengthWhenYouAddOne(b-1);
    }
}

static lemma lemma_64BitValueIsZerosThen32Bits(v: int)
    requires Word32(v);
    ensures BEIntToDigitSeq(2, 64, v) == SequenceOfZeros(32) + BEWordToBitSeq(v);
{
    lemma_power2_is_power_2_general();
    lemma_BEIntToDigitSeqProducesRightSizedDigits(2, 32, v);
    calc {
        BEDigitSeqToInt(2, SequenceOfZeros(32) + BEIntToDigitSeq(2, 32, v));
        { lemma_LeadingZeros(2, BEIntToDigitSeq(2, 32, v), SequenceOfZeros(32) + BEIntToDigitSeq(2, 32, v)); }
        BEDigitSeqToInt(2, BEIntToDigitSeq(2, 32, v));
    }
    calc {
        BEDigitSeqToInt(2, SequenceOfZeros(32) + BEIntToDigitSeq(2, 32, v));
        { lemma_BEIntToDigitSeq_private_properties(2, 32, v);
          lemma_BEIntToDigitSeq_invertibility(2, v, BEIntToDigitSeq(2, 32, v)); }
        v;
    }
    calc {
        BEIntToDigitSeq(2, 64, v);
        { lemma_BEDigitSeqToInt_invertibility(2, v, SequenceOfZeros(32) + BEIntToDigitSeq(2, 32, v));
          lemma_BEIntToDigitSeq_private_properties(2, 32, v); }
        SequenceOfZeros(32) + BEIntToDigitSeq(2, 32, v);
        { lemma_power2_1_is_2(); }
        SequenceOfZeros(32) + BEWordToBitSeq(v);
    }
}

static function {:opaque} GetArrayBitOpaque(a: array<int>, b:int) : int
    requires IsWordArray(a);
    requires 0 <= b < Mul32_const(a.Length);
    ensures IsBit(GetArrayBitOpaque(a, b));
    ensures b < |BEWordSeqToBitSeq_premium(a[..])|;
    ensures /*REVIEW: GetArrayBitOpaque*/ GetArrayBit(a, b) == BEWordSeqToBitSeq_premium(a[..])[b];
    reads a;
{
    reveal_Mul32_const();
    GetArrayBit(a, b)
}

ghost static method {:dafnycc_conservative_seq_triggers} {:timeLimitMultiplier 6} Lemma_ArrayIsPaddedMessageHelper(a: array<int>, b: int, m: seq<int>)
    requires IsWordArray(a);
    requires |m| == b;
    requires Word32(b);
    requires 0 <= b < power2(64);
    requires b + 1 + NumPaddingZeroes(b) + 64 <= Mul32_const(a.Length);
    requires 0 <= PaddedLength(b) <= Mul32_const(a.Length);
    requires forall i {:trigger GetArrayBit(a, i)}{:trigger m[i]} :: 0 <= i < b ==> GetArrayBitOpaque(a, i) == m[i];
    requires GetArrayBitOpaque(a, b) == 1;
    requires a.Length > Div32_const(b + NumPaddingZeroes(b) + 33);
    requires 0 <= Div32_const(b + NumPaddingZeroes(b) + 1) < a.Length;
    requires 0 <= Div32_const(b + NumPaddingZeroes(b) + 33) < a.Length;
    requires forall i {:trigger GetArrayBit(a, i)} :: b + 1 <= i <= b + NumPaddingZeroes(b) ==> GetArrayBitOpaque(a, i) == 0;
    requires a[Div32_const(b + NumPaddingZeroes(b) + 1)] == 0;
    requires a[Div32_const(b + NumPaddingZeroes(b) + 33)] == b;
    ensures PaddedLength(b) <= |BEWordSeqToBitSeq(a[..])|;
    ensures BEWordSeqToBitSeq(a[..])[..PaddedLength(b)] == PadMessageForSHA(m);
{
    ghost var s := BEWordSeqToBitSeq_premium(a[..]);
    assert forall j :: 0 <= j < a.Length ==> s[j] == GetArrayBit(a, j);

    calc <= { PaddedLength(b); { reveal_Mul32_const(); } |s|; }
    calc {
        s[..PaddedLength(b)];
        { reveal_PaddedLength(); }
        s[0..|m|+NumPaddingZeroes(|m|)+65];
        { lemma_LengthInPaddedMessageIsWordAligned(|m|);
          reveal_Mul32_const();
          lemma_subseq_concatenation(s, 0, |m|+NumPaddingZeroes(|m|)+33, |m|+NumPaddingZeroes(|m|)+65); }
        s[0..|m|+NumPaddingZeroes(|m|)+33] + s[|m|+NumPaddingZeroes(|m|)+33..|m|+NumPaddingZeroes(|m|)+65];
        { reveal_Mul32_const(); reveal_Div32_const(); }
        { lemma_LengthInPaddedMessageIsWordAligned(|m|); }
        { lemma_ExtractingWordFromArray(b+NumPaddingZeroes(b)+33, b+NumPaddingZeroes(b)+65, a, b, s); }
        s[0..|m|+NumPaddingZeroes(|m|)+33] + BEWordToBitSeq(b);
        { reveal_Mul32_const(); }
        { lemma_subseq_concatenation(s, 0, |m|+NumPaddingZeroes(|m|)+1, |m|+NumPaddingZeroes(|m|)+33); }
        s[0..|m|+NumPaddingZeroes(|m|)+1] + s[|m|+NumPaddingZeroes(|m|)+1..|m|+NumPaddingZeroes(|m|)+33] + BEWordToBitSeq(b);
        { reveal_Div32_const(); }
        { lemma_LengthInPaddedMessageIsWordAligned(|m|); }
        { lemma_ExtractingWordFromArray(b+NumPaddingZeroes(b)+1, b+NumPaddingZeroes(b)+33, a, 0, s); }
        s[0..|m|+NumPaddingZeroes(|m|)+1] + BEWordToBitSeq(0) + BEWordToBitSeq(b);
        { reveal_power2(); lemma_BEIntToDigitSeq_private_zero(power2(1), 32); }
        s[0..|m|+NumPaddingZeroes(|m|)+1] + SequenceOfZeros(32) + BEWordToBitSeq(b);
        { lemma_64BitValueIsZerosThen32Bits(b); }
        s[0..|m|+NumPaddingZeroes(|m|)+1] + BEIntToDigitSeq(2, 64, b);
        { lemma_subseq_concatenation(s, 0, |m|+1, |m|+NumPaddingZeroes(|m|)+1); }
        s[0..|m|+1] + s[|m|+1..|m|+NumPaddingZeroes(|m|)+1] + BEIntToDigitSeq(2, 64, b);
        { assert forall j :: |m|+1 <= j < |m|+NumPaddingZeroes(|m|)+1 ==> s[j] == GetArrayBit(a, j); reveal_GetArrayBitOpaque(); }
        s[0..|m|+1] + SequenceOfZeros(NumPaddingZeroes(|m|)) + BEIntToDigitSeq(2, 64, b);
        { lemma_subseq_concatenation(s, 0, |m|, |m|+1); }
        s[0..|m|] + s[|m|..|m|+1] + SequenceOfZeros(NumPaddingZeroes(|m|)) + BEIntToDigitSeq(2, 64, b);
        { reveal_GetArrayBitOpaque(); assert s[|m|] == 1; assert s[|m|..|m|+1] == [1]; }
        s[0..|m|] + [1] + SequenceOfZeros(NumPaddingZeroes(|m|)) + BEIntToDigitSeq(2, 64, b);
        { reveal_GetArrayBitOpaque();
          assert forall i {:trigger GetArrayBit(a, i)}{:trigger m[i]} :: 0 <= i < b ==> GetArrayBit(a, i) == m[i];
          lemma_seq_equality(s[0..|m|], m, b); }
        m + [1] + SequenceOfZeros(NumPaddingZeroes(|m|)) + BEIntToDigitSeq(2, 64, b);
        { lemma_SequenceOfZerosIsRepeatDigitZero(NumPaddingZeroes(|m|));
          assert |m| == b; }
        PadMessageForSHA(m);
     }
}

ghost static method Lemma_ArrayIsPaddedMessage(a: array<int>, b: int, m: seq<int>)
    requires IsWordArray(a);
    requires |m| == b;
    requires Word32(b);
    requires 0 <= b < power2(64);
    requires b + 1 + NumPaddingZeroes(b) + 64 <= a.Length * 32;
    requires 0 <= PaddedLength(b) <= a.Length * 32;
    requires forall i {:trigger GetArrayBit(a, i)}{:trigger m[i]} :: 0 <= i < b ==> GetArrayBit(a, i) == m[i];
    requires GetArrayBit(a, b) == 1;
    requires a.Length > (b + NumPaddingZeroes(b) + 33) / 32;
    requires forall i {:trigger GetArrayBit(a, i)} :: b + 1 <= i <= b + NumPaddingZeroes(b) ==> GetArrayBit(a, i) == 0;
    requires a[(b + NumPaddingZeroes(b) + 1) / 32] == 0;
    requires a[(b + NumPaddingZeroes(b) + 33) / 32] == b;
    ensures BEWordSeqToBitSeq(a[..])[..PaddedLength(b)] == PadMessageForSHA(m);
{
    reveal_Mul32_const();
    reveal_Div32_const();
    reveal_GetArrayBitOpaque();
    Lemma_ArrayIsPaddedMessageHelper(a, b, m);
}

static method {:dafnycc_conservative_seq_triggers} PadMessageArray(a: array<int>, b: int)
    requires IsWordArray(a);
    requires Word32(b);
    requires 0 <= b < power2(64);
    requires 0 <= PaddedLength(b) <= a.Length * 32;
    ensures IsWordSeq(a[..]);
    ensures |BEWordSeqToBitSeq(a[..])| >= PaddedLength(b);
    ensures |old(BEWordSeqToBitSeq(a[..]))| >= b;
    ensures BEWordSeqToBitSeq(a[..])[..PaddedLength(b)] == old(PadMessageForSHA(BEWordSeqToBitSeq(a[..])[..b]));
    modifies a;
{
    var numPad := NumPaddingZeroes(b);

    calc {
        a.Length * 32;
        >= PaddedLength(b);
        == { reveal_PaddedLength(); }
        b + 1 + NumPaddingZeroes(b) + 64;
        b + 1 + numPad + 64;
        > b + numPad + 33;
    }

    calc {
        (b + numPad + 1) % 32;
        (b + NumPaddingZeroes(b) + 1) % 32;
        == { reveal_NumPaddingZeroes(); }
        0;
    }

    calc {
        (b + numPad + 33) % 32;
        (32 + b + numPad + 1) % 32;
        { lemma_mod_add_multiples_vanish(b + numPad + 1, 32); }
        (b + numPad + 1) % 32;
        0;
    }

    lemma_BEWordSeqToBitSeq_ensures(a[..]);
    ghost var m := BEWordSeqToBitSeq(a[..])[..b];

    AppendBitToArray(a, b, 1);
    AppendBitsToArray(a, b + 1, 0, numPad);
    AppendWordToArray(a, b + numPad + 1, 0);
    AppendWordToArray(a, b + numPad + 33, b);

    assert IsWordArray(a);
    assert forall i {:trigger m[i]}{:trigger GetArrayBit(a, i)} :: 0 <= i < b ==> GetArrayBit(a, i) == m[i];
    assert GetArrayBit(a, b) == 1;
    assert forall i {:trigger GetArrayBit(a, i)} :: b + 1 <= i <= b + numPad ==> GetArrayBit(a, i) == 0;
    assert a[(b + numPad + 1) / 32] == 0;
    assert a[(b + numPad + 33) / 32] == b;

    Lemma_ArrayIsPaddedMessage(a, b, m);
}

static method {:dafnycc_conservative_seq_triggers} CreateArrayForSHA(messageBytes:seq<int>) returns (a: array<int>, b: int)
    requires IsByteSeq(messageBytes);
    ensures fresh(a);
    ensures b == |messageBytes| * 8;
    ensures b >= 0;
    ensures 0 <= PaddedLength(b) <= a.Length * 32;
    ensures IsWordArray(a);
    ensures |BEWordSeqToBitSeq_premium(a[..])| >= b;
    ensures BEByteSeqToBitSeq_premium(messageBytes) == BEWordSeqToBitSeq(a[..])[..b];
{
    reveal_PaddedLength();

    b := |messageBytes| * 8;
    var paddedLength := PaddedLength(b);

    lemma_LengthInPaddedMessageIsWordAligned(b);
    reveal_Mod32_const();
    assert paddedLength % 32 == 0;
    a := new int[paddedLength / 32];

    var wordseq := BEByteSeqToWordSeqTailPadding(messageBytes);
    ghost var wordseq_extended :=
        if |wordseq| <= a.Length then wordseq + RepeatDigit_premium(0, a.Length - |wordseq|) else wordseq[..a.Length];
    assert |wordseq_extended| == a.Length;

    lemma_2toX();

    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length;
        invariant forall j :: 0 <= j < i ==> Word32(a[j]);
        invariant a[..i] == wordseq_extended[..i];
    {
        if i < |wordseq| {
            a[i] := wordseq[i];
        }
        else {
            a[i] := 0;
        }
        assert a[..i+1] == a[..i] + [a[i]]; //- dafnycc triggering
        assert wordseq_extended[..i+1] == wordseq_extended[..i] + [wordseq_extended[i]]; //- dafnycc triggering
        i := i + 1;
    }

    assert a[..] == wordseq_extended[..a.Length] == wordseq_extended;

    if |wordseq| <= a.Length {
        calc {
            BEWordSeqToBitSeq_premium(wordseq_extended)[..b];
            { lemma_WordSeqToBitSeqChop(wordseq_extended, wordseq, RepeatDigit(0, a.Length - |wordseq|)); }
            (BEWordSeqToBitSeq_premium(wordseq) + BEWordSeqToBitSeq_premium(RepeatDigit(0, a.Length - |wordseq|)))[..b];
            BEWordSeqToBitSeq_premium(wordseq)[..b];
        }
    }
    else {
        calc {
            BEWordSeqToBitSeq_premium(wordseq_extended)[..b];
            BEWordSeqToBitSeq_premium(wordseq[..a.Length])[..b];
            (BEWordSeqToBitSeq_premium(wordseq[..a.Length]) + BEWordSeqToBitSeq_premium(wordseq[a.Length..]))[..b];
            { lemma_WordSeqToBitSeqChop(wordseq, wordseq[..a.Length], wordseq[a.Length..]); }
            BEWordSeqToBitSeq_premium(wordseq)[..b];
        }
    }
}

static lemma lemma_wordseq_dafnycc_trigger(wordseq_extended:seq<int>, i:int)
    requires 0 <= i < |wordseq_extended|;
    ensures wordseq_extended[..i+1] == wordseq_extended[..i] + [wordseq_extended[i]];
{
}




static method CreateArrayForSHA_arrays(messageBytes:array<int>) returns (a: array<int>, b: int)
    requires messageBytes!=null;
    requires IsByteSeq(messageBytes[..]);
    ensures fresh(a);
    ensures b == messageBytes.Length * 8;
    ensures b >= 0;
    ensures 0 <= PaddedLength(b) <= a.Length * 32;
    ensures IsWordArray(a);
    ensures |BEWordSeqToBitSeq_premium(a[..])| >= b;
    ensures BEByteSeqToBitSeq_premium(messageBytes[..]) == BEWordSeqToBitSeq(a[..])[..b];
{
    reveal_PaddedLength();

    b := messageBytes.Length * 8;
    var paddedLength := PaddedLength(b);

    lemma_LengthInPaddedMessageIsWordAligned(b);
    reveal_Mod32_const();
    assert paddedLength % 32 == 0;
    a := new int[paddedLength / 32];

    ghost var messageByteSeq := messageBytes[..];
    var wa,wordseq := BEByteSeqToWordSeqTailPadding_arrays(messageBytes, messageByteSeq);
//-    assert BEByteSeqToBitSeq(messageByteSeq) == BEWordSeqToBitSeq(wordseq)[..|messageByteSeq|*8];

    ghost var wordseq_extended :=
        if |wordseq| <= a.Length then wordseq + RepeatDigit_premium(0, a.Length - |wordseq|) else wordseq[..a.Length];
    assert |wordseq_extended| == a.Length;

    lemma_2toX();

    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length;
        invariant wa[..] == wordseq;
        invariant forall j :: 0 <= j < i ==> Word32(a[j]);
        invariant a[..i] == wordseq_extended[..i];
    {
        if i < wa.Length {
            a[i] := wa[i];
        }
        else {
            a[i] := 0;
        }
        assert a[..i+1] == a[..i] + [a[i]]; //- dafnycc triggering
        //-assert wordseq_extended[..i+1] == wordseq_extended[..i] + [wordseq_extended[i]]; //- dafnycc triggering
        lemma_wordseq_dafnycc_trigger(wordseq_extended, i);
        i := i + 1;
    }

    assert a[..] == wordseq_extended[..a.Length] == wordseq_extended;

    if |wordseq| <= a.Length {
        calc {
            BEWordSeqToBitSeq_premium(wordseq_extended)[..b];
            { lemma_WordSeqToBitSeqChop(wordseq_extended, wordseq, RepeatDigit(0, a.Length - |wordseq|)); }
            (BEWordSeqToBitSeq_premium(wordseq) + BEWordSeqToBitSeq_premium(RepeatDigit(0, a.Length - |wordseq|)))[..b];
            BEWordSeqToBitSeq_premium(wordseq)[..b];
        }
    }
    else {
        calc {
            BEWordSeqToBitSeq_premium(wordseq_extended)[..b];
            BEWordSeqToBitSeq_premium(wordseq[..a.Length])[..b];
            (BEWordSeqToBitSeq_premium(wordseq[..a.Length]) + BEWordSeqToBitSeq_premium(wordseq[a.Length..]))[..b];
            { lemma_WordSeqToBitSeqChop(wordseq, wordseq[..a.Length], wordseq[a.Length..]); }
            BEWordSeqToBitSeq_premium(wordseq)[..b];
        }
    }

    assert messageByteSeq == messageBytes[..]; //- OBSERVE
//-    assert BEByteSeqToBitSeq(messageByteSeq) == BEWordSeqToBitSeq(wordseq)[..|messageByteSeq|*8];
//-    assert BEByteSeqToBitSeq(messageBytes[..]) == BEWordSeqToBitSeq(wordseq)[..|messageBytes[..]|*8];
    calc {
        BEByteSeqToBitSeq_premium(messageBytes[..]);
        BEWordSeqToBitSeq_premium(wordseq)[..b];
        BEWordSeqToBitSeq_premium(wordseq_extended)[..b];
        BEWordSeqToBitSeq(a[..])[..b];
    }
}

static method CreateArrayForSHA_arrays_words(messageWords:array<int>) returns (a: array<int>, b: int)
    requires messageWords!=null;
    requires IsWordSeq(messageWords[..]);
    ensures fresh(a);
    ensures b == messageWords.Length * 32;
    ensures b >= 0;
    ensures 0 <= PaddedLength(b) <= a.Length * 32;
    ensures IsWordArray(a);
    ensures |BEWordSeqToBitSeq_premium(a[..])| >= b;
    ensures BEWordSeqToBitSeq_premium(messageWords[..]) == BEWordSeqToBitSeq(a[..])[..b];
{
    reveal_PaddedLength();

    b := messageWords.Length * 32;
    var paddedLength := PaddedLength(b);

    lemma_LengthInPaddedMessageIsWordAligned(b);
    reveal_Mod32_const();
    assert paddedLength % 32 == 0;
    a := new int[paddedLength / 32];

    ghost var messageWordSeq := messageWords[..];
    ghost var wordseq := messageWordSeq;
//-    var wa,wordseq := BEByteSeqToWordSeqTailPadding_arrays(messageBytes, messageByteSeq);
//-    assert BEByteSeqToBitSeq(messageByteSeq) == BEWordSeqToBitSeq(wordseq)[..|messageByteSeq|*8];

    ghost var wordseq_extended :=
        if |wordseq| <= a.Length then wordseq + RepeatDigit_premium(0, a.Length - |wordseq|) else wordseq[..a.Length];
    assert |wordseq_extended| == a.Length;

    lemma_2toX();

    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length;
        invariant messageWords[..] == wordseq;
        invariant forall j :: 0 <= j < i ==> Word32(a[j]);
        invariant a[..i] == wordseq_extended[..i];
    {
        if i < messageWords.Length {
            a[i] := messageWords[i];
        }
        else {
            a[i] := 0;
        }
        assert a[..i+1] == a[..i] + [a[i]]; //- dafnycc triggering
        //-assert wordseq_extended[..i+1] == wordseq_extended[..i] + [wordseq_extended[i]]; //- dafnycc triggering
        lemma_wordseq_dafnycc_trigger(wordseq_extended, i);
        i := i + 1;
    }

    assert a[..] == wordseq_extended[..a.Length] == wordseq_extended;

    if |wordseq| <= a.Length {
        calc {
            BEWordSeqToBitSeq_premium(wordseq_extended)[..b];
            { lemma_WordSeqToBitSeqChop(wordseq_extended, wordseq, RepeatDigit(0, a.Length - |wordseq|)); }
            (BEWordSeqToBitSeq_premium(wordseq) + BEWordSeqToBitSeq_premium(RepeatDigit(0, a.Length - |wordseq|)))[..b];
            BEWordSeqToBitSeq_premium(wordseq)[..b];
        }
    }
    else {
        calc {
            BEWordSeqToBitSeq_premium(wordseq_extended)[..b];
            BEWordSeqToBitSeq_premium(wordseq[..a.Length])[..b];
            (BEWordSeqToBitSeq_premium(wordseq[..a.Length]) + BEWordSeqToBitSeq_premium(wordseq[a.Length..]))[..b];
            { lemma_WordSeqToBitSeqChop(wordseq, wordseq[..a.Length], wordseq[a.Length..]); }
            BEWordSeqToBitSeq_premium(wordseq)[..b];
        }
    }

    assert messageWordSeq == messageWords[..]; //- OBSERVE
//-    assert BEByteSeqToBitSeq(messageByteSeq) == BEWordSeqToBitSeq(wordseq)[..|messageByteSeq|*8];
//-    assert BEByteSeqToBitSeq(messageBytes[..]) == BEWordSeqToBitSeq(wordseq)[..|messageBytes[..]|*8];
    calc {
        BEWordSeqToBitSeq_premium(messageWords[..]);
        BEWordSeqToBitSeq_premium(wordseq)[..b];
        BEWordSeqToBitSeq_premium(wordseq_extended)[..b];
        BEWordSeqToBitSeq(a[..])[..b];
    }
}

static lemma lemma_mod_words(bits:int, words:int)
    requires words == PaddedLength(bits)/32;
    ensures Mod16(words) == 0;
{ 
    reveal_Mod16(); lemma_PaddedLength_properties(bits); 
}

