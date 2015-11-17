include "BigNatBitCount.i.dfy"
include "BigNatMod.i.dfy"
include "../Util/seqs_reverse.i.dfy"
include "BigNumBEAdaptor.i.dfy"

static method FakeBigNat(digit:nat, count:nat) returns (F:BigNat)
    requires Word32(digit);
    requires 1<digit;
    requires 1<count<power2(25);
    ensures FrumpyBigNat(F);
    ensures !zero(F);
    ensures 1<I(F);
    ensures |F.words| == count;
    ensures forall i :: 0 <= i < count ==> F.words[i]==digit;
{
    var s := RepeatDigit_impl(digit, count);
    ghost var rs := Reverse(s);
    F := BigNat_ctor(s);

    lemma_BigNatIIsLEDigitSeqToInt(F);
    lemma_Reverse_symmetry(rs, F.words);
    lemma_Reverse(rs, F.words);
    lemma_Reverse_converts_endianness(Width(), rs, F.words);
    calc {
        I(F);
        LEDigitSeqToInt(Width(), F.words);
        BEDigitSeqToInt_premium(Width(), rs);
    }
    lemma_BEDigitSeqToInt_bound(Width(), rs);
    lemma_2toX32();

    calc {
        32 * count;
        <   { lemma_mul_strict_inequality_forall(); lemma_mul_is_commutative_forall(); }
        32 * power2(25);
        power2(5)*power2(25);
            { lemma_power2_adds(5,25); }
        power2(30);
    }
    calc {
        I(F);
        BEDigitSeqToInt(Width(), rs);
        < power(Width(), |rs|);
        power(power2(32), |rs|);
            { lemma_power2_is_power_2(32); }
        power(power(2,32), |rs|);
            { lemma_power_multiplies(2,32,|rs|); }
        power(2,32*|rs|);
            { lemma_power2_is_power_2(32 * |rs|); }
        power2(32 * |rs|);
        power2(32 * count);
        <   { lemma_power2_strictly_increases(32 * count, power2(30)); }
        power2(power2(30));
        Frump();
    }

    lemma_2toX();
    lemma_power_1(Width());
    lemma_power_increases(Width(), 1, |rs|-1);
    calc {
        1;
        <
        power(Width(), |rs|-1);
        <=  { lemma_mul_increases(rs[0], power(Width(), |rs|-1)); }
        rs[0] * power(Width(), |rs|-1);
        <= BEDigitSeqToInt(Width(), rs);
        I(F);
    }
}

