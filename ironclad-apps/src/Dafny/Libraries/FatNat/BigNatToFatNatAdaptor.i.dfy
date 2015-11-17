include "FatNatCommon.i.dfy"
include "../BigNum/BigNatCore.i.dfy"
include "../BigNum/BigNumBEAdaptor.i.dfy"
include "CanonicalArrays.i.dfy"

include "FatInt.i.dfy"
include "../BigNum/BigNum.i.dfy"

method BigNatToFatNat(B:BigNat) returns (F:array<int>)
    requires WellformedBigNat(B);
    ensures F!=null && IsWordSeq(F[..]);
    ensures I(B) == BEWordSeqToInt(F[..]);
    ensures |B.words| == F.Length;
    ensures IsCanonicalDigitSeq(power2(32), F[..]);
{
    F := new int[|B.words|];
    var i:=0;
    while (i<|B.words|)
        invariant 0<=i<=|B.words|;
        invariant forall j::0<=j<i ==> F[j] == B.words[|B.words|-1-j];
    {
        F[i] := B.words[|B.words|-1-i];
        i := i + 1;
    }
    
    lemma_2toX();
    calc {
        I(B);
            { lemma_BigNatIIsLEDigitSeqToInt(B); }
        LEDigitSeqToInt(Width(), B.words);
            { lemma_Reverse_converts_endianness_inner(Width(), F[..], B.words); }
        BEDigitSeqToInt(Width(), F[..]);
    }
}

method FatNatToBigNat(F:array<int>) returns (B:BigNat)
    requires F!=null && IsWordSeq(F[..]);
    ensures WellformedBigNat(B);
    ensures I(B) == BEWordSeqToInt(F[..]);
    ensures |B.words| <= F.Length;
{
    lemma_2toX();

    var t := CountTopZeroWords(F);
    
    var lewords := ReverseDigitSeq(power2(32), F[t..]);
    lemma_Reverse(F[t..], lewords);
    if (|lewords|>0)
    {
        assert lewords[|lewords|-1] == F[t..][0] == F[t];   //- OBSERVE
    }
    B := BigNat_ctor(lewords);

    calc {
        I(B);
            { lemma_BigNatIIsLEDigitSeqToInt(B); }
        LEDigitSeqToInt(Width(), B.words);
            { lemma_Reverse_converts_endianness_inner(Width(), F[t..], lewords); }
        BEDigitSeqToInt(Width(), F[t..]);
            { lemma_LeadingZeros(power2(32), F[t..], F[..]); }
        BEDigitSeqToInt(Width(), F[..]);
    }
}

method FatIntToBigNum(F:FatInt) returns (B:BigNum)
    requires WellformedFatInt(F);
    ensures WellformedBigNum(B);
    ensures BV(B) == FIV(F);
    ensures |B.value.words| <= F.value.Length;
{
    var bv := FatNatToBigNat(F.value);
    B := BigNum_ctor(F.negate, bv);
}
