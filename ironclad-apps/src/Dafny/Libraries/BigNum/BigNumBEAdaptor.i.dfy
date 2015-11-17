include "BigNatCore.i.dfy"
include "../Util/seqs_transforms.i.dfy"
include "../Util/seqs_reverse.i.dfy"

//-////////////////////////////////////////////////////////////////////////////
//- Convert between "legacy" little-endian, well-formed-required BigNats
//- and new-style BEIsByteSeq

static predicate ZeroPrefix(s:seq<int>, s_suffix:seq<int>)
{
    |s| >= |s_suffix|
    && s[ |s|-|s_suffix| .. ] == s_suffix
    && forall i :: 0 <= i < |s|-|s_suffix| ==> s[i] == 0
}

//- Takes a string that may contain leading zeros.
//- Returns a string with no leading zeros.
static method StripLeadingZeros(ghost pv:int, ins:seq<int>) returns (outs:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, ins);
    ensures IsDigitSeq(pv, outs);
    ensures ZeroPrefix(ins, outs);
    ensures |outs|>0 ==> outs[0]!=0;
{
    var ptr := 0;
    while (ptr<|ins| && ins[ptr]==0)
        invariant 0 <= ptr <= |ins|;
        invariant forall i :: 0 <= i < ptr ==> ins[i] == 0;
    {
        ptr := ptr + 1;
    }
    outs := ins[ptr..];
}



static lemma lemma_BigNatIIsLEDigitSeqToInt(a:BigNat)
    requires WellformedBigNat(a);
    decreases |a.words|;
    ensures I(a) == LEDigitSeqToInt(Width(), a.words);
{
    reveal_I();
    reveal_LEDigitSeqToInt_private();
    if (|a.words|>0)
    {
        lemma_BigNatIIsLEDigitSeqToInt(BigNat_ctor(a.words[1..]));
    }
}

static method BigNatToBEByteSeq(M:BigNat) returns (m:seq<int>)
    requires WellformedBigNat(M);
    ensures IsByteSeq(m);
    ensures BEByteSeqToInt(m) == I(M);
    ensures BEIntToByteSeq(I(M)) == m;
    ensures |m|==0 || 0<m[0];
{
    lemma_2toX();
    var be_word_seq := ReverseDigitSeq(4294967296, M.words);
    var be_words := be_word_seq;

    lemma_Reverse_preserves_IsDigitSeq(Width(), M.words, be_words);

    assert IsWordSeq(be_words);
    var bloated_byte_seq := BEWordSeqToByteSeq_impl(be_words);    //- may have leading zeros
    m := TrimLeadingZeros(256, bloated_byte_seq);

    ghost var le_words := M.words;

    lemma_Reverse(M.words, be_word_seq);
    lemma_Reverse_converts_endianness_inner(Width(), be_words, le_words);

    calc {
        I(M);
            { lemma_BigNatIIsLEDigitSeqToInt(M); }
        LEDigitSeqToInt(Width(), M.words);
        BEDigitSeqToInt(Width(), be_words);
        BEByteSeqToInt(m);
    }

//-    assert I(M) == BEDigitSeqToInt(256, m);
    lemma_BEDigitSeqToInt_invertibility(256, I(M), m);
//-    assert BEIsWordSeqToIsByteSeq_impl
//-    assert m == BEIntToDigitSeq(256, 0, I(M));

    lemma_BEDigitSeqToInt_invertibility_tight(256, BEDigitSeqToInt(256, m), m);
//-    ensures digitseq == BEIntToDigitSeq(pv, 0, x);
}

static method BEByteSeqToBigNat(m:seq<int>) returns (M:BigNat)
    requires IsByteSeq(m);
    ensures WellformedBigNat(M);
    ensures BEByteSeqToInt(m) == I(M);
//-    ensures BEIntToByteSeq(I(M)) == m;    //- not available, unless we require no prefix 0s.
{
    lemma_2toX();
    var be_words:seq<int>;
    ghost var pad_bytes:seq<int>;
    be_words,pad_bytes := BEByteSeqToWordSeq_impl(m);
    var be_words_normalized := StripLeadingZeros(4294967296, be_words);
//-    assert |be_words_normalized|>0 ==> be_words_normalized[0]!=0;

    var le_words := ReverseDigitSeq(4294967296, be_words_normalized);
    lemma_Reverse(be_words_normalized, le_words);
//-    assert |le_words|>0 ==> le_words[|le_words|-1]!=0;

    M := BigNat_ctor(le_words);

    calc {
        I(M);
            { lemma_BigNatIIsLEDigitSeqToInt(M); }
        LEDigitSeqToInt(Width(), le_words);
            { lemma_Reverse_converts_endianness_inner(Width(), be_words_normalized, le_words); }
        BEDigitSeqToInt(Width(), be_words_normalized);
            { lemma_LeadingZeros(Width(), be_words_normalized, be_words); }
        BEDigitSeqToInt(Width(), be_words);
        BEDigitSeqToInt(power2(8), m);
        BEByteSeqToInt(m);
    }
}


