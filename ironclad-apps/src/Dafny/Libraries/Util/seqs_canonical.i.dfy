include "seqs_and_ints.i.dfy"

//- Reason about the lengths of sequences with no preceding zeros

static predicate IsCanonicalDigitSeq(pv:nat, inseq:seq<int>)
{
    IsDigitSeq(pv, inseq)
    && (|inseq|>0 ==> inseq[0]!=0)
}

static lemma lemma_CanonicalLengthBound(pv:nat, inseq:seq<int>, l:nat)
    requires IsCanonicalDigitSeq(pv, inseq);
    requires BEDigitSeqToInt(pv, inseq) < power(pv, l);
    ensures |inseq| <= l;
{
    if (|inseq|>0)
    {
        if (l < |inseq|)
        {
            calc {
                power(pv, l);
                <=  { lemma_power_increases(pv, l, |inseq|-1); }
                power(pv, |inseq|-1);
                <=  { lemma_power_positive(pv, |inseq|-1);
                      lemma_mul_increases(inseq[0], power(pv, |inseq|-1)); }
                inseq[0] * power(pv, |inseq|-1);
                <=  { lemma_BEDigitSeqToInt_bound(pv, inseq); }
                BEDigitSeqToInt(pv, inseq);
                <
                power(pv,l);
            }
        }
    }

}

lemma lemma_CanonicalLength_inherit(pv:int, A:seq<int>, B:seq<int>, l:nat)
    requires 1<pv;
    requires |B| < l;
    requires IsCanonicalDigitSeq(pv, A);
    requires IsDigitSeq(pv, B);
    requires BEDigitSeqToInt(pv, A) < BEDigitSeqToInt(pv, B);
    ensures |A| < l;
{
    calc {
        BEDigitSeqToInt(pv,A);
        <
        BEDigitSeqToInt(pv,B);
        <   { lemma_BEDigitSeqToInt_bound(pv, B); }
        power(pv, |B|);
        <=  { lemma_power_increases(pv, |B|, l-1); }
        power(pv, l-1);
    }
    lemma_CanonicalLengthBound(pv, A, l-1);
}

