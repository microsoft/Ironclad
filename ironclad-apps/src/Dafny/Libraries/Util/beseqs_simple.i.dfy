include "be_sequences.s.dfy"

static lemma lemma_selection_preserves_digit_seq(pv:int, a:seq<int>, i:int)
    requires IsDigitSeq(pv, a);
    requires 0 <= i <= |a|;
    ensures IsDigitSeq(pv, a[i..]);
    ensures IsDigitSeq(pv, a[..i]);
{
}
