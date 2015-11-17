include "FatNatDivDefs.i.dfy"

//- The simplest possible estimator: it subtracts q=1 copy of dv at a time.
//- Runtime is linear in the value of the final quotient.

method FNDivision_Estimate_Q_trivial(n:array<int>, dv:array<int>) returns (q:array<int>)
    requires n!=null;
    requires IsWordSeq(n[..]);
    requires dv!=null;
    requires IsWordSeq(dv[..]);
    requires 0 < BEWordSeqToInt(dv[..]) <= BEWordSeqToInt(n[..]);
    ensures q!=null;
    ensures IsWordSeq(q[..]);
    ensures 0 < BEWordSeqToInt(q[..])*BEWordSeqToInt(dv[..]);
    ensures BEWordSeqToInt(q[..])*BEWordSeqToInt(dv[..]) <= BEWordSeqToInt(n[..]);
{
    ghost var Divs := dv[..];
    q := new int[1];
    q[0] := 1;
    ghost var Qs := q[..];
    lemma_2toX();
    ghost var Qv := BEWordSeqToInt(Qs);
    reveal_BEDigitSeqToInt_private();
    lemma_mul_basics_forall();
    assert Qs[0..|Qs|-1] == []; //- OBSERVE
    assert Qv == BEWordSeqToInt(Qs[0..|Qs|-1])*power2(32) + Qs[|Qs|-1]; //- OBSERVE
    assert Qv == 1;
    calc {
        BEWordSeqToInt(q[..])*BEWordSeqToInt(dv[..]);
        BEWordSeqToInt(Qs)*BEWordSeqToInt(Divs);
        Qv*BEWordSeqToInt(Divs);
        BEWordSeqToInt(Divs);
        BEWordSeqToInt(dv[..]);
    }
    lemma_BEDigitSeqToInt_bound(power2(32), Qs);
    lemma_BEDigitSeqToInt_bound(power2(32), Divs);
    assert 0 < BEWordSeqToInt(q[..]);
    assert 0 < BEWordSeqToInt(dv[..]);
    lemma_mul_strictly_positive(BEWordSeqToInt(q[..]), BEWordSeqToInt(dv[..]));
}



