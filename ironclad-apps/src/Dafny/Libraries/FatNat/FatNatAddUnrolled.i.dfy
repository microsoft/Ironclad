include "FatNatAdd.i.dfy"

method {:timeLimitMultiplier 4} FatNatAdd_optimized(a:array<int>, b:array<int>) returns (c:array<int>)
    requires a!=null;
    requires b!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires IsDigitSeq(power2(32), b[..]);
    ensures c!=null;
    ensures IsDigitSeq(power2(32), c[..]);
    ensures BEWordSeqToInt(a[..]) + BEWordSeqToInt(b[..]) == BEWordSeqToInt(c[..]);
    ensures fresh(c);
{
    var maxlen := if a.Length > b.Length then a.Length else b.Length;
    var padding := if (maxlen%8==0) then 0 else 8 - maxlen % 8;
    var paddedlen := maxlen + padding;
    assert paddedlen % 8 == 0;  //- OBSERVE

    lemma_2toX();

    var apad := PadArrayLeft(paddedlen-a.Length, a);
    lemma_LeadingZeros(power2(32), a[..], apad[..]);

    var bpad := PadArrayLeft(paddedlen-b.Length, b);
    lemma_LeadingZeros(power2(32), b[..], bpad[..]);

    c := FatNatAddUnrolledLoop(apad, bpad);
}

