include "FatNatCommon.i.dfy"
include "Bitwise.i.dfy"







predicate {:heap} ModestFatNatValue(X:array<int>)
    reads X;
{
    WellformedFatNat(X)
    && J(X) < power2(power2(31))
}

method IsModestFatNat(X:array<int>) returns (rc:bool)
    requires WellformedFatNat(X);
    ensures rc <==> ModestFatNatValue(X);
{
    var xc := FatNatCountBits(X);
    rc := xc <= 0x80000000;
    lemma_2toX32();
    if (rc) {
        lemma_power2_increases(xc, 0x80000000);
    } else {
        lemma_power2_increases(power2(31), xc-1);
    }
}

