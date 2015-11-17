//- <NuBuild AddDafnyFlag /z3opt:NL_ARITH=true/>
include "BigNum.i.dfy"
include "../Math/mul.i.dfy"

datatype BigRat = BigRat_ctor(
    n : BigNum,
    d : BigNat);

static function WellformedBigRat(Q:BigRat) : bool
{
    WellformedBigNum(Q.n) && WellformedBigNat(Q.d) && !zero(Q.d)
}

static function RV(Q:BigRat) : real
    requires WellformedBigRat(Q);
{
    real(BV(Q.n)) / real(I(Q.d))
}

static function method BigRatNegate(Q:BigRat) : BigRat
    requires WellformedBigRat(Q);
    ensures WellformedBigRat(BigRatNegate(Q));
    ensures RV(BigRatNegate(Q)) == 0.0 - RV(Q);
{
    BigRat_ctor(BigNumNegate(Q.n), Q.d)
}

static lemma Lemma_BigRatAdd(an:int, ad:int, bn:int, bd:int)
    requires ad != 0;
    requires bd != 0;
    ensures real(ad * bd) != 0.0;
    ensures real(an * bd + bn * ad) / real(ad * bd) == real(an) / real(ad) + real(bn) / real(bd);
{
    lemma_mul_nonzero(ad, bd);
    Lemma_RealOfMultiplyIsMultiply(an, bd);
    Lemma_RealOfMultiplyIsMultiply(ad, bd);
    Lemma_RealOfMultiplyIsMultiply(bn, ad);
    Lemma_RealOfMultiplyIsMultiply(bd, ad);
}

method BigRatAdd(A:BigRat, B:BigRat) returns (R:BigRat)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures WellformedBigRat(R);
    ensures RV(R) == RV(A) + RV(B);
{
    var ScaledANumerator:BigNum := BigNumMul(A.n, BigNum_ctor(false, B.d));
    var ScaledBNumerator:BigNum := BigNumMul(B.n, BigNum_ctor(false, A.d));
    var ResultNumerator:BigNum := BigNumAdd(ScaledANumerator, ScaledBNumerator);
    var ResultDenominator:BigNat := BigNatMul(A.d, B.d);
    lemma_mul_nonzero(I(A.d), I(B.d));
    R := BigRat_ctor(ResultNumerator, ResultDenominator);
    Lemma_BigRatAdd(BV(A.n), I(A.d), BV(B.n), I(B.d));
}

static lemma Lemma_BigRatSub(an:int, ad:int, bn:int, bd:int)
    requires ad != 0;
    requires bd != 0;
    ensures real(ad * bd) != 0.0;
    ensures real(an * bd - bn * ad) / real(ad * bd) == real(an) / real(ad) - real(bn) / real(bd);
{
    lemma_mul_nonzero(ad, bd);
    Lemma_RealOfMultiplyIsMultiply(an, bd);
    Lemma_RealOfMultiplyIsMultiply(ad, bd);
    Lemma_RealOfMultiplyIsMultiply(bn, ad);
    Lemma_RealOfMultiplyIsMultiply(bd, ad);
}

method BigRatSub(A:BigRat, B:BigRat) returns (R:BigRat)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures WellformedBigRat(R);
    ensures RV(R) == RV(A) - RV(B);
{
    var ScaledANumerator:BigNum := BigNumMul(A.n, BigNum_ctor(false, B.d));
    var ScaledBNumerator:BigNum := BigNumMul(B.n, BigNum_ctor(false, A.d));
    var ResultNumerator:BigNum := BigNumSub(ScaledANumerator, ScaledBNumerator);
    var ResultDenominator:BigNat := BigNatMul(A.d, B.d);
    lemma_mul_nonzero(I(A.d), I(B.d));
    R := BigRat_ctor(ResultNumerator, ResultDenominator);
    Lemma_BigRatSub(BV(A.n), I(A.d), BV(B.n), I(B.d));
    calc {
        RV(R);
        real(BV(R.n)) / real(I(R.d));
        real(BV(A.n)) / real(I(A.d)) - real(BV(B.n)) / real(I(B.d));
        RV(A) - RV(B);
    }
}

method BigRatCmp(A:BigRat, B:BigRat) returns (c:BNCmp)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures (c==BNCmpLt) <==> (RV(A)  < RV(B));
    ensures (c==BNCmpEq) <==> (RV(A) == RV(B));
    ensures (c==BNCmpGt) <==> (RV(A)  > RV(B));
{
    var ScaledANumerator:BigNum := BigNumMul(A.n, BigNum_ctor(false, B.d));
    var ScaledBNumerator:BigNum := BigNumMul(B.n, BigNum_ctor(false, A.d));
    c := BigNumCmp(ScaledANumerator, ScaledBNumerator);

    ghost var CommonDenominator:BigNat := BigNatMul(A.d, B.d);
    lemma_mul_nonzero(I(A.d), I(B.d));
    ghost var ScaledA := BigRat_ctor(ScaledANumerator, CommonDenominator);
    ghost var ScaledB := BigRat_ctor(ScaledBNumerator, CommonDenominator);
    Lemma_ScalingPreservesValue(A, ScaledA, B.d);
    lemma_mul_is_commutative(I(A.d), I(B.d));
    Lemma_ScalingPreservesValue(B, ScaledB, A.d);
    Lemma_DivideByPositiveRealPreservesOrder(real(BV(ScaledANumerator)), real(BV(ScaledBNumerator)), real(I(CommonDenominator)));
}

method BigRatLt(A:BigRat, B:BigRat) returns (r:bool)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures r == (RV(A) < RV(B));
{
    var c := BigRatCmp(A,B);
    r := (c.BNCmpLt?);
}

method BigRatLe(A:BigRat, B:BigRat) returns (r:bool)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures r == (RV(A) <= RV(B));
{
    var c := BigRatCmp(A,B);
    r := (c.BNCmpLt? || c.BNCmpEq?);
}

method BigRatEq(A:BigRat, B:BigRat) returns (r:bool)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures r == (RV(A) == RV(B));
{
    var c := BigRatCmp(A,B);
    r := (c.BNCmpEq?);
}

method BigRatNe(A:BigRat, B:BigRat) returns (r:bool)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures r == (RV(A) != RV(B));
{
    var c := BigRatCmp(A,B);
    r := !(c.BNCmpEq?);
}

method BigRatGe(A:BigRat, B:BigRat) returns (r:bool)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures r == (RV(A) >= RV(B));
{
    var c := BigRatCmp(A,B);
    r := (c.BNCmpGt? || c.BNCmpEq?);
}

method BigRatGt(A:BigRat, B:BigRat) returns (r:bool)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures r == (RV(A) > RV(B));
{
    var c := BigRatCmp(A,B);
    r := (c.BNCmpGt?);
}

method BigRatMul(A:BigRat, B:BigRat) returns (R:BigRat)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures WellformedBigRat(R);
    ensures RV(R) == RV(A) * RV(B);
{
    var ResultNumerator:BigNum := BigNumMul(A.n, B.n);
    var ResultDenominator:BigNat := BigNatMul(A.d, B.d);
    lemma_mul_nonzero(I(A.d), I(B.d));
    R := BigRat_ctor(ResultNumerator, ResultDenominator);

    Lemma_RealOfMultiplyIsMultiply(BV(A.n), BV(B.n));
    Lemma_RealOfMultiplyIsMultiply(I(A.d), I(B.d));
    assert !zero(R.d);
}

method BigRatDiv(A:BigRat, B:BigRat) returns (R:BigRat)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    requires nonzero(B.n.value);
    ensures WellformedBigRat(R);
    ensures RV(R) == RV(A) / RV(B);
{
    if (zero(A.n.value)) {
        R := BigRat_ctor(MakeSmallLiteralBigNum(0), MakeSmallLiteralBigNat(1));
        assert RV(R) == real(0) == RV(A) / RV(B);
        return;
    }

    var ResultNegative:bool := (A.n.negate != B.n.negate);
    var ResultNumerator:BigNum := BigNumMul(BigNum_ctor(ResultNegative, A.n.value), BigNum_ctor(false, B.d));
    var ResultDenominator:BigNat := BigNatMul(B.n.value, A.d);
    lemma_mul_nonzero(I(B.n.value), I(A.d));
    R := BigRat_ctor(ResultNumerator, ResultDenominator);

    Lemma_RealOfMultiplyIsMultiply(BV(BigNum_ctor(ResultNegative, A.n.value)), BV(BigNum_ctor(false, B.d)));
    Lemma_RealOfMultiplyIsMultiply(I(B.n.value), I(A.d));
    assert I(ResultDenominator) == I(B.n.value) * I(A.d);

    calc {
        RV(R);
        real(BV(ResultNumerator)) / real(I(ResultDenominator));
        real(BV(ResultNumerator)) / real(I(B.n.value) * I(A.d));
    }
}

static function method MakeSmallLiteralBigRat(x:nat) : BigRat
    requires x < Width();
    ensures WellformedBigRat(MakeSmallLiteralBigRat(x));
    ensures RV(MakeSmallLiteralBigRat(x)) == real(x);
{
    lemma_2toX();
    BigRat_ctor(MakeSmallLiteralBigNum(x), MakeSmallLiteralBigNat(1))
}

static function method BigNatToBigRat(x:BigNat) : BigRat
    requires WellformedBigNat(x);
    ensures WellformedBigRat(BigNatToBigRat(x));
    ensures RV(BigNatToBigRat(x)) == real(I(x));
{
    lemma_2toX();
    BigRat_ctor(BigNum_ctor(false, x), MakeSmallLiteralBigNat(1))
}

//-/////////////////////////////////
//- Useful mathematical lemmas
//-/////////////////////////////////

static lemma Lemma_RealOfMultiplyIsMultiply(a:int, b:int)
    ensures real(a * b) == real(a) * real(b);
{
    lemma_mul_is_mul_boogie(a, b);
}

static lemma Lemma_ScalingPreservesValue(A:BigRat, ScaledA:BigRat, scale:BigNat)
    requires WellformedBigRat(A);
    requires WellformedBigRat(ScaledA);
    requires WellformedBigNat(scale);
    requires nonzero(scale);
    requires BV(ScaledA.n) == BV(A.n) * I(scale);
    requires I(ScaledA.d) == I(A.d) * I(scale);
    ensures RV(A) == RV(ScaledA);
{
    Lemma_RealOfMultiplyIsMultiply(BV(A.n), I(scale));
    Lemma_RealOfMultiplyIsMultiply(I(A.d), I(scale));
}

static lemma Lemma_DivideByPositiveRealPreservesOrder(a:real, b:real, c:real)
    requires c > 0.0;
    ensures a < b <==> a/c < b/c;
    ensures a == b <==> a/c == b/c;
    ensures a > b <==> a/c > b/c;
{
}
