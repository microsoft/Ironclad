include "../Math/mul.i.dfy"
include "Word32.i.dfy"

datatype BigNat = BigNat_ctor(
    words : seq<int>);

static function WellformedBigNat(b:BigNat) : bool
{
    (forall i :: 0 <= i < |b.words| ==> b.words[i]>=0 && Word32(b.words[i]))
    && (|b.words|==0 || b.words[|b.words|-1] > 0)
}

static function {:opaque} I(b:BigNat) : nat
    decreases |b.words|;
    requires WellformedBigNat(b);
{
    lemma_mul_nonnegative_forall();
    if (|b.words|==0) then
        0
    else
        I(BigNat_ctor(b.words[1..])) * Width()+b.words[0]
}

static function method lo(a:BigNat) : nat
    requires WellformedBigNat(a);
    ensures Word32(lo(a));
{
    if (|a.words|==0) then 0 else a.words[0]
}

static function method hi(a:BigNat) : BigNat
    requires WellformedBigNat(a);
    ensures WellformedBigNat(hi(a));
{
    if (|a.words|==0) then
        BigNat_ctor([])
    else
        BigNat_ctor(a.words[1..])
}

static lemma lemma_hilo(A:BigNat)
    requires WellformedBigNat(A);
    ensures I(A)==I(hi(A)) * Width() + lo(A);
{
    reveal_I();
    if (|A.words|==0)
    {
        calc {
            I(A);
            0;
                { lemma_mul_properties(); }
            0 * Width();
            I(hi(A)) * Width();
        }
    }
}

static lemma lemma_I_length_implies_value(a:BigNat)
    decreases |a.words|;
    requires WellformedBigNat(a);
    ensures |a.words|==0 ==> I(a)==0;
    ensures |a.words|>0 ==> I(a)>0;
{
    if (|a.words|==0)
    {
        reveal_I();
        assert I(a)==0;
    }
    else if (|a.words|==1)
    {
        reveal_I();
        lemma_mul_basics_forall();
        assert I(a)>0;
    }
    else
    {
        var sub_a:BigNat := hi(a);
        lemma_I_length_implies_value(sub_a);
        assert |sub_a.words| > 0;
        assert I(sub_a) > 0;
        calc {
            I(a);
                { reveal_I(); }
            I(BigNat_ctor(a.words[1..])) * Width() + a.words[0];
            I(sub_a) * Width() + a.words[0];
            > {
                    assert I(sub_a) > 0;
                    assert Width() > 0;
                    lemma_mul_strictly_positive_forall();
                    assert I(sub_a) * Width() > 0;
                }
            0;
        }
        assert I(a)>0;
    }
}

static lemma lemma_I_value_implies_length(a:BigNat)
    requires WellformedBigNat(a);
    ensures I(a)==0 ==> |a.words|==0;
{
    if (I(a)==0)
    {
        if (|a.words|>0)
        {
            lemma_I_length_implies_value(a);
            assert I(a)>0;
            assert false;
        }
        assert |a.words|==0;
    }
    else
    {
        if (|a.words|==0)
        {
            lemma_I_length_implies_value(a);
            assert I(a)==0;
            assert false;
        }
        assert |a.words|>0;
    }
}

static function method nonzero(a:BigNat) : bool
    requires WellformedBigNat(a);
    ensures nonzero(a) <==> I(a)!=0;
{
    lemma_I_length_implies_value(a);
    lemma_I_value_implies_length(a);
    |a.words|>0
}

static function method zero(a:BigNat) : bool
    requires WellformedBigNat(a);
    ensures zero(a) <==> I(a)==0;
{
    lemma_I_length_implies_value(a);
    lemma_I_value_implies_length(a);
    |a.words|==0
}

static function method BigNatZero() : BigNat
    ensures WellformedBigNat(BigNatZero());
    ensures zero(BigNatZero());
    ensures zero(BigNatZero()) <==> I(BigNatZero())==0;
    ensures I(BigNatZero()) == 0;
{
    reveal_I();
    BigNat_ctor([])
}

static lemma selectively_reveal_I(A:BigNat)
    requires WellformedBigNat(A);
    ensures I(A) ==
        if (|A.words|==0) then
            0
        else
            I(BigNat_ctor(A.words[1..])) * Width()+A.words[0];
{
    reveal_I();
}

static lemma lemma_I_is_nonnegative(A:BigNat)
    requires WellformedBigNat(A);
    ensures 0 <= I(A);
{
    if (|A.words|==0)
    {
    }
    else
    {
        calc {
            I(A);
                { selectively_reveal_I(A); }
            I(BigNat_ctor(A.words[1..])) * Width()+A.words[0];
            >=    { lemma_mul_nonnegative_forall(); }
            0+A.words[0];
            >= 0;
        }
    }
}

static lemma lemma_I_is_nonnegative_forall()
    ensures forall A:BigNat :: WellformedBigNat(A) ==> 0 <= I(A);
{
    forall (A:BigNat | WellformedBigNat(A))
        ensures 0 <= I(A);
    {
        lemma_I_is_nonnegative(A);
    }
}
