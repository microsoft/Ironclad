include "BigNatAdd.i.dfy"
include "BigNatCompare.i.dfy"

static lemma lemma_mul_zero()
    ensures forall x,y :: x==0 || y==0 ==> x*y == 0;
{
    forall (x:int, y:int | x==0 || y==0)
        ensures x*y==0;
    {
        if (x==0)
        {
            lemma_mul_basics(y);
            assert x*y == 0;
        }
        else
        {
            assert y==0;
            lemma_mul_basics(x);
            lemma_mul_is_commutative(x,y);
            assert x*y == 0;
        }
    }
}

static lemma lemma_mul_monotonic(x:int, y:int)
    ensures (1 < x && 0 < y) ==> (y < x*y);
{ lemma_mul_properties(); }


//-////////////////////////////////////////////////////////////////////////////

method SmallMul_(a:nat, b:nat) returns (s:BigNat)
    requires Word32(a);
    requires Word32(b);
    ensures WellformedBigNat(s);
    ensures I(s) == a*b;
{

    var l,h := Product32(a,b);
    if (l==0 && h==0)
    {
        lemma_mul_zero();
        s := BigNat_ctor([]);
        reveal_I();
    }
    else if (h==0)
    {
        s := BigNat_ctor([l]);
        reveal_I();
    }
    else
    {
        s := BigNat_ctor([l,h]);
        calc {
            I(s);
                { reveal_I(); }
            I(BigNat_ctor(s.words[1..])) *  Width() + l;
                { reveal_I(); lemma_mul_zero(); }
            h *  Width() + l;
                //- Product32 ensures
            a*b;
        }
    }
}

method BigNatLeftShift_(A:BigNat) returns (R:BigNat)
    requires WellformedBigNat(A);
    ensures WellformedBigNat(R);
    ensures I(R) == I(A) *  Width();
{
    if (zero(A))
    {
        lemma_mul_zero();
        R := A;
    }
    else
    {
        R := BigNat_ctor([0] + A.words);
        reveal_I();
    }
}

static lemma lemma_step1(b:int, ihiAW:int, loA:int)
    ensures b *  ihiAW + b * loA == b * (ihiAW + loA);
{
    lemma_mul_is_distributive_add(b, ihiAW, loA);
}

method BigNatSingleMul_(A:BigNat, b:nat) returns (R:BigNat)
    decreases |A.words|;
    requires WellformedBigNat(A);
    requires Word32(b);
    ensures WellformedBigNat(R);
    ensures I(A) * b == I(R);
{
    R := BigNatZero();
    calc {
        I(BigNatZero()) * b;
        0 * b;
            { lemma_mul_zero(); }
        0;
        I(R);
    }
    var n := |A.words|;
    assert A.words[n..] == [];
    while (n > 0)
        invariant 0 <= n <= |A.words|;
        invariant WellformedBigNat(R);
        invariant I(R) == I(BigNat_ctor(A.words[n..])) * b;    //- induction hypothesis
    {
        ghost var hi_A := BigNat_ctor(A.words[n..]);
        ghost var ugly_expression := I(hi_A) *  Width();
        n := n - 1;
        ghost var hilo_A := BigNat_ctor(A.words[n..]);
        assert hi_A.words == hi(hilo_A).words;
        var sub_R := R;
        var parent:BigNat := BigNatLeftShift_(sub_R);
        var child:BigNat := SmallMul_(A.words[n], b);
        R := BigNatAdd(parent, child);

        calc {
            I(R);
            I(parent) + I(child);
            I(parent) + A.words[n] * b;
            I(sub_R) *  Width() + A.words[n] * b;
            (I(hi_A) * b) * Width() + A.words[n] * b;
                { lemma_mul_is_commutative(I(hi_A),b); }
            (b * I(hi_A)) * Width() + A.words[n] * b;
                { lemma_mul_is_associative(b, I(hi_A), Width()); }
            b * (I(hi_A) *  Width()) + A.words[n] * b;
                { lemma_mul_is_commutative(b,A.words[n]); }
            b * ugly_expression + b * A.words[n];
                { lemma_step1(b, ugly_expression, A.words[n]); }
            b * (ugly_expression + A.words[n]);
                { lemma_hilo(hilo_A); }
            b * I(hilo_A);
                { lemma_mul_is_commutative(b,I(hilo_A)); }
            I(hilo_A) * b;
        }
    }
    assert A.words[0..] == A.words;
}

method BigNatMul(A:BigNat, B:BigNat) returns (R:BigNat)
    decreases |B.words|;
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    ensures WellformedBigNat(R);
    ensures I(A) * I(B) == I(R);
{
    if (zero(A))
    {
        lemma_mul_zero();
        R := A;
        return;
    }
    R := BigNatZero();
    var n := |B.words|;
    assert B.words[n..] == [];
    lemma_mul_zero();
    while (n > 0)
        invariant 0 <= n <= |B.words|;
        invariant WellformedBigNat(R);
        invariant I(R) == I(A) *  I(BigNat_ctor(B.words[n..]));    //- induction hypothesis
    {
        ghost var hi_B := BigNat_ctor(B.words[n..]);
        n := n - 1;
        ghost var hilo_B := BigNat_ctor(B.words[n..]);
        assert hi_B.words == hi(hilo_B).words;
        var sub_R := R;
        var parent:BigNat := BigNatLeftShift_(sub_R);
        var child:BigNat := BigNatSingleMul_(A, B.words[n]);
        R := BigNatAdd(parent, child);

        calc
        {
            I(R);
            I(parent) + I(child);
            I(sub_R) *  Width() + I(child);
            I(sub_R) *  Width() + I(A) *  B.words[n];
            (I(A) *  I(hi_B)) * Width() + I(A) *  B.words[n];
                { lemma_mul_is_associative(I(A), I(hi_B), Width()); }
            I(A) * (I(hi_B) * Width()) + I(A) *  B.words[n];
                { lemma_mul_is_distributive_add(I(A), I(hi_B) *  Width(), B.words[n]); }
            I(A) * (I(hi_B) * Width() + B.words[n]);
                { lemma_hilo(hilo_B); }
            I(A) *  I(hilo_B);
        }
    }
    assert B.words[0..] == B.words;
}
