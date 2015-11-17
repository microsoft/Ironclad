include "BigNatPartial.i.dfy"


//-///////////////////////////////////////////
//- local (legacy) names for some mul functions.

static lemma lemma_mul_annihilate(x:int)
    ensures x * 0 == 0 * x == 0;
{
    lemma_mul_basics_forall();
    lemma_mul_is_commutative(x, 0);
}

static lemma lemma_exponentiation(a:nat, b:nat)
    decreases b;
    ensures power2(a) * power2(b) == power2(a+b);
{
    lemma_power2_adds(a,b);
}

//-
//-///////////////////////////////////////////

//-///////////////////////////////////////////
//-


//
//-method Lt32(a:nat, b:nat) returns (r:bool)
//-    requires Word32(a);
//-    requires Word32(b);
//-    ensures r <==> (a < b);
//-
//-method Eq32(a:nat, b:nat) returns (r:bool)
//-    requires Word32(a);
//-    requires Word32(b);
//-    ensures r <==> (a==b);
//-
//-///////////////////////////////////////////


static lemma lemma_bignum_lower_bound(A:BigNat)
    decreases |A.words|;
    requires WellformedBigNat(A);
    requires nonzero(A);
    ensures 0 <= 32 * (|A.words|-1);
    ensures power2(32 * (|A.words|-1)) <= I(A);
{
    var alen:int := |A.words|;
    if (alen==1)
    {
        lemma_mul_nonnegative(32,(alen-1));
        calc
        {
            power2(32 * (|A.words|-1));
            power2(32 * 0);
                { lemma_mul_annihilate(32); }
            power2(0);
                { lemma_power2_0_is_1(); }
            1;
        }
        calc {
            1;
            <= { reveal_I(); }
            I(A);
        }
    }
    else
    {
        lemma_mul_nonnegative(32,(alen-1));
        assert 0<=32 *(alen-1);
        lemma_mul_nonnegative(32,(alen-2));
        assert 0<=32 *(alen-2);

        assert 0 < Width();
        assert Width() == power2(32);
        assert 0 <= lo(A);

        calc ==> {
            true;
                { lemma_bignum_lower_bound(hi(A)); }
            power2(32*(alen-2)) <= I(hi(A));
                { lemma_mul_left_inequality(Width(), power2(32*(alen-2)), I(hi(A))); }
            Width() * power2(32*(alen-2)) <= Width() * I(hi(A));
            power2(32) * power2(32*(alen-2)) <= Width() * I(hi(A));
                { lemma_power2_adds(32, 32*(alen-2)); }
            power2(32 + 32*(alen-2)) <= Width() * I(hi(A));
            power2(32*1 + 32*(alen-2)) <= Width() * I(hi(A));
                { lemma_mul_is_distributive_add(32, 1, alen-2); }
            power2(32 * (1 + (alen-2))) <= Width() * I(hi(A));
                //- additive math
            power2(32 * (alen-1)) <= Width() * I(hi(A));
                //- add 0<=lo(A) to each sides
            power2(32*(alen-1)) + 0 <= Width() * I(hi(A)) + lo(A);
                { lemma_hilo(A); lemma_mul_is_commutative(Width(), I(hi(A))); }
            power2(32*(alen-1)) <= I(A);
            power2(32 * (|A.words|-1)) <= I(A);
        }
    }
}

static lemma lemma_bignum_upper_bound(A:BigNat)
    decreases |A.words|;
    requires WellformedBigNat(A);
    ensures 0 <= 32 * |A.words|;
    ensures I(A) <= power2(32 * |A.words|)-1;
{
    var alen:int := |A.words|;
    lemma_mul_nonnegative(32,alen);
    if (alen==0)
    {
        calc ==>
        {
            true;
                { reveal_I(); }
            I(A) == 0;
                { lemma_power2_0_is_1(); }
            I(A) < power2(0);
                { lemma_mul_annihilate(32); }
            I(A) < power2(32*0);
            I(A) < power2(32*alen);
        }
    }
    else
    {
        lemma_mul_nonnegative(32,alen-1);
        calc ==> {
            true;
                { lemma_bignum_upper_bound(hi(A)); }
            I(hi(A)) <= power2(32*(alen-1)) - 1;
                { lemma_mul_left_inequality(Width(), I(hi(A)), power2(32*(alen-1))-1); }
            Width() * I(hi(A)) <= Width() * (power2(32*(alen-1)) - 1);
                { lemma_mul_is_distributive_sub(Width(), power2(32*(alen-1)), 1); }
            Width() * I(hi(A)) <= Width() * power2(32*(alen-1)) - Width() * 1;
            Width() * I(hi(A)) <= Width() * power2(32*(alen-1)) - Width();
            Width() * I(hi(A)) <= power2(32) * power2(32*(alen-1)) - Width();
                { lemma_exponentiation(32, 32*(alen-1)); }
            Width() * I(hi(A)) <= power2(32 + 32*(alen-1)) - Width();
            Width() * I(hi(A)) <= power2(32*1 + 32*(alen-1)) - Width();
                { lemma_mul_is_distributive_add(32, 1, alen-1); }
            Width() * I(hi(A)) <= power2(32*alen) - Width();
                //- add lo(A) <= power2(32)-1;
            Width() * I(hi(A)) + lo(A) <= power2(32*alen) - Width() + power2(32) - 1;
                { lemma_hilo(A); lemma_mul_is_commutative(Width(), I(hi(A))); }
            I(A) <= power2(32*alen) - 1;
        }
    }
}



static lemma lemma_word_bound(A:BigNat)
    requires WellformedBigNat(A);
    requires !zero(A);
    ensures 0<=32 * |A.words|;
    ensures I(A) < power2(32*|A.words|);
    ensures 0<=32*(|A.words|-1);
    ensures power2(32*(|A.words|-1)) <= I(A);
{
    lemma_bignum_lower_bound(A);
    lemma_bignum_upper_bound(A);
}

static lemma{:dafnycc_conservative_seq_triggers} behead(A:BigNat,i:int) returns (t:int, m:int, l:int)
    requires WellformedBigNat(A);
    requires |A.words| > 0;
    requires 0<=i<|A.words|;
    ensures 32*i >= 0;
    ensures 32*(i+1) >= 0;
    ensures I(A)==power2(32*(i+1)) * t + power2(32*i) * m + l;
    ensures WellformedBigNat(BigNat_ctor(A.words[i+1..]));
    ensures t == I(BigNat_ctor(A.words[i+1..]));
    ensures m == A.words[i];
    ensures 0 <= l < power2(32*i);
{
    calc ==> {
        0<=i;
            { lemma_mul_left_inequality(32,0,i); }
        32*0 <= 32*i;
            { lemma_mul_annihilate(32); }
        0 <= 32*i;
    }

    var ts:seq<int> := A.words[i+1..];
    var ms:seq<int> := A.words[i..i+1];
    var ls:seq<int> := A.words[0..i];

    var T:BigNat := BigNat_ctor(ts);
    assert WellformedBigNat(T);

    t := V(ts);
    lemma_V_I(T);
    assert V(ts) == I(T);

    m := V(ms);
    lemma_V_singleton(ms);
    assert m == A.words[i];

    l := V(ls);
    lemma_V_lower_bound(ls);
    assert 0 <= l;
    lemma_V_upper_bound(ls);
    assert l < power2(32*i);

    lemma_V_power(ls,ms);
    assert V(ls+ms) == power2(32*i) *V(ms)+V(ls);
    lemma_V_power(ls+ms,ts);
    assert V((ls+ms)+ts) == power2(32*(i+1))*V(ts) +V(ls+ms);
    assert V((ls+ms)+ts) == power2(32*(i+1))*V(ts) + power2(32*i) * V(ms) + V(ls);
    assert V((ls+ms)+ts) == power2(32*(i+1))*t+power2(32*i) * m +l;
    assert ls+(ms+ts) == A.words;
    assert (ls+ms)+ts == A.words;
    lemma_V_I(A);
    assert I(A) == V(A.words);
    assert I(A) == V((ls+ms)+ts);
    assert I(A) == power2(32*(i+1))*t+power2(32*i)*m+l;
}

datatype BNCmp = BNCmpLt | BNCmpEq | BNCmpGt;

static lemma BigNatLtEqualLengthOne_(A:BigNat, B:BigNat, i:int)
    decreases i;
    requires |A.words|==|B.words|;
    requires 0 <= i < |A.words|;
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    requires forall k:int :: i < k < |A.words| ==> A.words[k]==B.words[k];
    requires A.words[i] < B.words[i];
    ensures I(A)  < I(B);
{
    ghost var At,Am,Al := behead(A,i);
    ghost var Bt,Bm,Bl := behead(B,i);

    var Atop:seq<int> := A.words[i+1..];
    var Btop:seq<int> := B.words[i+1..];
    assert Atop == Btop;
    calc
    {
        At;
        I(BigNat_ctor(Atop));
        I(BigNat_ctor(Btop));
        Bt;
    }

    ghost var t:int := power2(32*(i+1));
    ghost var m:int := power2(32*i);

    assert I(B)==power2(32*(i+1)) * Bt + power2(32*i) * Bm + Bl;
    assert I(B)==t * Bt + m * Bm + Bl;

    calc ==>
    {
            //- behead
        I(A) == t * At + m * Am + Al;
            //- behead { Al <= k; }
        I(A) < t * At + m * Am + m;
            { lemma_mul_is_distributive_add(m,Am,1); }
        I(A) < t * At + m * (Am+1);
            { assert Am+1 <= Bm; lemma_mul_left_inequality(m,Am+1,Bm); }
        I(A) < t * Bt + m * Bm;
            //- behead { 0 <= Bl; }
        I(A) < t * Bt + m * Bm + Bl;
            //- behead
        I(A) < I(B);
    }
}

static lemma lemma_lt_equal_length(A:BigNat, B:BigNat)
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    requires |A.words|==|B.words|;
    requires !zero(A);
    requires A.words[|A.words|-1] < B.words[|A.words|-1];
    ensures I(A) < I(B);
{
    BigNatLtEqualLengthOne_(A, B, |A.words|-1);
}

static lemma BigNatLeEqualLengthOne_(A:BigNat, B:BigNat, i:int)
    decreases i;
    requires |A.words|==|B.words|;
    requires 0 <= i < |A.words|;
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    requires forall k:int :: i < k < |A.words| ==> A.words[k]==B.words[k];
    requires forall j:int :: 0 <= j <= i ==> A.words[j]<=B.words[j];
    ensures I(A) <= I(B);
{
    if (A.words[i] < B.words[i])
    {
        BigNatLtEqualLengthOne_(A, B, i);
        //- We've established inequality
    }
    else if (A.words[i] > B.words[i])
    {
        assert false;
    }
    else if (i > 0)
    {
        //- continue in the loop towards equality.
        BigNatLeEqualLengthOne_(A, B, i - 1);
    }
    else
    {
        lemma_BigNatEqEqualLength_(A,B);
    }
}

static lemma lemma_BigNatEqEqualLength_(A:BigNat, B:BigNat)
    requires |A.words|==|B.words|;
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    requires forall k:int :: 0 <= k < |A.words| ==> A.words[k]==B.words[k];
    ensures I(A) == I(B);
{
    calc ==> {
        A.words == B.words;
        A == B;
        I(A) == I(B);
    }
}

static method BigNatCmpEqualLength_(A:BigNat, B:BigNat, i:int) returns (c:BNCmp)
    requires |A.words|==|B.words|;
    requires 0 <= i < |A.words|;
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    requires forall k:int :: i < k < |A.words| ==> A.words[k]==B.words[k];
    ensures (c==BNCmpLt) <==> (I(A)  < I(B));
    ensures (c==BNCmpEq) <==> (I(A) == I(B));
    ensures (c==BNCmpGt) <==> (I(A)  > I(B));
{
    var n := i + 1;
    while (n > 0)
        invariant 0 <= n <= i + 1;
        invariant forall k:int :: n <= k < |A.words| ==> A.words[k]==B.words[k];
    {
        n := n - 1;
        if (A.words[n] < B.words[n])
        {
            BigNatLtEqualLengthOne_(A,B,n);
            c := BNCmpLt;
            return;
        }
        else if (A.words[n] > B.words[n])
        {
            BigNatLtEqualLengthOne_(B,A,n);
            c := BNCmpGt;
            return;
        }
    }
    c := BNCmpEq;
    lemma_BigNatEqEqualLength_(A,B);
}

static lemma lemma_cmp_inequal_length(A:BigNat, B:BigNat)
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    requires |A.words| < |B.words|;
    ensures I(A) < I(B);
{
    lemma_bignum_upper_bound(A);
    assert I(A) < power2(32 * (|A.words|));
    lemma_bignum_lower_bound(B);
    assert power2(32 * (|B.words|-1)) <= I(B);
    assert |A.words| <= |B.words|-1;
    lemma_mul_left_inequality(32, |A.words|, |B.words|-1);
    assert 32*|A.words| <= 32 * (|B.words|-1);
    lemma_power2_increases(32*|A.words|, 32 * (|B.words|-1));
    assert power2(32 * (|A.words|)) <= power2(32 * (|B.words|-1));
}

static lemma lemma_hi_decreases(A:BigNat)
    requires WellformedBigNat(A);
    ensures zero(A) || I(hi(A))<I(A);
    ensures zero(A) ==> zero(hi(A));
{
    if (zero(A))
    {
        assert zero(hi(A));
    }
    else
    {
        assert |hi(A).words| < |A.words|;
        lemma_cmp_inequal_length(hi(A), A);
    }
}

static method BigNatCmp(A:BigNat, B:BigNat) returns (c:BNCmp)
    decreases |A.words|;
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    ensures (c==BNCmpLt) <==> (I(A)  < I(B));
    ensures (c==BNCmpEq) <==> (I(A) == I(B));
    ensures (c==BNCmpGt) <==> (I(A)  > I(B));
{
    if (zero(A))
    {
        if (zero(B))
        {
            c := BNCmpEq;
        }
        else
        {
            c := BNCmpLt;
        }
    }
    else if (zero(B))
    {
        c := BNCmpGt;
    }
    else if (|A.words| < |B.words|)
    {
        lemma_cmp_inequal_length(A,B);
        c := BNCmpLt;
    }
    else if (|A.words| > |B.words|)
    {
        lemma_cmp_inequal_length(B,A);
        c := BNCmpGt;
    }
    else
    {
        c := BigNatCmpEqualLength_(A,B,|A.words|-1);
    }
}

static method BigNatLt(A:BigNat, B:BigNat) returns (r:bool)
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    ensures r <==> I(A)<I(B);
{
    var c := BigNatCmp(A,B);
    r := (c.BNCmpLt?);
}

static method BigNatLe(A:BigNat, B:BigNat) returns (r:bool)
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    ensures r <==> I(A)<=I(B);
{
    var c := BigNatCmp(A,B);
    r := (c.BNCmpLt?) || (c.BNCmpEq?);
}

static method BigNatEq(A:BigNat, B:BigNat) returns (r:bool)
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    ensures r <==> I(A)==I(B);
{
    var c := BigNatCmp(A,B);
    r := (c.BNCmpEq?);
}

static method BigNatGe(A:BigNat, B:BigNat) returns (r:bool)
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    ensures r <==> I(A)>=I(B);
{
    var c := BigNatCmp(A,B);
    r := (c.BNCmpGt?) || (c.BNCmpEq?);
}

static method BigNatGt(A:BigNat, B:BigNat) returns (r:bool)
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    ensures r <==> I(A)>I(B);
{
    var c := BigNatCmp(A,B);
    r := (c.BNCmpGt?);
}


static function method TestEqSmallLiteralBigNat_def(x:nat, X: BigNat) : bool
    requires x < Width();
    requires WellformedBigNat(X);
{
    if (zero(X)) then
        x==0
    else if |X.words|>1 then
        false
    else
        X.words[0]==x
}

static lemma lemma_TestEqSmallLiteralBigNat(x:nat, X: BigNat)
    requires x < Width();
    requires WellformedBigNat(X);
    ensures x==I(X) <==> TestEqSmallLiteralBigNat_def(x,X);
{
    if (zero(X))
    {
    }
    else if (|X.words|>1)
    {
        calc ==> {
            1 <= |X.words|-1;
                { lemma_mul_inequality_forall(); }
            1 *  32 <= (|X.words|-1) * 32;
                { lemma_mul_is_mul_boogie(1,32); }
            32 <= (|X.words|-1) * 32;
                { lemma_mul_is_commutative_forall(); }
            32 <= 32 * (|X.words|-1);
                { lemma_power2_increases(32, 32 * (|X.words|-1)); }
            power2(32) <= power2(32 * (|X.words|-1));
                { lemma_bignum_lower_bound(X); }
            Width() <= power2(32 * (|X.words|-1)) <= I(X);
        }

        assert x < Width();
    }
    else
    {
        assert |X.words|==1;
        calc {
            I(X);
                { reveal_I(); }
            I(BigNat_ctor(X.words[1..])) * Width()+X.words[0];
                { assert X.words[1..] == []; }
            I(BigNat_ctor([])) * Width()+X.words[0];
                { reveal_I(); }
            0 * Width()+X.words[0];
                { lemma_mul_basics_forall(); }
            X.words[0];
        }
    }
}

static function method TestEqSmallLiteralBigNat(x:nat, X: BigNat) : bool
    requires x < Width();
    requires WellformedBigNat(X);
    ensures x==I(X) <==> TestEqSmallLiteralBigNat(x,X);
{
    lemma_TestEqSmallLiteralBigNat(x, X);
    TestEqSmallLiteralBigNat_def(x, X)
}

static lemma lemma_le_equal_length(A:BigNat, B:BigNat)
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    requires |A.words|==|B.words|;
    requires !zero(A);
    requires forall i:nat :: i < |A.words| ==> A.words[i] <= B.words[i];
    ensures I(A) <= I(B);
{
    BigNatLeEqualLengthOne_(A, B, |A.words|-1);
}

