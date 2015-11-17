include "BigNatDiv.i.dfy"

datatype BigNum = BigNum_ctor(
    negate : bool,
    value : BigNat);

static function WellformedBigNum(A:BigNum) : bool
{
    WellformedBigNat(A.value)
        //- disallow redundant zero (-0)
    && (zero(A.value) ==> !A.negate)
}

static function BV(A:BigNum) : int
    requires WellformedBigNum(A);
    ensures (BV(A) < 0) <==> A.negate;
{
    if (A.negate) then
        -I(A.value)
    else
        I(A.value)
}

static function method BigNumNegate(A:BigNum) : BigNum
    requires WellformedBigNum(A);
    ensures WellformedBigNum(BigNumNegate(A));
    ensures BV(BigNumNegate(A)) == -BV(A);
{
    if (zero(A.value)) then
        A
    else
        BigNum_ctor(!A.negate, A.value)
}

static method BigNumAddSameSign(A:BigNum, B:BigNum) returns (R:BigNum)
    requires A.negate == B.negate;
    requires WellformedBigNum(A);
    requires WellformedBigNum(B);
    ensures WellformedBigNum(R);
    ensures BV(A)+BV(B) == BV(R);
{
    var value:BigNat := BigNatAdd(A.value, B.value);
    assert I(value) == I(A.value) + I(B.value);
    R := BigNum_ctor(A.negate, value);
    if (A.negate)
    {
        assert B.negate;
        calc {
            BV(R);
            -I(R.value);
            -(I(A.value)+I(B.value));
            -I(A.value)-I(B.value);
            BV(A)+BV(B);
        }
    }
    else
    {
        assert !B.negate;
        calc {
            BV(R);
            I(R.value);
            I(A.value)+I(B.value);
            BV(A)+BV(B);
        }
    }
}

static method BigNumSubPos(A:BigNum, B:BigNum) returns (R:BigNum)
    requires !A.negate && !B.negate;
    requires WellformedBigNum(A);
    requires WellformedBigNum(B);
    ensures WellformedBigNum(R);
    ensures BV(A)-BV(B) == BV(R);
{
    //- A - B ==> this is the interesting case
    var negate:bool := BigNatLt(A.value,B.value);
    if (negate)
    {
        assert I(B.value) > I(A.value);
        var value:BigNat := BigNatSub(B.value, A.value);
        R := BigNum_ctor(negate, value);
        calc {
            BV(R);
            -I(value);
            -(I(B.value)-I(A.value));
            I(A.value)-I(B.value);
            BV(A) - BV(B);
        }
    }
    else
    {
        assert I(B.value) <= I(A.value);
        var value:BigNat := BigNatSub(A.value, B.value);
        R := BigNum_ctor(negate, value);
        calc {
            BV(R);
            I(value);
            I(A.value)-I(B.value);
            BV(A) - BV(B);
        }
    }
}

static method BigNumAdd(A:BigNum, B:BigNum) returns (R:BigNum)
    requires WellformedBigNum(A);
    requires WellformedBigNum(B);
    ensures WellformedBigNum(R);
    ensures BV(A)+BV(B) == BV(R);
{
    if (A.negate == B.negate)
    {
        R := BigNumAddSameSign(A, B);
    }
    else if (A.negate)
    {
        assert !B.negate;
        R := BigNumSubPos(B,BigNumNegate(A));
        calc {
            BV(R);
            BV(B) - BV(BigNumNegate(A));
            BV(B) - (-BV(A));
            BV(B) + BV(A);
            BV(A) + BV(B);
        }
    }
    else
    {
        //- A - B
        R := BigNumSubPos(A,BigNumNegate(B));
        calc {
            BV(R);
            BV(A)-BV(BigNumNegate(B));
            BV(A)-(-BV(B));
            BV(A)+BV(B);
        }
    }
}

static method BigNumSub(A:BigNum, B:BigNum) returns (R:BigNum)
    requires WellformedBigNum(A);
    requires WellformedBigNum(B);
    ensures WellformedBigNum(R);
    ensures BV(A)-BV(B) == BV(R);
{
    if (B.negate)
    {
        //- -A - -B == -A + B
        //- A - -B == A + B
        R := BigNumAdd(A, BigNumNegate(B));
        calc {
            BV(R);
            BV(A) + BV(BigNumNegate(B));
            BV(A) + -BV(B);
            BV(A) - BV(B);
        }
    }
    else if (A.negate)
    {
        assert !B.negate;
        //- -A - B == - (A + B)
        var value:BigNat := BigNatAdd(A.value, B.value);
        R := BigNum_ctor(true, value);
        calc {
            BV(R);
            -I(value);
            -(I(A.value) + I(B.value));
            -I(A.value) - I(B.value);
            BV(A) - BV(B);
        }
    }
    else
    {
        R := BigNumSubPos(A, B);
    }
}

static method BigNumCmp(A:BigNum, B:BigNum) returns (c:BNCmp)
    requires WellformedBigNum(A);
    requires WellformedBigNum(B);
    ensures (c==BNCmpLt) <==> (BV(A)  < BV(B));
    ensures (c==BNCmpEq) <==> (BV(A) == BV(B));
    ensures (c==BNCmpGt) <==> (BV(A)  > BV(B));
{
    if (A.negate)
    {
        if (!B.negate)
        {    //- -A, B
            c := BNCmpLt;
            assert BV(A) < 0 <= BV(B);
        }
        else
        {    //- -A,-B
            var nc := BigNatCmp(A.value,B.value);
            if (nc.BNCmpEq?)
            {
                c := BNCmpEq;
                assert BV(A)==-I(A.value)==-I(B.value)==BV(B);
            }
            else if (nc.BNCmpLt?)
            {
                c := BNCmpGt;
                assert BV(A)==-I(A.value) > -I(B.value)==BV(B);
            }
            else
            {
                c := BNCmpLt;
                assert BV(A)==-I(A.value) < -I(B.value)==BV(B);
            }
        }
    }
    else
    {
        if (B.negate)
        {    //- A, -B
            c := BNCmpGt;
            assert BV(A) >= 0 > BV(B);
        }
        else
        {    //- A, B
            c := BigNatCmp(A.value,B.value);
            if (c==BNCmpEq)
            {
                assert BV(A)==I(A.value)==I(B.value)==BV(B);
            }
            else if (c==BNCmpLt)
            {
                assert BV(A)==I(A.value)<I(B.value)==BV(B);
            }
            else
            {
                assert c==BNCmpGt;
                assert BV(A)==I(A.value)>I(B.value)==BV(B);
            }
        }
    }
}

static method BigNumLt(A:BigNum, B:BigNum) returns (r:bool)
    requires WellformedBigNum(A);
    requires WellformedBigNum(B);
    ensures r <==> BV(A)<BV(B);
{
    var c := BigNumCmp(A,B);
    r := c.BNCmpLt?;
}

static method BigNumLe(A:BigNum, B:BigNum) returns (r:bool)
    requires WellformedBigNum(A);
    requires WellformedBigNum(B);
    ensures r <==> BV(A)<=BV(B);
{
    var c := BigNumCmp(A,B);
    r := c.BNCmpLt? || c.BNCmpEq?;
}

static method BigNumEq(A:BigNum, B:BigNum) returns (r:bool)
    requires WellformedBigNum(A);
    requires WellformedBigNum(B);
    ensures r <==> BV(A)==BV(B);
{
    var c := BigNumCmp(A,B);
    r := c.BNCmpEq?;
}

static method BigNumGe(A:BigNum, B:BigNum) returns (r:bool)
    requires WellformedBigNum(A);
    requires WellformedBigNum(B);
    ensures r <==> BV(A)>=BV(B);
{
    var c := BigNumCmp(A,B);
    r := c.BNCmpGt? || c.BNCmpEq?;
}

static method BigNumGt(A:BigNum, B:BigNum) returns (r:bool)
    requires WellformedBigNum(A);
    requires WellformedBigNum(B);
    ensures r <==> BV(A)>BV(B);
{
    var c := BigNumCmp(A,B);
    r := c.BNCmpGt?;
}

method BigNumMul(A:BigNum, B:BigNum) returns (R:BigNum)
    requires WellformedBigNum(A);
    requires WellformedBigNum(B);
    ensures WellformedBigNum(R);
    ensures BV(A)*BV(B) == BV(R);
{
    if ((A.negate && B.negate)
        || (!A.negate && !B.negate))
    {
        var value:BigNat := BigNatMul(A.value, B.value);
        R := BigNum_ctor(false, value);

        if (A.negate)
        {
            calc {
                BV(R);
                I(value);
                I(A.value) * I(B.value);
                    { lemma_mul_cancels_negatives(I(A.value), I(B.value)); }
                (-I(A.value)) * (-I(B.value));
                BV(A) * BV(B);
            }
        }
        else
        {
            calc {
                BV(R);
                I(value);
                I(A.value) * I(B.value);
                BV(A) * BV(B);
            }
        }
    }
    else //- if ((!A.negate && B.negate) || (A.negate && !B.negate))
    {
        if ((B.negate && zero(A.value))
            || (A.negate && zero(B.value)))
        {
            
            R := BigNum_ctor(false, BigNatZero());
            if (zero(A.value))
            {
                assert I(A.value)==0;
                calc {
                    BV(A) * BV(B);
                    I(A.value) * -I(B.value);
                    0 * (-I(B.value));
                        { lemma_mul_basics_forall(); }
                    0;
                    I(BigNatZero());
                    BV(R);
                }
            }
            else
            {
                assert I(B.value)==0;
                calc {
                    BV(A) * BV(B);
                    (-I(A.value)) * I(B.value);
                    (-I(A.value)) * 0;
                        { lemma_mul_basics_forall(); }
                    0;
                    I(BigNatZero());
                    BV(R);
                }
            }
        }
        else
        {
            var value:BigNat := BigNatMul(A.value, B.value);
            R := BigNum_ctor(true, value);

            calc ==> {
                !zero(A.value) && !zero(B.value);
                I(A.value)!=0 && I(B.value)!=0;
                    { lemma_mul_nonzero_forall(); }
                I(A.value)*I(B.value) != 0;
                I(value) != 0;
                !zero(value);
                WellformedBigNum(R);
            }

            if (A.negate)
            {
                calc {
                    BV(R);
                    -I(value);
                    -(I(A.value) * I(B.value));
                        { lemma_mul_properties(); }
                    (-I(A.value)) * I(B.value);
                    BV(A) * BV(B);
                }
            }
            else
            {
                calc {
                    BV(R);
                    -I(value);
                    -(I(A.value) * I(B.value));
                        { lemma_mul_properties(); }
                    I(A.value) * (-(I(B.value)));
                    BV(A) * BV(B);
                }
            }
        }
    }
}

static predicate ModestBigNumWords(A:BigNum)
{
    WellformedBigNum(A)
    && ModestBigNatWords(A.value)
}

method BigNumDiv(N:BigNum, D:BigNum) returns (Q:BigNum, R:BigNum)
    requires WellformedBigNum(N);
    requires WellformedBigNum(D);
    requires nonzero(D.value);

    requires BV(D) >= 0;
    ensures WellformedBigNum(Q);
    ensures WellformedBigNum(R);
    ensures 0 <= BV(R) < BV(D);    //- negative D inverts this condition.
    ensures BV(Q)*BV(D) + BV(R) == BV(N);
    ensures BV(N) / BV(D) == BV(Q);
    ensures BV(N) % BV(D) == BV(R);
{

//-    if (D.negate)
//-    {
//-        var q:BigNat,r:BigNat := BigNatDiv(N, BigNumNegate(D));
//-        Q := BigNum_ctor(true, q);
//-        R := BigNum_ctor(false, r);
//-    }

    var q:BigNat,r:BigNat := BigNatDivImmodest(N.value, D.value);
    if (N.negate && !zero(r))
    {
        var one := MakeSmallLiteralBigNat(1);
        q := BigNatAdd(q, one);
        Q := BigNum_ctor(true, q);
        r := BigNatSub(D.value, r);
        R := BigNum_ctor(false, r);
        calc ==> {
            0 <= I(r) < I(D.value);
            0 <= BV(R) < BV(D);
        }
        calc ==> {
            (I(q)-1)*I(D.value) + (I(D.value) - I(r)) == I(N.value);
            { lemma_mul_is_distributive_forall(); }
            { lemma_mul_is_mul_boogie(1, I(D.value)); }
            I(q)*I(D.value) - I(D.value) + (I(D.value) - I(r)) == I(N.value);
            I(q)*I(D.value) - I(r) == I(N.value);
            { lemma_mul_unary_negation(I(q), I(D.value)); }
            (-I(q))*I(D.value) + I(r) == -I(N.value);
            BV(Q)*BV(D) + BV(R) == BV(N);
        }
    }
    else
    {
        if (N.negate && zero(q))
        {
            calc {
                I(q)*I(D.value) + I(r) == I(N.value);
                { lemma_mul_is_mul_boogie(0, I(D.value)); }
                0*I(D.value) + 0 == I(N.value);
                false;
            }
        }
        Q := BigNum_ctor(N.negate, q);
        R := BigNum_ctor(false, r);
        calc ==> {
            0 <= I(r) < I(D.value);
            0 <= BV(R) < BV(D);
        }
        if (N.negate)
        {
            calc ==> {
                I(q)*I(D.value) + I(r) == I(N.value);
                I(q)*I(D.value) == I(N.value);
                { lemma_mul_unary_negation(I(q), I(D.value)); }
                (-I(q))*I(D.value) == -I(N.value);
                BV(Q)*BV(D) == BV(N);
                BV(Q)*BV(D) + BV(R) == BV(N);
            }
        }
        else
        {
            calc ==> {
                I(q)*I(D.value) + I(r) == I(N.value);
                BV(Q)*BV(D) + BV(R) == BV(N);
            }
        }
    }
    lemma_fundamental_div_mod_converse(BV(N), BV(D), BV(Q), BV(R));
}

static function method MakeSmallLiteralBigNum_def(x:nat) : BigNum
    requires x < Width();
    ensures WellformedBigNum(MakeSmallLiteralBigNum_def(x));
{
    if (x==0) then
        BigNum_ctor(false, BigNat_ctor([]))
    else
        BigNum_ctor(false, BigNat_ctor([x]))
}

static lemma lemma_MakeSmallLiteralBigNum(x:nat)
    requires x < Width();
    ensures BV(MakeSmallLiteralBigNum_def(x)) == x;
{
    var R:BigNum := MakeSmallLiteralBigNum_def(x);
    assert WellformedBigNum(R);
    assert WellformedBigNat(R.value);
    if (x==0)
    {
        assert zero(R.value);
        assert BV(R) == 0;
    }
    else
    {
        assert R.value.words == [x];
        calc {
            I(R.value);
                { reveal_I(); }
            I(BigNat_ctor(R.value.words[1..]))*Width()+R.value.words[0];
                { assert R.value.words[1..] == []; }
            I(BigNat_ctor([]))*Width()+R.value.words[0];
                {
                    reveal_I();
                    lemma_mul_basics_forall();
                }
            R.value.words[0];
            x;
        }
        assert I(R.value) == x;
        assert BV(R) == x;
    }
}

static function method MakeSmallLiteralBigNum(x:nat) : BigNum
    requires x < Width();
    ensures WellformedBigNum(MakeSmallLiteralBigNum(x));
    ensures BV(MakeSmallLiteralBigNum(x))==x;
{
    lemma_MakeSmallLiteralBigNum(x);
    MakeSmallLiteralBigNum_def(x)
}
