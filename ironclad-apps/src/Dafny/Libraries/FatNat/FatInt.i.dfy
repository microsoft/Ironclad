include "FatNatAddUnrolled.i.dfy"
include "FatNatDiv.i.dfy"
include "FatNatX86.i.dfy"

datatype FatInt = FatInt_ctor(
    negate : bool,
    value : array<int>);

//-////////////////////////////////////////////////////////////////////////////

function {:heap} WellformedFatInt(A:FatInt) : bool
    reads A.value;
{
    A.value != null
    && IsWordSeq(A.value[..])
    && (IsZeroValue(A.value[..]) ==> !A.negate) //- disallow redundant zero (-0)
}

//-////////////////////////////////////////////////////////////////////////////

function {:heap} FIV(A:FatInt) : int
    requires WellformedFatInt(A);
    reads A.value;
    ensures (FIV(A) < 0) <==> A.negate;
{
    lemma_2toX();
    lemma_BEDigitSeqToInt_bound(power2(32), A.value[..]);
    if (A.negate) then
        -BEWordSeqToInt(A.value[..])
    else
        BEWordSeqToInt(A.value[..])
}

method FatIntNegate(A:FatInt) returns (R:FatInt)
    requires WellformedFatInt(A);
    ensures WellformedFatInt(R);
    ensures FIV(R) == -FIV(A);
{
    var z := FatNatIsZero(A.value);
    if (z) {
        R := A;
    } else {
        R := FatInt_ctor(!A.negate, A.value);
    }
}

method FatIntAddSameSign(A:FatInt, B:FatInt) returns (R:FatInt)
    requires A.negate == B.negate;
    requires WellformedFatInt(A);
    requires WellformedFatInt(B);
    ensures WellformedFatInt(R);
    ensures FIV(A)+FIV(B) == FIV(R);
{
    ghost var As := A.value[..];
    ghost var Bs := B.value[..];
    var value:array<int> := FatNatAdd(A.value, B.value);
    ghost var Rs := value[..];
    assert BEWordSeqToInt(Rs) == BEWordSeqToInt(As) + BEWordSeqToInt(Bs);
    R := FatInt_ctor(A.negate, value);
    lemma_BEDigitSeqToInt_bound(power2(32), As);
    lemma_BEDigitSeqToInt_bound(power2(32), Bs);
    if (A.negate)
    {
        assert B.negate;
        calc {
            FIV(R);
            -BEWordSeqToInt(Rs);
            -(BEWordSeqToInt(As)+BEWordSeqToInt(Bs));
            -BEWordSeqToInt(As)-BEWordSeqToInt(Bs);
            FIV(A)+FIV(B);
        }
    }
    else
    {
        assert !B.negate;
        calc {
            FIV(R);
            BEWordSeqToInt(Rs);
            BEWordSeqToInt(As)+BEWordSeqToInt(Bs);
            FIV(A)+FIV(B);
        }
    }
}

method FatIntSubPos(A:FatInt, B:FatInt) returns (R:FatInt)
    requires !A.negate && !B.negate;
    requires WellformedFatInt(A);
    requires WellformedFatInt(B);
    ensures WellformedFatInt(R);
    ensures FIV(A)-FIV(B) == FIV(R);
{
    //- A - B ==> this is the interesting case
    ghost var As := A.value[..];
    ghost var Bs := B.value[..];
    var cmp := FatNatCompare(A.value,B.value);
    lemma_BEDigitSeqToInt_bound(power2(32), As);
    lemma_BEDigitSeqToInt_bound(power2(32), Bs);
    if (cmp.CmpLt?)
    {
        var value:array<int> := FatNatSub(B.value, A.value);
        R := FatInt_ctor(true, value);
    }
    else
    {
        var value:array<int> := FatNatSub(A.value, B.value);
        R := FatInt_ctor(false, value);
    }
}

method FatIntAdd(A:FatInt, B:FatInt) returns (R:FatInt)
    requires WellformedFatInt(A);
    requires WellformedFatInt(B);
    ensures WellformedFatInt(R);
    ensures FIV(A)+FIV(B) == FIV(R);
{
    var a_ref := A.value; //- do something real to A.value to convince dafyncc it's allocated
    var b_ref := B.value; //- do something real to B.value to convince dafyncc it's allocated

    if (A.negate == B.negate)
    {
        R := FatIntAddSameSign(A, B);
    }
    else if (A.negate)
    {
        assert !B.negate;
        var NA := FatIntNegate(A);
        var na_ref := NA.value; //- do something real to NA.value to convince dafnycc it's allocated
        R := FatIntSubPos(B,NA);
    }
    else
    {
        //- A - B
        var NB := FatIntNegate(B);
        var nb_ref := NB.value; //- do something real to NB.value to convince dafnycc it's allocated
        R := FatIntSubPos(A,NB);
    }
}

method FatIntSub(A:FatInt, B:FatInt) returns (R:FatInt)
    requires WellformedFatInt(A);
    requires WellformedFatInt(B);
    ensures WellformedFatInt(R);
    ensures FIV(A)-FIV(B) == FIV(R);
{
    var a_ref := A.value; //- do something real to A.value to convince dafyncc it's allocated
    var b_ref := B.value; //- do something real to B.value to convince dafyncc it's allocated

    if (B.negate)
    {
        //- -A - -B == -A + B
        //- A - -B == A + B
        var NB := FatIntNegate(B);
        var nb_ref := NB.value; //- do something real to NB.value to convince dafnycc it's allocated
        R := FatIntAdd(A, NB);
        calc {
            FIV(R);
            FIV(A) + FIV(NB);
            FIV(A) + -FIV(B);
            FIV(A) - FIV(B);
        }
    }
    else if (A.negate)
    {
        assert !B.negate;
        //- -A - B == - (A + B)
        ghost var As := A.value[..];
        ghost var Bs := B.value[..];
        var value:array<int> := FatNatAdd(A.value, B.value);
        lemma_BEDigitSeqToInt_bound(power2(32), As);
        lemma_BEDigitSeqToInt_bound(power2(32), Bs);
        R := FatInt_ctor(true, value);
    }
    else
    {
        R := FatIntSubPos(A, B);
    }
}

method FatIntCmp(A:FatInt, B:FatInt) returns (c:Cmp)
    requires WellformedFatInt(A);
    requires WellformedFatInt(B);
    ensures (c.CmpLt?) <==> (FIV(A)  < FIV(B));
    ensures (c.CmpEq?) <==> (FIV(A) == FIV(B));
    ensures (c.CmpGt?) <==> (FIV(A)  > FIV(B));
{
    var a_ref := A.value; //- do something real to A.value to convince dafyncc it's allocated
    var b_ref := B.value; //- do something real to B.value to convince dafyncc it's allocated

    if (A.negate)
    {
        if (!B.negate)
        {    //- -A, B
            c := CmpLt;
            assert FIV(A) < 0 <= FIV(B);
        }
        else
        {    //- -A,-B
            var nc := FatNatCompare(A.value,B.value);
            if (nc.CmpEq?)
            {
                c := CmpEq;
            }
            else if (nc.CmpLt?)
            {
                c := CmpGt;
            }
            else
            {
                c := CmpLt;
            }
        }
    }
    else
    {
        if (B.negate)
        {    //- A, -B
            c := CmpGt;
            assert FIV(A) >= 0 > FIV(B);
        }
        else
        {    //- A, B
            c := FatNatCompare(A.value,B.value);
        }
    }
}

method FatIntLt(A:FatInt, B:FatInt) returns (r:bool)
    requires WellformedFatInt(A);
    requires WellformedFatInt(B);
    ensures r <==> FIV(A)<FIV(B);
{
    var c := FatIntCmp(A,B);
    r := c.CmpLt?;
}

method FatIntLe(A:FatInt, B:FatInt) returns (r:bool)
    requires WellformedFatInt(A);
    requires WellformedFatInt(B);
    ensures r <==> FIV(A)<=FIV(B);
{
    var c := FatIntCmp(A,B);
    r := c.CmpLt? || c.CmpEq?;
}

method FatIntEq(A:FatInt, B:FatInt) returns (r:bool)
    requires WellformedFatInt(A);
    requires WellformedFatInt(B);
    ensures r <==> FIV(A)==FIV(B);
{
    var c := FatIntCmp(A,B);
    r := c.CmpEq?;
}

method FatIntGe(A:FatInt, B:FatInt) returns (r:bool)
    requires WellformedFatInt(A);
    requires WellformedFatInt(B);
    ensures r <==> FIV(A)>=FIV(B);
{
    var c := FatIntCmp(A,B);
    r := c.CmpGt? || c.CmpEq?;
}

method FatIntGt(A:FatInt, B:FatInt) returns (r:bool)
    requires WellformedFatInt(A);
    requires WellformedFatInt(B);
    ensures r <==> FIV(A)>FIV(B);
{
    var c := FatIntCmp(A,B);
    r := c.CmpGt?;
}

method FatIntMul(A:FatInt, B:FatInt) returns (R:FatInt)
    requires WellformedFatInt(A);
    requires WellformedFatInt(B);
    ensures WellformedFatInt(R);
    ensures FIV(A)*FIV(B) == FIV(R);
{
    var a_ref := A.value; //- do something real to A.value to convince dafyncc it's allocated
    var b_ref := B.value; //- do something real to B.value to convince dafyncc it's allocated

    ghost var As := A.value[..];
    ghost var Bs := B.value[..];
    lemma_BEDigitSeqToInt_bound(power2(32), As);
    lemma_BEDigitSeqToInt_bound(power2(32), Bs);

    if ((A.negate && B.negate)
        || (!A.negate && !B.negate))
    {
        var value:array<int> := FatNatMul(A.value, B.value);
        ghost var Rs := value[..];
        R := FatInt_ctor(false, value);

        if (A.negate)
        {
            calc {
                FIV(R);
                BEWordSeqToInt(Rs);
                BEWordSeqToInt(As) * BEWordSeqToInt(Bs);
                    { lemma_mul_cancels_negatives(BEWordSeqToInt(As), BEWordSeqToInt(Bs)); }
                (-BEWordSeqToInt(As)) * (-BEWordSeqToInt(Bs));
                FIV(A) * FIV(B);
            }
        }
        else
        {
            calc {
                FIV(R);
                BEWordSeqToInt(Rs);
                BEWordSeqToInt(As) * BEWordSeqToInt(Bs);
                FIV(A) * FIV(B);
            }
        }
    }
    else //- if ((!A.negate && B.negate) || (A.negate && !B.negate))
    {
        var za := FatNatIsZero(A.value);
        var zb := FatNatIsZero(B.value);
        assert za <==> (BEWordSeqToInt(As)==0);
        if ((B.negate && za) || (A.negate && zb))
        {
            
            var Z := FatNatZero();
            R := FatInt_ctor(false, Z);
            lemma_mul_basics_forall();
        }
        else
        {
            var value:array<int> := FatNatMul(A.value, B.value);
            ghost var Rs := value[..];
            R := FatInt_ctor(true, value);

            calc ==> {
                !IsZeroValue(As) && !IsZeroValue(Bs);
                BEWordSeqToInt(As)!=0 && BEWordSeqToInt(Bs)!=0;
                    { lemma_mul_nonzero_forall(); }
                BEWordSeqToInt(As)*BEWordSeqToInt(Bs) != 0;
                BEWordSeqToInt(Rs) != 0;
                !IsZeroValue(Rs);
                WellformedFatInt(R);
            }

            if (A.negate)
            {
                calc {
                    FIV(R);
                    -BEWordSeqToInt(Rs);
                    -(BEWordSeqToInt(As) * BEWordSeqToInt(Bs));
                        { lemma_mul_properties(); }
                    (-BEWordSeqToInt(As)) * BEWordSeqToInt(Bs);
                    FIV(A) * FIV(B);
                }
            }
            else
            {
                calc {
                    FIV(R);
                    -BEWordSeqToInt(Rs);
                    -(BEWordSeqToInt(As) * BEWordSeqToInt(Bs));
                        { lemma_mul_properties(); }
                    BEWordSeqToInt(As) * (-(BEWordSeqToInt(Bs)));
                    FIV(A) * FIV(B);
                }
            }
        }
    }
}

method FatIntDiv(N:FatInt, D:FatInt) returns (Q:FatInt, R:FatInt)
    requires WellformedFatInt(N);
//-    requires N.value.Length < power2(27);
    requires WellformedFatInt(D);
    requires BEWordSeqToInt(D.value[..])!=0;

    requires FIV(D) >= 0;
    ensures WellformedFatInt(Q);
    ensures WellformedFatInt(R);
    ensures 0 <= FIV(R) < FIV(D);    //- negative D inverts this condition.
    ensures FIV(Q)*FIV(D) + FIV(R) == FIV(N);
    ensures FIV(N) / FIV(D) == FIV(Q);
    ensures FIV(N) % FIV(D) == FIV(R);
{
    var n_ref := N.value; //- do something real to N.value to convince dafyncc it's allocated
    var d_ref := D.value; //- do something real to D.value to convince dafyncc it's allocated


//-    if (D.negate)
//-    {
//-        var q:BigNat,r:BigNat := BigNatDiv(N, FatIntNegate(D));
//-        Q := FatInt_ctor(true, q);
//-        R := FatInt_ctor(false, r);
//-    }

    ghost var Ns := N.value[..];
    ghost var Nv := BEWordSeqToInt(Ns);
    ghost var Ds := D.value[..];
    ghost var Dv := BEWordSeqToInt(Ds);
    var q:array<int>,r:array<int> := FatNatDiv(N.value, D.value);
    ghost var Qs := q[..];
    ghost var Qv := BEWordSeqToInt(Qs);
    ghost var Rs := r[..];
    ghost var Rv := BEWordSeqToInt(Rs);

    var zr := FatNatIsZero(r);
    if (N.negate && !zr)
    {
        var one := MakeBELiteralArray(1);
        ghost var Ones := one[..];
        ghost var Onev := BEWordSeqToInt(Ones);

        var q' := FatNatAdd(q, one);
        ghost var Q's := q'[..];
        ghost var Q'v := BEWordSeqToInt(Q's);
        Q := FatInt_ctor(true, q');
        lemma_BEDigitSeqToInt_bound(power2(32), Qs);
        var r' := FatNatSub(D.value, r);
        ghost var R's := r'[..];
        ghost var R'v := BEWordSeqToInt(R's);
        R := FatInt_ctor(false, r');
        calc ==> {
            true;
            0 <= R'v < Dv;
            0 <= FIV(R) < FIV(D);
        }
        calc ==> {
            true;
            Dv*Qv + Rv == Nv;
                { lemma_mul_is_commutative_forall(); }
            Qv*Dv + Rv == Nv;
            (Q'v-1)*Dv + (Dv - R'v) == Nv;
            { lemma_mul_is_distributive_forall(); }
            { lemma_mul_is_mul_boogie(1, Dv); }
            Q'v*Dv - Dv + (Dv - R'v) == Nv;
            Q'v*Dv - R'v == Nv;
            { lemma_mul_unary_negation(Q'v, Dv); }
            (-Q'v)*Dv + R'v == -Nv;
            FIV(Q)*FIV(D) + FIV(R) == FIV(N);
        }
    }
    else
    {
        var zq := FatNatIsZero(q);
        if (N.negate && zq)
        {
            calc ==> {
                true;
                Dv*Qv + Rv == Nv;
                    { lemma_mul_is_commutative_forall(); }
                Qv*Dv + Rv == Nv;
                Qv*Dv == Nv;
                    { lemma_mul_is_mul_boogie(0, Dv); }
                0*Dv == Nv;
                false;
            }
        }
        Q := FatInt_ctor(N.negate, q);
        R := FatInt_ctor(false, r);
        calc ==> {
            0 <= Rv < Dv;
            0 <= FIV(R) < FIV(D);
        }
        if (N.negate)
        {
            calc ==> {
                true;
                Dv*Qv + Rv == Nv;
                    { lemma_mul_is_commutative_forall(); }
                Qv*Dv + Rv == Nv;
                Qv*Dv == Nv;
                { lemma_mul_unary_negation(Qv, Dv); }
                (-Qv)*Dv == -Nv;
                FIV(Q)*FIV(D) == FIV(N);
                FIV(Q)*FIV(D) + FIV(R) == FIV(N);
            }
        }
        else
        {
            calc ==> {
                true;
                Dv*Qv + Rv == Nv;
                    { lemma_mul_is_commutative_forall(); }
                Qv*Dv + Rv == Nv;
                FIV(Q)*FIV(D) + FIV(R) == FIV(N);
            }
        }
    }
    lemma_fundamental_div_mod_converse(FIV(N), FIV(D), FIV(Q), FIV(R));
}

method MakeSmallLiteralFatInt(x:nat) returns (f:FatInt)
    requires x < Width();
    ensures WellformedFatInt(f);
    ensures FIV(f)==x;
{
    var a;
    if (x==0) {
        a := FatNatZero();
    } else {
        a := MakeBELiteralArray(x);
    }
    f := FatInt_ctor(false, a);
}

method CanonicalizeFatInt(f:FatInt) returns (na:FatInt)
    requires WellformedFatInt(f);
    ensures WellformedFatInt(na);
    ensures FIV(f) == FIV(na);
    ensures na.value.Length <= f.value.Length;
    ensures IsCanonicalDigitSeq(power2(32), na.value[..]);
{
    var fvc := CanonicalizeArray(f.value);
    na := FatInt_ctor(f.negate, fvc);
}
