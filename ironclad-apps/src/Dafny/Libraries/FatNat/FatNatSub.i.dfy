include "FatNatCommon.i.dfy"

predicate FNSubRelation_local(pv:int, a:seq<int>, b:seq<int>, c:seq<int>, carryin:seq<int>, i:int)
    requires 1<pv;
    requires IsDigitSeq(pv, a);
    requires IsDigitSeq(pv, b);
    requires IsDigitSeq(pv, c);
    requires IsDigitSeq(2, carryin);
    requires 0 <= i < MaxLen3(a,b,c);
{
    DigitAt(carryin,i+1) * pv + DigitAt(a,i)
        == DigitAt(b,i) + DigitAt(c,i) + DigitAt(carryin,i)
}

predicate FNSubRelation(pv:int, a:seq<int>, b:seq<int>, c:seq<int>, carryin:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, a);
    requires IsDigitSeq(pv, b);
    requires IsDigitSeq(pv, c);
    requires IsDigitSeq(2, carryin);
{
    forall i :: 0 <= i < MaxLen3(a,b,c)
        ==> FNSubRelation_local(pv, a, b, c, carryin, i)
}

lemma lemma_FNSubtraction_recursive(pv:int, a:seq<int>, b:seq<int>, c:seq<int>, carryin:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, a);
    requires IsDigitSeq(pv, b);
    requires IsDigitSeq(pv, c);
    requires IsDigitSeq(2, carryin);
    requires |a| == |b| == |c| == |carryin| - 1;
    requires FNSubRelation(pv, a, b, c, carryin);
    ensures DigitAt(carryin,|a|) * power(pv,|a|) + BEDigitSeqToInt(pv,a)
        == BEDigitSeqToInt(pv,b) + BEDigitSeqToInt(pv,c) + DigitAt(carryin,0);
    decreases |a|;
{
    var ml := |a|;
    if (ml==0)
    {
        reveal_BEDigitSeqToInt_private();
        calc {
            DigitAt(carryin,|a|) * power(pv,|a|) + BEDigitSeqToInt(pv,a);
            DigitAt(carryin,0) * power(pv,0) + 0;
                { lemma_power_0(pv); }
            mul(DigitAt(carryin,0), 1) + 0;
                { lemma_mul_basics_forall(); }
            0 + 0 + DigitAt(carryin,0);
            BEDigitSeqToInt(pv,b) + BEDigitSeqToInt(pv,c) + DigitAt(carryin,0);
        }
    }
    else
    {
        var sa := a[..ml-1];
        var sb := b[..ml-1];
        var sc := c[..ml-1];
        var scarryin := carryin[..ml];

        forall (i | 0 <= i < MaxLen3(sa,sb,sc))
            ensures FNSubRelation_local(pv, sa, sb, sc, scarryin, i);
        {
            reveal_BEDigitSeqToInt_private();
            assert FNSubRelation_local(pv, a, b, c, carryin, i+1);    //- OBSERVE
        }
        assert FNSubRelation(pv, sa, sb, sc, scarryin);

        var nextcarry := DigitAt(carryin, 1);
        calc {
            DigitAt(carryin,|a|) * power(pv,|a|) + BEDigitSeqToInt(pv,a);
                { reveal_BEDigitSeqToInt_private();
                assert a[0..ml-1]==sa; }
            DigitAt(carryin,|a|) * power(pv,|a|)
                + BEDigitSeqToInt(pv,sa) * pv + DigitAt(a, 0);
            DigitAt(carryin,|a|)*power(pv,|sa|+1)
                + BEDigitSeqToInt(pv,sa)*pv + DigitAt(a,0);
                { lemma_power_adds(pv, |sa|, 1); }
            DigitAt(carryin,|a|)*(power(pv,|sa|)*power(pv,1))
                + BEDigitSeqToInt(pv,sa)*pv + DigitAt(a,0);
                { lemma_power_1(pv); }
            DigitAt(carryin,|a|)*(power(pv,|sa|)*pv)
                + BEDigitSeqToInt(pv,sa)*pv + DigitAt(a,0);
            DigitAt(scarryin,|sa|)*(power(pv,|sa|)*pv)
                + BEDigitSeqToInt(pv,sa)*pv + DigitAt(a,0);
                { lemma_mul_is_distributive_forall(); lemma_mul_is_commutative_forall(); lemma_mul_is_associative_forall(); }
            (DigitAt(scarryin,|sa|) * power(pv,|sa|) + BEDigitSeqToInt(pv,sa))*pv
                + DigitAt(a,0);
                { lemma_FNSubtraction_recursive(pv, sa, sb, sc, scarryin); }
            (BEDigitSeqToInt(pv,sb) + BEDigitSeqToInt(pv,sc) + DigitAt(scarryin,0))*pv
                + DigitAt(a,0);
            (BEDigitSeqToInt(pv,sb) + BEDigitSeqToInt(pv,sc) + DigitAt(carryin,1))*pv
                + DigitAt(a,0);
                { lemma_mul_is_distributive_forall(); lemma_mul_is_commutative_forall(); }
            BEDigitSeqToInt(pv,sb)*pv + BEDigitSeqToInt(pv,sc)*pv
                + DigitAt(carryin,1)*pv + DigitAt(a,0);
                { assert FNSubRelation_local(pv, a, b, c, carryin, 0); }
            BEDigitSeqToInt(pv,sb)*pv + BEDigitSeqToInt(pv,sc)*pv
                + DigitAt(b,0) + DigitAt(c,0) + DigitAt(carryin,0);
                { reveal_BEDigitSeqToInt_private();
                assert b[0..ml-1]==sb;
                assert c[0..ml-1]==sc; }
            BEDigitSeqToInt(pv,b) + BEDigitSeqToInt(pv,c) + DigitAt(carryin,0);
        }
    }
}

lemma lemma_FNSubtraction(pv:int, a:seq<int>, b:seq<int>, c:seq<int>, carryin:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, a);
    requires IsDigitSeq(pv, b);
    requires IsDigitSeq(pv, c);
    requires IsDigitSeq(2, carryin);
    requires |carryin| <= MaxLen3(a,b,c)+1;
    requires FNSubRelation(pv, a, b, c, carryin);
    ensures DigitAt(carryin,MaxLen3(a,b,c)) * power(pv,MaxLen3(a,b,c)) + BEDigitSeqToInt(pv,a)
        == BEDigitSeqToInt(pv,b) + BEDigitSeqToInt(pv,c) + DigitAt(carryin,0);
{
    var ml := MaxLen3(a,b,c);
    var la := Stretch(a, ml);
    var lb := Stretch(b, ml);
    var lc := Stretch(c, ml);
    var lcarryin := Stretch(carryin, ml+1);

    forall (i | 0 <= i < MaxLen3(a,b,c))
        ensures FNSubRelation_local(pv, la, lb, lc, lcarryin, i);
    {
        assert FNSubRelation_local(pv, a, b, c, carryin, i);    //- OBSERVE
    }

    assert FNSubRelation(pv, la, lb, lc, lcarryin);
    lemma_FNSubtraction_recursive(pv, la, lb, lc, lcarryin);
    lemma_LeadingZeros(pv, a, la);
    lemma_LeadingZeros(pv, b, lb);
    lemma_LeadingZeros(pv, c, lc);

    calc {
        DigitAt(carryin,MaxLen3(a,b,c)) * power(pv,MaxLen3(a,b,c)) + BEDigitSeqToInt(pv,a);
        DigitAt(carryin,|la|) * power(pv,|la|) + BEDigitSeqToInt(pv,la);
        BEDigitSeqToInt(pv,lb) + BEDigitSeqToInt(pv,lc) + DigitAt(carryin,0);
        BEDigitSeqToInt(pv,b) + BEDigitSeqToInt(pv,c) + DigitAt(carryin,0);
    }
}

//- Need to be able to talk about just the assembled part of c.
predicate FNSubRelation_inductive(pv:int, a:seq<int>, b:seq<int>, c:seq<int>, carryin:seq<int>, j:int)
    requires 1<pv;
    requires IsDigitSeq(pv, a);
    requires IsDigitSeq(pv, b);
    requires 0 <= j <= |c|;
    requires IsDigitSeq(pv, c[|c|-j..]);
    requires IsDigitSeq(2, carryin);
    requires |carryin| >= j;
{
    forall i :: 0 <= i < j
        ==> FNSubRelation_local(pv, a, b, c[|c|-j..], carryin, i)
}

lemma lemma_SubRelationInduction(pv:int, a:seq<int>, b:seq<int>, c:seq<int>, carryin:seq<int>, j:int)
    requires 1<pv;
    requires IsDigitSeq(pv, a);
    requires IsDigitSeq(pv, b);
    requires j == MaxLen3(a,b,c);
    requires j == |c|;
    requires IsDigitSeq(pv, c[|c|-j..]);
    requires IsDigitSeq(2, carryin);
    requires |carryin| == j+1;
    requires FNSubRelation_inductive(pv, a, b, c, carryin, j);
//-    requires DigitAt(carryin, 0) == 0;
    ensures IsDigitSeq(pv, c);
    ensures FNSubRelation(pv, a, b, c, carryin);
{
    forall (i | 0 <= i < |c|)
        ensures 0 <= c[i] < pv;
    {
        assert c[i] == c[|c|-|c|..][i]; //- OBSERVE
    }

    forall (i | 0 <= i < MaxLen3(a,b,c))
        ensures FNSubRelation_local(pv, a, b, c, carryin, i);
    {
        if (i<j) {
            assert FNSubRelation_local(pv, a, b, c[|c|-j..], carryin, i);
            assert FNSubRelation_local(pv, a, b, c, carryin, i);
        } else {
            assert FNSubRelation_local(pv, a, b, c, carryin, i);
        }
    }


//-    var la := [0]+a;
//-    var lb := [0]+b;
//-    var lc := [0]+c;
//-
//-    lemma_mul_basics_forall();
//-    forall (i | 0 <= i < MaxLen3(la,lb,lc))
//-        ensures FNSubRelation_local(pv, la, lb, lc, carryin, i);
//-    {
//-        if (i < MaxLen3(a,b,c))
//-        {
//-            assert FNSubRelation_local(pv, a, b, c[|c|-j..], carryin, i); //- OBSERVE
//-//-            assert FNSubRelation_local(pv, la, lb, lc, carryin, i);
//-        }
//-        else if (i==0)
//-        {
//-//-            assert FNSubRelation_local(pv, la, lb, lc, carryin, i);
//-        }
//-        else
//-        {
//-            assert i==MaxLen3(a,b,c);
//-            assert FNSubRelation_local(pv, a, b, c[|c|-j..], carryin, i-1); //- OBSERVE
//-            calc {
//-                DigitAt(carryin,i+1) * pv + DigitAt(la,i);
//-                DigitAt(carryin,i+1) * pv + 0;
//-                0 + 0 + DigitAt(carryin,i);
//-                DigitAt(lb,i) + DigitAt(lc,i) + DigitAt(carryin,i);
//-            }
//-        }
//-    }
}

lemma lemma_FNSubtraction_induction(pv:int, oml:int, a:seq<int>, b:seq<int>, oldc:seq<int>, c:seq<int>, oldcarryin:seq<int>, carryin:seq<int>, oldj:int, j:int, lastcarry:int)
    requires 1<pv;
    requires 0 <= oldj < oml;
    requires j==oldj+1;
    requires IsBitSeq(oldcarryin);
    requires oml == MaxLen3(a,b,c);
    requires IsDigitSeq(pv, a[..]);
    requires IsDigitSeq(pv, b[..]);
    requires oml==|oldc|==|c|;
    requires IsDigitSeq(pv, oldc[|c|-oldj..]);
    requires IsDigitSeq(pv, c[|c|-oldj..]);
    requires IsDigitSeq(pv, c[|c|-j..]);
    requires IsDigitSeq(2, oldcarryin);
    requires 0<=lastcarry<2;
    requires carryin == [lastcarry] + oldcarryin;
//-    requires lastcarry == DigitAt(oldcarryin, oldj);
    requires DigitAt(oldcarryin, 0) == 0;
    requires |oldcarryin| == oldj+1;
    requires forall i :: 0<=i<oldj ==> DigitAt(c, i) == DigitAt(oldc, i);
    requires FNSubRelation_inductive(pv, a, b, oldc, oldcarryin, oldj);
    requires DigitAt(carryin,j) * pv + DigitAt(a,oldj)
        == DigitAt(b,oldj) + DigitAt(c,oldj) + DigitAt(oldcarryin,oldj);
    ensures IsDigitSeq(pv, c[|c|-j..]);
    ensures FNSubRelation_inductive(pv, a, b, c, [lastcarry]+oldcarryin, j);
{
    assert 0 <= |c|-j < |c|;

    assert lastcarry == DigitAt(carryin, j);

    ghost var olda := a;
    ghost var oldb := b;
    ghost var newc := c[|c|-j..];
    forall (i | 0 <= i < j)
        ensures FNSubRelation_local(pv, a, b, newc, carryin, i);
    {
        if (i<oldj)
        {
            calc {
                DigitAt(carryin,i+1) * pv + DigitAt(a,i);
                    { assert DigitAt(carryin,i+1)==DigitAt(oldcarryin,i+1); }
                DigitAt(oldcarryin,i+1) * pv + DigitAt(a,i);
                    { assert DigitAt(a,i)==DigitAt(olda,i); }
                DigitAt(oldcarryin,i+1) * pv + DigitAt(olda,i);
                {
                    assert FNSubRelation_inductive(pv, olda, oldb, oldc, oldcarryin, oldj);
                    assert FNSubRelation_local(pv, olda, oldb, oldc[|oldc|-oldj..], oldcarryin, i);
                }
                DigitAt(oldb,i) + DigitAt(oldc[|oldc|-oldj..],i) + DigitAt(oldcarryin,i);
                    { assert DigitAt(b,i)==DigitAt(oldb,i); }
                DigitAt(b,i) + DigitAt(oldc[|oldc|-oldj..],i) + DigitAt(oldcarryin,i);
                     { assert DigitAt(carryin,i)==DigitAt(oldcarryin,i); }
                DigitAt(b,i) + DigitAt(oldc[|oldc|-oldj..],i) + DigitAt(carryin,i);
                DigitAt(b,i) + DigitAt(oldc,i) + DigitAt(carryin,i);
                    { assert DigitAt(newc,i)==DigitAt(oldc,i); }
                DigitAt(b,i) + DigitAt(newc,i) + DigitAt(carryin,i);
            }
            assert FNSubRelation_local(pv, a, b, c[|c|-j..], carryin, i);
            assert FNSubRelation_local(pv, a, b, newc, carryin, i);
        }
    }
    assert newc == c[|c|-j..];
    assert IsDigitSeq(pv, newc);
    assert forall i :: 0 <= i < j
        ==> FNSubRelation_local(pv, a, b, newc, carryin, i);
    assert forall i :: 0 <= i < j
        ==> FNSubRelation_local(pv, a, b, c[|c|-j..], carryin, i);
    assert FNSubRelation_inductive(pv, a, b, c, carryin, j);
}

//- inner variant exposes the borrow
method FNSubtract_inner(ghost pv:int, a:array<int>, b:array<int>) returns (c:array<int>, ghost borrow:int)
    requires pv == power2(32);
    requires a!=null;
    requires b!=null;
    requires IsDigitSeq(pv, a[..]);
    requires IsDigitSeq(pv, b[..]);
    ensures c!=null;
    ensures IsDigitSeq(pv, c[..]);
    ensures c.Length <= a.Length || c.Length <= b.Length;
    ensures 0<=borrow;
    ensures borrow * power(pv,MaxLen3(a[..],b[..],c[..])) + BEDigitSeqToInt(pv,a[..])
        == BEDigitSeqToInt(pv,b[..]) + BEDigitSeqToInt(pv,c[..]);
{
    lemma_2toX32();
    ghost var carryin:seq<int> := [0];
    var iml := (if a.Length > b.Length then a.Length else b.Length);
    var oml := iml;
    c := new int[oml];
    assert oml == MaxLen3(a[..],b[..],c[..]);
    var lastcarry := 0;
    var j:=0;
    while (j < oml)
        invariant 0 <= j <= oml;
        invariant IsBitSeq(carryin);
        invariant lastcarry == DigitAt(carryin, j);
        invariant DigitAt(carryin, 0) == 0;
        invariant IsDigitSeq(pv, c[c.Length-j..]);
        invariant |carryin| == j+1;
        invariant FNSubRelation_inductive(pv, a[..], b[..], c[..], carryin, j);
    {
        ghost var olda := a[..];
        ghost var oldb := b[..];
        ghost var oldc := c[..];
        ghost var oldcarryin := carryin[..];
        ghost var oldj := j;
        assert FNSubRelation_inductive(pv, olda, oldb, oldc, oldcarryin, oldj);

        var difference,carry := Sub32_with_borrow(
            ArrayDigitAt_sub(a,j), ArrayDigitAt_sub(b,j), lastcarry);
        assert c[..] == oldc;   //- OBSERVE

        carryin := [carry] + carryin;
        lastcarry := carry;
        c[c.Length - 1 - j] := difference;

        assert c[c.Length-1-j..] == [c[c.Length-1-j]] + c[c.Length-j..];    //- OBSERVE

        j:=j+1;
        assert olda==a[..];
        assert oldb==b[..];
        lemma_FNSubtraction_induction(pv, oml, a[..], b[..], oldc, c[..], oldcarryin, carryin, oldj, j, lastcarry);
    }

    assert c[..] == c[c.Length-oml..];   //- OBSERVE

    lemma_SubRelationInduction(pv, a[..], b[..], c[..], carryin, oml);

    assert DigitAt(carryin,0)==0;
    borrow := DigitAt(carryin,oml);
    calc {
        borrow * power(pv,MaxLen3(a[..],b[..],c[..])) + BEDigitSeqToInt(pv,a[..]);
        DigitAt(carryin,oml) * power(pv,oml) + BEDigitSeqToInt(pv,a[..]);
            { lemma_FNSubtraction(pv, a[..], b[..], c[..], carryin); }
        BEDigitSeqToInt(pv,b[..]) + BEDigitSeqToInt(pv,c[..]) + DigitAt(carryin,0);
        BEDigitSeqToInt(pv,b[..]) + BEDigitSeqToInt(pv,c[..]);
    }
}

method FatNatSub(a:array<int>, b:array<int>) returns (c:array<int>)
    requires a!=null;
    requires b!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires IsDigitSeq(power2(32), b[..]);
    requires BEDigitSeqToInt(power2(32), a[..]) >= BEDigitSeqToInt(power2(32), b[..]);
    ensures c!=null;
    ensures IsDigitSeq(power2(32), c[..]);
    ensures c.Length <= a.Length || c.Length <= b.Length;
    ensures BEDigitSeqToInt(power2(32),a[..])
        == BEDigitSeqToInt(power2(32),b[..]) + BEDigitSeqToInt(power2(32),c[..]);
{
    ghost var As := a[..];
    ghost var Bs := b[..];

    lemma_mul_basics_forall();
    ghost var borrow;
    c,borrow := FNSubtract_inner(power2(32), a, b);
    if (borrow > 0)
    {
        ghost var pv := power2(32);
        calc {
            BEDigitSeqToInt(pv,c[..]);
            <   { lemma_BEDigitSeqToInt_bound(pv, c[..]); }
            power(pv,|c[..]|);
            <=  { lemma_power_increases(pv, |c[..]|, MaxLen3(a[..],b[..],c[..])); }
            power(pv,MaxLen3(a[..],b[..],c[..]));
        }
        calc {
            BEDigitSeqToInt(pv,a[..]);
            <
            power(pv,MaxLen3(a[..],b[..],c[..])) + BEDigitSeqToInt(pv,a[..])
                - BEDigitSeqToInt(pv,c[..]);
                { lemma_mul_basics_forall(); }
            mul(1, power(pv,MaxLen3(a[..],b[..],c[..]))) + BEDigitSeqToInt(pv,a[..])
                - BEDigitSeqToInt(pv,c[..]);
            <= {
                lemma_power_positive(pv, MaxLen3(a[..],b[..],c[..]));
                lemma_mul_inequality(1, borrow, power(pv,MaxLen3(a[..],b[..],c[..]))); }
            borrow * power(pv,MaxLen3(a[..],b[..],c[..])) + BEDigitSeqToInt(pv,a[..])
                - BEDigitSeqToInt(pv,c[..]);
            BEDigitSeqToInt(pv,b[..]);
        }
        assert false;
    }
    assert borrow == 0;
    ghost var pv := power2(32);
    calc {
        BEDigitSeqToInt(power2(32),a[..]);
            { lemma_mul_basics(power(pv,MaxLen3(a[..],b[..],c[..]))); }
        borrow * power(pv,MaxLen3(a[..],b[..],c[..])) + BEDigitSeqToInt(pv,a[..]);
        BEDigitSeqToInt(power2(32),b[..]) + BEDigitSeqToInt(power2(32),c[..]);
        BEDigitSeqToInt(pv,b[..]) + BEDigitSeqToInt(pv,c[..]);
    }
}
