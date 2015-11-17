include "FatNatCommon.i.dfy"
include "FatNatX86.i.dfy"
include "../Util/beseqs_simple.i.dfy"
include "FatNatAddLemmas.i.dfy"

predicate FNAddRelation_local(pv:int, a:seq<int>, b:seq<int>, c:seq<int>, carryin:seq<int>, i:int)
    requires 1<pv;
    requires IsDigitSeq(pv, a);
    requires IsDigitSeq(pv, b);
    requires IsDigitSeq(pv, c);
    requires IsDigitSeq(2, carryin);
    requires 0 <= i < MaxLen3(a,b,c);
{
    DigitAt(c,i) + DigitAt(carryin,i+1) * pv
        == DigitAt(a,i) + DigitAt(b,i) + DigitAt(carryin,i)
}

predicate FNAddRelation(pv:int, a:seq<int>, b:seq<int>, c:seq<int>, carryin:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, a);
    requires IsDigitSeq(pv, b);
    requires IsDigitSeq(pv, c);
    requires IsDigitSeq(2, carryin);
{
    forall i :: 0 <= i < MaxLen3(a,b,c)
        ==> FNAddRelation_local(pv, a, b, c, carryin, i)
}

lemma lemma_FNAddition_recursive(pv:int, a:seq<int>, b:seq<int>, c:seq<int>, carryin:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, a);
    requires IsDigitSeq(pv, b);
    requires IsDigitSeq(pv, c);
    requires IsDigitSeq(2, carryin);
    requires |a| == |b| == |c| == |carryin|;
    requires FNAddRelation(pv, a, b, c, carryin);
    ensures DigitAt(carryin, 0) + BEDigitSeqToInt(pv,a) + BEDigitSeqToInt(pv,b) == BEDigitSeqToInt(pv,c);
    decreases |a|;
{
    var ml := |a|;
    if (ml==0)
    {
        reveal_BEDigitSeqToInt_private();
    }
    else
    {
        var sa := a[..ml-1];
        var sb := b[..ml-1];
        var sc := c[..ml-1];
        var scarryin := carryin[..ml-1];

        forall (i | 0 <= i < MaxLen3(sa,sb,sc))
            ensures FNAddRelation_local(pv, sa, sb, sc, scarryin, i);
        {
            assert FNAddRelation_local(pv, a, b, c, carryin, i+1);    //- OBSERVE
        }
        assert FNAddRelation(pv, sa, sb, sc, scarryin);

        var nextcarry := DigitAt(carryin, 1);
        calc {
            DigitAt(carryin, 0) + BEDigitSeqToInt(pv,a) + BEDigitSeqToInt(pv,b);
                { reveal_BEDigitSeqToInt_private();
                assert a[0..ml-1]==sa;
                assert b[0..ml-1]==sb; }
            DigitAt(carryin, 0)
                + BEDigitSeqToInt(pv,sa) * pv
                + DigitAt(a, 0)
                + BEDigitSeqToInt(pv,sb) * pv
                + DigitAt(b, 0);
            DigitAt(a,0) + DigitAt(b,0) + DigitAt(carryin,0)
                + BEDigitSeqToInt(pv,sa)*pv
                + BEDigitSeqToInt(pv,sb)*pv;
            { assert FNAddRelation_local(pv, a, b, c, carryin, 0);    //- OBSERVE
            }
            DigitAt(c,0) + DigitAt(carryin,1) * pv
                + BEDigitSeqToInt(pv,sa)*pv
                + BEDigitSeqToInt(pv,sb)*pv;
                { lemma_mul_is_distributive_forall(); }
            (nextcarry + BEDigitSeqToInt(pv,sa) + BEDigitSeqToInt(pv,sb)) * pv + DigitAt(c,0);
            (DigitAt(scarryin, 0) + BEDigitSeqToInt(pv,sa) + BEDigitSeqToInt(pv,sb)) * pv + DigitAt(c,0);
                { lemma_FNAddition_recursive(pv, sa, sb, sc, scarryin); }
            BEDigitSeqToInt(pv,sc) * pv + DigitAt(c,0);
                { reveal_BEDigitSeqToInt_private();
                assert c[0..ml-1]==sc; }
            BEDigitSeqToInt(pv,c);
        }
    }
}

lemma lemma_FNAddition(pv:int, a:seq<int>, b:seq<int>, c:seq<int>, carryin:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, a);
    requires IsDigitSeq(pv, b);
    requires IsDigitSeq(pv, c);
    requires IsDigitSeq(2, carryin);
    requires |carryin| <= MaxLen3(a,b,c);
    requires FNAddRelation(pv, a, b, c, carryin);
    ensures DigitAt(carryin, 0) + BEDigitSeqToInt(pv,a) + BEDigitSeqToInt(pv,b) == BEDigitSeqToInt(pv,c);
{
    var ml := MaxLen3(a,b,c);
    var la := Stretch(a, ml);
    var lb := Stretch(b, ml);
    var lc := Stretch(c, ml);
    var lcarryin := Stretch(carryin, ml);

    forall (i | 0 <= i < MaxLen3(la,lb,lc))
        ensures FNAddRelation_local(pv, la, lb, lc, lcarryin, i);
    {
        assert FNAddRelation_local(pv, a, b, c, carryin, i);    //- OBSERVE
    }

    lemma_FNAddition_recursive(pv, la, lb, lc, lcarryin);
    lemma_LeadingZeros(pv, a, la);
    lemma_LeadingZeros(pv, b, lb);
    lemma_LeadingZeros(pv, c, lc);
}

//- Need to be able to talk about just the assembled part of c.
predicate FNAddRelation_inductive(pv:int, a:seq<int>, b:seq<int>, c:seq<int>, carryin:seq<int>, j:int)
    requires 1<pv;
    requires IsDigitSeq(pv, a);
    requires IsDigitSeq(pv, b);
    requires 0 <= j <= |c|;
    requires IsDigitSeq(pv, c[|c|-j..]);
    requires IsDigitSeq(2, carryin);
//-    requires |carryin| >= j;
{
    forall i :: 0 <= i < j
        ==> FNAddRelation_local(pv, a, b, c[|c|-j..], carryin, i)
}

lemma lemma_AddRelationInduction(pv:int, a:seq<int>, b:seq<int>, c:seq<int>, carryin:seq<int>, j:int)
    requires 1<pv;
    requires IsDigitSeq(pv, a);
    requires IsDigitSeq(pv, b);
    requires j == MaxLen3(a,b,c);
    requires j == |c|;
    requires IsDigitSeq(pv, c[|c|-j..]);
    requires IsDigitSeq(2, carryin);
    requires |carryin| == j+1;
    requires FNAddRelation_inductive(pv, a, b, c, carryin, j);
    requires DigitAt(carryin, 0) == 0;
    requires DigitAt(a, j-1) == 0;
    requires DigitAt(b, j-1) == 0;
    ensures IsDigitSeq(pv, c);
    ensures FNAddRelation(pv, [0]+a, [0]+b, [0]+c, carryin);
{
    forall (i | 0 <= i < |c|)
        ensures 0 <= c[i] < pv;
    {
        assert c[i] == c[|c|-|c|..][i]; //- OBSERVE
    }
    var la := [0]+a;
    var lb := [0]+b;
    var lc := [0]+c;

    lemma_mul_basics_forall();
    forall (i | 0 <= i < MaxLen3(la,lb,lc))
        ensures FNAddRelation_local(pv, la, lb, lc, carryin, i);
    {
        if (i < MaxLen3(a,b,c))
        {
            assert FNAddRelation_local(pv, a, b, c[|c|-j..], carryin, i); //- OBSERVE
        }
        else if (i==0)
        {
        }
        else
        {
            assert FNAddRelation_local(pv, a, b, c[|c|-j..], carryin, i-1); //- OBSERVE
            if (DigitAt(carryin,i) > 0)
            {
                lemma_mul_increases(DigitAt(carryin,i), pv);
                assert false;
            }
        }
    }
}



lemma lemma_FNAddition_induction(pv:int, oml:int, a:seq<int>, b:seq<int>, oldc:seq<int>, c:seq<int>, oldcarryin:seq<int>, carryin:seq<int>, oldj:int, j:int, lastcarry:int)
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
    requires FNAddRelation_inductive(pv, a, b, oldc, oldcarryin, oldj);
    requires DigitAt(a,oldj)+DigitAt(b,oldj)+DigitAt(oldcarryin,oldj) == DigitAt(c,oldj) + DigitAt(carryin,j) * pv;
    ensures 0 <= |c|-j < |c|;
    ensures IsDigitSeq(pv, c[|c|-j..]);
    ensures FNAddRelation_inductive(pv, a, b, c, [lastcarry]+oldcarryin, j);
{
    assert 0 <= |c|-j < |c|;

    assert lastcarry == DigitAt(carryin, j);

    ghost var olda := a;
    ghost var oldb := b;
    ghost var newc := c[|c|-j..];
    forall (i | 0 <= i < j)
        ensures FNAddRelation_local(pv, a, b, newc, carryin, i);
    {
        if (i<oldj)
        {
            calc {
                DigitAt(newc,i) + DigitAt(carryin,i+1) * pv;
                {
                    assert DigitAt(newc,i)==DigitAt(oldc,i);
                    assert DigitAt(carryin,i+1)==DigitAt(oldcarryin,i+1);
                }
                DigitAt(oldc,i) + DigitAt(oldcarryin,i+1) * pv;
                {
                    assert FNAddRelation_inductive(pv, olda, oldb, oldc, oldcarryin, oldj);
                    assert FNAddRelation_local(pv, olda, oldb, oldc[|oldc|-oldj..], oldcarryin, i);
                }
                DigitAt(olda,i) + DigitAt(oldb,i) + DigitAt(oldcarryin,i);
                {
                    assert DigitAt(a,i)==DigitAt(olda,i);
                    assert DigitAt(b,i)==DigitAt(oldb,i);
                    assert DigitAt(carryin,i)==DigitAt(oldcarryin,i);
                }
                DigitAt(a,i) + DigitAt(b,i) + DigitAt(carryin,i);
            }
            assert FNAddRelation_local(pv, a, b, c[|c|-j..], carryin, i);

        }
    }
    assert newc == c[|c|-j..];
    assert IsDigitSeq(pv, newc);
    assert forall i :: 0 <= i < j
        ==> FNAddRelation_local(pv, a, b, newc, carryin, i);
    assert forall i :: 0 <= i < j
        ==> FNAddRelation_local(pv, a, b, c[|c|-j..], carryin, i);
    assert FNAddRelation_inductive(pv, a, b, c, carryin, j);
}

method FatNatAdd(a:array<int>, b:array<int>) returns (c:array<int>)
    requires a!=null;
    requires b!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires IsDigitSeq(power2(32), b[..]);
    ensures c!=null;
    ensures IsDigitSeq(power2(32), c[..]);
    ensures BEWordSeqToInt(a[..]) + BEWordSeqToInt(b[..]) == BEWordSeqToInt(c[..]);
{
    ghost var pv := power2(32);
    lemma_2toX32();
    ghost var carryin:seq<int> := [0];
    var iml := (if a.Length > b.Length then a.Length else b.Length);
    var oml := iml + 1; //- +1 => leave space for overflow
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
        invariant FNAddRelation_inductive(pv, a[..], b[..], c[..], carryin, j);
    {
        ghost var olda := a[..];
        ghost var oldb := b[..];
        ghost var oldc := c[..];
        ghost var oldcarryin := carryin[..];
        ghost var oldj := j;
        assert FNAddRelation_inductive(pv, olda, oldb, oldc, oldcarryin, oldj);

        var sum,carry := Add32_with_carry(
            ArrayDigitAt_add(a,j), ArrayDigitAt_add(b,j), lastcarry);
        assert c[..] == oldc;   //- OBSERVE

        carryin := [carry] + carryin;
        lastcarry := carry;
        c[c.Length - 1 - j] := sum;

        assert c[c.Length-1-j..] == [c[c.Length-1-j]] + c[c.Length-j..];    //- OBSERVE

        j:=j+1;
        assert olda==a[..];
        assert oldb==b[..];
        lemma_FNAddition_induction(pv, oml, a[..], b[..], oldc, c[..], oldcarryin, carryin, oldj, j, lastcarry);
    }

    assert c[..] == c[c.Length-oml..];   //- OBSERVE

    lemma_AddRelationInduction(pv, a[..], b[..], c[..], carryin, oml);

    ghost var la := [0]+a[..];
    ghost var lb := [0]+b[..];
    ghost var lc := [0]+c[..];
    lemma_FNAddition(pv, la, lb, lc, carryin);
    lemma_LeadingZeros(pv, a[..], la);
    lemma_LeadingZeros(pv, b[..], lb);
    lemma_LeadingZeros(pv, c[..], lc);
}

lemma lemma_FNAddition_induction_unrolled(pv:int, a:seq<int>, b:seq<int>, oldc:seq<int>, c:seq<int>, oldcarryin:seq<int>, carryin:seq<int>, oldj:int, j:int, loopsize:int, loopcarries:seq<int>)
    requires 1<pv;
    requires 0 <= oldj <= |a|-loopsize;
    requires j==oldj+loopsize;
    requires IsBitSeq(oldcarryin);
//-    requires oml == MaxLen3(a,b,c);
    requires |a|==|b|;
    requires |a|+1==|c|;
    requires |oldc|==|c|;
    requires IsDigitSeq(pv, a[..]);
    requires IsDigitSeq(pv, b[..]);
    requires 0<=loopsize;
    requires IsDigitSeq(pv, oldc[|c|-oldj..]);
    requires IsDigitSeq(pv, c[|c|-j..]);
    requires IsDigitSeq(2, oldcarryin);
    requires IsDigitSeq(2, loopcarries);
    requires |loopcarries| == loopsize;
    requires carryin == loopcarries + oldcarryin;
    requires DigitAt(oldcarryin, 0) == 0;
    requires |oldcarryin| == oldj+1;
    requires forall i :: 0<=i<oldj ==> DigitAt(c, i) == DigitAt(oldc, i);
    requires FNAddRelation_inductive(pv, a, b, oldc, oldcarryin, oldj);
    requires forall i :: 0<=i<loopsize ==>
        DigitAt(a,oldj+i)+DigitAt(b,oldj+i)+DigitAt(carryin,oldj+i) == DigitAt(c,oldj+i) + DigitAt(carryin,oldj+i+1) * pv;
//-    ensures 0 <= |c|-j < |c|;
    ensures IsDigitSeq(pv, c[|c|-j..]);
    ensures FNAddRelation_inductive(pv, a, b, c, carryin, j);
    decreases loopsize;
{
    if (loopsize==0)
    {
//-        assert oldc==c;
        assert oldj==j;
        assert FNAddRelation_inductive(pv, a, b, oldc, oldcarryin, oldj);
        assert forall i :: 0 <= i < oldj
            ==> FNAddRelation_local(pv, a, b, oldc[|oldc|-oldj..], oldcarryin, i);
        forall (i | 0 <= i < j)
            ensures FNAddRelation_local(pv, a, b, c[|c|-j..], carryin, i);
        {
            if (i < oldj)
            {
                assert j == |c[|c|-j..]| == |oldc[|oldc|-oldj..]|;
                forall (ci | 0 <= ci < j)
                    ensures c[|c|-j..][ci] == oldc[|oldc|-oldj..][ci];
                {
                    calc {
                        c[|c|-j..][ci];
                        c[|c|-j+ci];
                        DigitAt(c, j-ci-1);
                        DigitAt(oldc, j-ci-1);
                        oldc[|oldc|-oldj+ci];
                        oldc[|oldc|-oldj..][ci];
                    }
                }
                assert c[|c|-j..] == oldc[|oldc|-oldj..];
                assert FNAddRelation_local(pv, a, b, oldc[|oldc|-oldj..], oldcarryin, i);
                assert FNAddRelation_local(pv, a, b, c[|c|-j..], carryin, i);
            }
            else
            {
            }
        }

        assert forall i :: 0 <= i < j
            ==> FNAddRelation_local(pv, a, b, c[|c|-j..], carryin, i);
        assert FNAddRelation_inductive(pv, a, b, c, carryin, j);
    }
    else
    {
        lemma_2toX32();
        forall (ci | 0 <= ci < |c[|c|-(j-1)..]|)
            ensures 0 <= c[|c|-(j-1)..][ci] < pv;
        {
            var v := c[|c|-j+1+ci];
            assert v == c[|c|-(j-1)..][ci]; //- OBSERVE
            assert v == c[|c|-j..][ci+1];   //- OBSERVE
            assert IsDigitSeq(pv, c[|c|-j..]);
            assert 0 <= v < pv;
        }
        assert IsDigitSeq(pv, c[|c|-(j-1)..]);

        var r_carryin := carryin[1..];
        lemma_selection_preserves_digit_seq(2, carryin, 1);
        var r_loopcarries := loopcarries[1..];
        calc {
            r_carryin;
            carryin[1..];
            (loopcarries + oldcarryin)[1..];
            loopcarries[1..] + oldcarryin;
            r_loopcarries + oldcarryin;
        }

        lemma_FNAddition_induction_unrolled(pv, a, b, oldc, c,
            oldcarryin, r_carryin, oldj, j-1, loopsize-1, r_loopcarries);

        lemma_FNAddition_induction(pv, |c|, a, b, c, c, r_carryin, carryin, j-1, j, loopcarries[0]);
    }
}

method {:timeLimitMultiplier 3} FatNatAddUnrolledLoop(a:array<int>, b:array<int>) returns (c:array<int>)
    requires a!=null;
    requires b!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires IsDigitSeq(power2(32), b[..]);
    requires a.Length == b.Length;
    requires a.Length%8 == 0;
    ensures c!=null;
    ensures IsDigitSeq(power2(32), c[..]);
    ensures BEWordSeqToInt(a[..]) + BEWordSeqToInt(b[..]) == BEWordSeqToInt(c[..]);
    ensures fresh(c);
{
    ghost var pv := power2(32);
    lemma_2toX32();
    ghost var carryin:seq<int> := [0];

    var iml := a.Length;
    var oml := iml + 1; //- +1 => leave space for carry overflow
    c := new int[oml];
    assert oml == MaxLen3(a[..],b[..],c[..]);

    var lastcarry := 0;
    var j:=0;
    while (j < iml)
        invariant j%8 == 0;
        invariant 0 <= j <= iml;
        invariant IsBitSeq(carryin);
        invariant lastcarry == DigitAt(carryin, j);
        invariant DigitAt(carryin, 0) == 0;
        invariant IsDigitSeq(pv, c[c.Length-j..]);
        invariant |carryin| == j+1;
        invariant FNAddRelation_inductive(pv, a[..], b[..], c[..], carryin, j);
    {
        ghost var olda := a[..];
        ghost var oldb := b[..];
        ghost var oldc := c[..];
        ghost var oldcarryin := carryin[..];
        ghost var oldj := j;
        ghost var old_lastcarry := lastcarry;
        assert FNAddRelation_inductive(pv, olda, oldb, oldc, oldcarryin, oldj);

//-        ghost var c1,c2,c3,c4,c5,c6,c7,carries;
//-        lastcarry,c1,c2,c3,c4,c5,c6,c7,carries := Add32_unrolled_8(a, j, b, j, c, j, lastcarry);
        
        ghost var carries;
        lastcarry,carries := Add32_unrolled_8(a, j, b, j, c, j, lastcarry);
        ghost var c1,c2,c3,c4,c5,c6,c7;
        c1 := carries[1];
        assert c1 == if a[a.Length-1-(j+0)] +b[b.Length-1-(j+0)] + carries[0] >= 0x100000000 then 1 else 0;
        c2 := carries[2];
        c3 := carries[3];
        c4 := carries[4];
        c5 := carries[5];
        c6 := carries[6];
        c7 := carries[7];

        ghost var loopcarries := [ lastcarry, c7, c6, c5, c4, c3, c2, c1 ];
//-        ghost var loopcarries := [ lastcarry ] + carries;
        carryin := loopcarries + carryin;

        ghost var sc := c[..];

        lemma_FatNatAddUnrolledLoop_DigitSeq_preservation(oldc, sc, j);

        lemma_Add32_unrolled_8_glue(
            a[..], j, b[..], j, c[..], j, old_lastcarry,
            lastcarry, c1, c2, c3, c4, c5, c6, c7,
//-            lastcarry, carries[1], carries[2], carries[3], carries[4], carries[5], carries[6], carries[7],
            loopcarries, oldcarryin, carryin);
        
        j:=j+8;
        assert olda==a[..];
        assert oldb==b[..];
        assert |carryin| == j+1;
        ghost var loopsize := 8;

        lemma_FNAddition_induction_unrolled(pv, a[..], b[..], oldc, c[..], oldcarryin, carryin, oldj, j, loopsize, loopcarries);
    }

    assert c[..] == c[c.Length-oml..];   //- OBSERVE SEQ

    //- Original FatNatAdd, to propagate the carry
    //- into c's last slot, used ArrayDigitAt's implicit zeros for a and b.
    //- We avoid ArrayDigitAt entirely, which is nice, but instead we
    //- must stuff the lastcarry into c explicitly after the loop.
    c[0] := lastcarry;

    ghost var sa := a[..];
    ghost var sb := b[..];
    ghost var sc := c[..];
    assert |carryin|==j+1;
    ghost var fcarryin := [0] + carryin;    //- that's f/inal/ carryin.

    forall (i | 0<=i<|sc|)
        ensures 0<=sc[i]<pv;
    {
        if (i>0)
        {
            //- assert IsDigitSeq(pv, sc[1..]);
            assert sc[i] == sc[1..][i-1];   //- OBSERVE SEQ
        }
    }

    forall (i | 0 <= i < oml)
        ensures FNAddRelation_local(pv, sa, sb, sc[|sc|-oml..], fcarryin, i);
    {
        if (i<oml-1)
        {
            assert FNAddRelation_local(pv, sa, sb, sc[|sc|-iml..], carryin, i); //- OBSERVE
        }
    }
    lemma_AddRelationInduction(pv, sa, sb, sc, fcarryin, oml);

    ghost var la := [0]+a[..];
    ghost var lb := [0]+b[..];
    ghost var lc := [0]+c[..];
    lemma_FNAddition(pv, la, lb, lc, fcarryin);
    lemma_LeadingZeros(pv, a[..], la);
    lemma_LeadingZeros(pv, b[..], lb);
    lemma_LeadingZeros(pv, c[..], lc);
}
