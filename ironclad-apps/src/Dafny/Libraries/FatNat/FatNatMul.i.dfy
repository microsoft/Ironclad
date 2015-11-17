include "../Util/seqs_common.i.dfy"
include "FatNatCommon.i.dfy"
include "FatNatAddUnrolled.i.dfy"
include "../FleetNat/FleetNatAdd.i.dfy"

include "../Util/ProfileIfc.i.dfy"

include "../Util/ProfileIfc.i.dfy"

datatype MulRow = MulRow_c(
    a_fragment:int, a_partial_sum:int, product:int);

predicate FNMulBase(row:MulRow)
{
    row.a_partial_sum == row.a_fragment
}

predicate FNMulRelation(row:MulRow, b:int, r:int)
{
    row.product == row.a_partial_sum * b + r
}

predicate FNMulNext(row:MulRow, row':MulRow)
{
    row'.a_partial_sum == row'.a_fragment + row.a_partial_sum
}

predicate FNMulEnd(row:MulRow, p:int, a:int)
{
    row.product == p
    && row.a_partial_sum == a
}

predicate FNMulProblemValid_partial(wks:seq<MulRow>, b:int, r:int)
{
    0<|wks|
    && (forall i :: 0<=i<|wks| ==> FNMulRelation(wks[i], b, r))
    && FNMulBase(wks[0])
    && (forall i :: 1<=i<|wks| ==> FNMulNext(wks[i-1], wks[i]))
}

predicate FNMulProblemValid(wks:seq<MulRow>, p:int, a:int, b:int, r:int)
{
    FNMulProblemValid_partial(wks, b, r)
    && FNMulEnd(wks[|wks|-1], p, a)
}

lemma lemma_FNMultiplication(wks:seq<MulRow>, p:int, a:int, b:int, r:int)
    requires FNMulProblemValid(wks, p, a, b, r);
    ensures p == a * b + r;
{
}

predicate FNMulRowReflectsBEDigits(pv:int, wks:seq<MulRow>, i:int, a:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, a);
    requires 0<=i<|wks|<=|a|;
{
    wks[i].a_partial_sum == BEDigitSeqToInt(pv, a[|a|-1-i..])
}

predicate PNWksReflectsBEDigits(pv:int, wks:seq<MulRow>, a:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, a);
    requires 0<|wks|<=|a|;
{
    forall i :: 0<=i<|wks| ==> FNMulRowReflectsBEDigits(pv, wks, i, a)
}

predicate FNMulProblemReflectsBESeq(pv:int, wks:seq<MulRow>, p:seq<int>, a:seq<int>, b:seq<int>, r:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, p);
    requires IsDigitSeq(pv, a);
    requires IsDigitSeq(pv, b);
    requires IsDigitSeq(pv, r);
{
    FNMulProblemValid(wks, BEDigitSeqToInt(pv, p), BEDigitSeqToInt(pv, a), BEDigitSeqToInt(pv, b), BEDigitSeqToInt(pv, r))
    && 0<|a|    
    && |wks|==|a|
    && PNWksReflectsBEDigits(pv, wks, a)
}

lemma lemma_FNMultiplication_BE(pv:int, wks:seq<MulRow>, p:seq<int>, a:seq<int>, b:seq<int>, r:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, a);
    requires IsDigitSeq(pv, b);
    requires IsDigitSeq(pv, p);
    requires IsDigitSeq(pv, r);
    requires FNMulProblemReflectsBESeq(pv, wks, p, a, b, r);
    ensures BEDigitSeqToInt(pv,p) ==
        BEDigitSeqToInt(pv,a) * BEDigitSeqToInt(pv,b) + BEDigitSeqToInt(pv,r);
{
}

//-////////////////////////////////////////////////////////////////////////////

method AllocArray(c:nat, right_zeros:nat) returns (a:array<int>)
    requires right_zeros<=c;
    ensures a!=null;
    ensures fresh(a);
    ensures a.Length==c;
    ensures forall i :: 0<=i<right_zeros ==> ArrayDigitAt(a, i)==0;
{
    a := new int[c];
    var j := 0;
    while (j < right_zeros)
        invariant 0 <= j <= right_zeros;
        invariant forall i :: 0<=i<j ==> ArrayDigitAt(a, i)==0;
    {
        assert forall i :: 0<=i<j ==> a[c-1-i]==ArrayDigitAt(a,i);  //- OBSERVE

        a[c-1-j] := 0;
        j := j + 1; // BURNED AGAIN by lack of termination-checking (decreases)!
    }
}

datatype M1Data = M1Data_c(b:array<int>, a:int, shiftd:int, pp:array<int>, i:int, carry:int);
datatype M1Ghost = M1Ghost_c(Bs:seq<int>, Ps:seq<int>);

predicate {:heap} M1invariant(d:M1Data, g:M1Ghost)
    reads d.b;
    reads d.pp;
{
       0<=d.a<power2(32)
    && 0<=d.shiftd
    && 0<=d.carry<power2(32)
    && d.b!=null
    && g.Bs == d.b[..]
    && IsDigitSeq(power2(32), g.Bs)
    && 0<=d.i<=|g.Bs|
    && d.pp!=null
    && g.Ps == d.pp[..]
    && |g.Ps| == 1 + |g.Bs| + d.shiftd
    && (forall j :: 0<=j<d.shiftd ==> DigitAt(g.Ps, j)==0)
    && IsDigitSeq(power2(32), SelectDigitRange(g.Ps, d.shiftd+d.i, d.shiftd))
    && d.a * BEWordSeqToInt(SelectDigits(g.Bs, d.i))
        == BEWordSeqToInt(SelectDigitRange(g.Ps, d.shiftd+d.i, d.shiftd)) + d.carry * power2(32*d.i)
}

method M1init(b:array<int>, a:int, shiftd:int) returns (d:M1Data, ghost g:M1Ghost)
    requires b!=null;
    requires IsDigitSeq(power2(32), b[..]);
    requires 0<=a<power2(32);
    requires 0<=shiftd;
    ensures fresh(d.pp);
    ensures M1invariant(d, g);
    ensures d.a == a;
    ensures d.shiftd == shiftd;
    ensures d.b == b;
{
    var pp := AllocArray(b.Length+shiftd+1, shiftd);
    ghost var Ps := pp[..];

    assert forall i :: 0<=i<shiftd ==> ArrayDigitAt(pp, i)==DigitAt(Ps,i);
    assert forall j :: 0<=j<shiftd ==> DigitAt(Ps, j)==0;

    d := M1Data_c(b, a, shiftd, pp, 0, 0);
    g := M1Ghost_c(b[..], pp[..]);
    assert Ps==pp[..];

    lemma_mul_basics_forall();
    reveal_BEDigitSeqToInt_private();
    assert IsWordSeq(SelectDigits(g.Bs, d.i));
    calc {
        BEWordSeqToInt(SelectDigits(g.Bs, d.i));
        d.a*BEWordSeqToInt(g.Bs[|g.Bs|-d.i..|g.Bs|]);
        d.a*BEWordSeqToInt(g.Bs[|g.Bs|..|g.Bs|]);
            { assert g.Bs[|g.Bs|..|g.Bs|]==[]; } //- OBSERVE
        d.a*BEWordSeqToInt([]);
        0;
        BEWordSeqToInt([]);
            { assert g.Ps[|g.Ps|-d.shiftd..|g.Ps|-d.shiftd]==[]; } //- OBSERVE
        BEWordSeqToInt(g.Ps[|g.Ps|-d.shiftd-d.i..|g.Ps|-d.shiftd]);
        BEWordSeqToInt(g.Ps[|g.Ps|-d.shiftd-d.i..|g.Ps|-d.shiftd]) + d.carry*power2(32*d.i);
        BEWordSeqToInt(SelectDigitRange(g.Ps, d.shiftd+d.i, d.shiftd)) + d.carry*power2(32*d.i);
    }
}


lemma lemma_M1step_a(g'Bs:seq<int>, di:int, d'i:int,
        b':seq<int>, t:seq<int>, b:seq<int>)
    requires IsWordSeq(g'Bs);
    requires 0<=di;
    requires di+1==d'i;
    requires d'i<=|g'Bs|;
    requires b'== SelectDigitRange(g'Bs, d'i, 0);
    requires t == SelectDigitRange(g'Bs, d'i, di);
    requires b == SelectDigitRange(g'Bs, di, 0);
    ensures b' == t+b;
    ensures b'[..|b'|-di] == t;
    ensures b'[|b'|-di..] == b;
{
    assert b' == t+b;   //- OBSERVE
    assert b'[..|b'|-di] == t;
    assert b'[|b'|-di..] == b;
}

method M1step(d:M1Data, ghost g:M1Ghost) returns (d':M1Data, ghost g':M1Ghost)
    requires M1invariant(d, g);
    requires d.i<|g.Bs|;
    modifies d.pp;
    ensures M1invariant(d', g');
    ensures d'.pp == d.pp;
    ensures d'.a == d.a;
    ensures d'.shiftd == d.shiftd;
    ensures d'.b == d.b;
{
    var dpp_ref := d.pp; //- do something real to d.pp so dafnycc will realize that d.pp is allocated, and thus that d.pp is unaffected by methods that don't affect allocated parts of the heap

    ghost var pv := power2(32);
    lemma_2toX();

    var ml,mh := Product32(d.a, ArrayDigitAt_mul(d.b,d.i));
    var sl,acarry := Add32_two_arguments(ml, d.carry);
    dpp_ref[dpp_ref.Length - 1 - d.shiftd - d.i] := sl;

    assert 0 <= acarry < 2;

    var zero,carry;
    carry,zero := Add32_two_arguments(mh, acarry);
    
    ghost var m := ml + mh*pv;
    lemma_mul_nonnegative(mh,pv);
    calc {
        m;
        d.a * ArrayDigitAt(d.b,d.i);
        <= { lemma_mul_inequality(d.a, pv-1, ArrayDigitAt(d.b,d.i)); }
        (pv-1) * ArrayDigitAt(d.b,d.i);
            { lemma_mul_is_commutative_forall(); }
        ArrayDigitAt(d.b,d.i) * (pv-1);
        <= { lemma_mul_inequality(ArrayDigitAt(d.b,d.i), pv-1, pv-1); }
        (pv-1) * (pv-1);
            { lemma_mul_is_distributive_forall(); }
        pv*(pv-1)-mul(1,pv-1);
            { lemma_mul_basics_forall(); }
        pv*(pv-1)-(pv-1);
            { lemma_mul_is_distributive_forall(); }
        pv*pv-mul(pv,1)-(pv-1);
            { lemma_mul_basics_forall(); }
        pv*pv-pv-pv+1;
            { lemma_mul_is_mul_boogie(2,pv); }
        pv*pv-mul(2,pv)+1;
            { lemma_mul_is_distributive_forall(); }
        (pv-2)*pv+1;
    }
    calc {
        mh;
            { lemma_fundamental_div_mod_converse(m, pv, mh, ml); }
        m / pv;
        <=  { lemma_div_is_ordered(m, ((pv-2)*pv + 1), pv); }
        ((pv-2)*pv + 1) / pv;
            { lemma_mul_is_commutative_forall(); }
        (pv*(pv-2) + 1) / pv;
            { lemma_div_multiples_vanish_fancy(pv-2, 1, pv); }
        pv-2;
    }
    assert mh+acarry < pv;
    lemma_mul_is_mul_boogie(0x100000000,zero);
    assert zero==0;

    d' := M1Data_c(d.b, d.a, d.shiftd, d.pp, d.i+1, carry);
    g' := M1Ghost_c(d.b[..], d.pp[..]);

    forall (j | 0<=j<d'.shiftd)
        ensures DigitAt(g'.Ps, j)==0;
    {
        assert DigitAt(g'.Ps, j)==DigitAt(g.Ps, j); //- OBSERVE
    }

    ghost var le_range := SelectDigitRange(g.Ps, d.shiftd+d.i, d.shiftd);
    ghost var be_range := g.Ps[|g.Ps|-d.shiftd-d.i..|g.Ps|-d.shiftd];
    ghost var le_range' := SelectDigitRange(g'.Ps, d'.shiftd+d'.i, d'.shiftd);
    ghost var be_range' := g'.Ps[|g'.Ps|-d'.shiftd-d'.i..|g'.Ps|-d'.shiftd];

    forall (j | 0<=j<|le_range'|)
        ensures 0 <= le_range'[j] < pv;
    {
        if (j>0)
        {
            assert 0 <= le_range[j-1] < pv;
            calc {
                le_range[j-1];
                be_range[j-1];
                g.Ps[|g.Ps|-d.shiftd-d.i..|g.Ps|-d.shiftd][j-1];
                g.Ps[|g.Ps|-d.shiftd-d.i+j-1];
                g'.Ps[|g'.Ps|-d'.shiftd-d'.i+j];
                be_range'[j];
                le_range'[j];
            }
            assert 0 <= le_range'[j] < pv;
        }
    }
    assert IsDigitSeq(power2(32), SelectDigitRange(g'.Ps, d'.shiftd+d'.i, d'.shiftd));

    ghost var b' := SelectDigitRange(g'.Bs, d'.i, 0);
    ghost var t := SelectDigitRange(g'.Bs, d'.i, d.i);
    ghost var b := SelectDigitRange(g'.Bs, d.i, 0);
    lemma_M1step_a(g'.Bs, d.i, d'.i, b', t, b);

    //- nicknames for subsequences of the product sequence
    ghost var HL := SelectDigitRange(g'.Ps, d'.i+d.shiftd, d.shiftd);
    ghost var HM := SelectDigitRange(g'.Ps, d'.i+d.shiftd, d.i+d.shiftd);
    ghost var ML := SelectDigitRange(g'.Ps, d.i+d.shiftd, d.shiftd);
    assert ML == SelectDigitRange(g.Ps, d.i+d.shiftd, d.shiftd);    //- OBSERVE
    assert IsDigitSeq(pv, ML);

    calc {
        d'.a * BEWordSeqToInt(SelectDigits(g'.Bs, d'.i));
        d'.a * BEWordSeqToInt(SelectDigitRange(g'.Bs, d'.i, 0));
            { lemma_BEInterpretation(pv, b', d.i);}
        d'.a *(
             BEWordSeqToInt(SelectDigitRange(g'.Bs, d'.i, d.i))*power(pv,d.i)
            + BEWordSeqToInt(SelectDigitRange(g'.Bs, d.i, 0)));
            { lemma_mul_is_distributive_forall(); lemma_mul_is_associative_forall(); }
        d'.a*BEWordSeqToInt(SelectDigitRange(g'.Bs, d'.i, d.i))*power(pv,d.i)
            + d'.a*BEWordSeqToInt(SelectDigitRange(g'.Bs, d.i, 0));
            //- equal primed terms
            { assert d'.a==d.a; assert g'.Bs==g.Bs;   //- OBSERVE
            }
        d.a*BEWordSeqToInt(SelectDigitRange(g.Bs, d'.i, d.i))*power(pv,d.i)
            + d.a*BEWordSeqToInt(SelectDigitRange(g.Bs, d.i, 0));
            //- induction hypothesis and
            { lemma_power2_unfolding(32, d.i);
                lemma_mul_is_mul_boogie(32, d.i); }
        d.a*BEWordSeqToInt(SelectDigitRange(g.Bs, d'.i, d.i))*power(pv,d.i)
            + BEWordSeqToInt(SelectDigitRange(g.Ps, d.i+d.shiftd, d.shiftd))
            + d.carry * power(pv,d.i);
            { lemma_mul_is_distributive_add_other_way(power(pv, d.i), d.a*BEWordSeqToInt(SelectDigitRange(g.Bs, d'.i, d.i)), d.carry); }
        (d.a*BEWordSeqToInt(SelectDigitRange(g.Bs, d'.i, d.i))
         + d.carry)*power(pv,d.i)
            + BEWordSeqToInt(SelectDigitRange(g.Ps, d.i+d.shiftd, d.shiftd));
            {
                reveal_BEDigitSeqToInt_private();
                lemma_SelectSingletonRange(g.Bs, d'.i, d.i);
                var s := [DigitAt(g.Bs, d.i)];
                assert s[0..|s|-1] == [];  
                lemma_BEDigitSeqToInt_singleton(pv, DigitAt(g.Bs, d.i));
            }

        (d.a*DigitAt(g.Bs,d.i)
         + d.carry)*power(pv,d.i)
            + BEWordSeqToInt(SelectDigitRange(g.Ps, d.i+d.shiftd, d.shiftd));
            { //- apply the 32-bit multiplication:
                assert ml+mh*pv == d.a * ArrayDigitAt(d.b,d.i);
                assert ArrayDigitAt(d.b,d.i)==DigitAt(g.Bs,d.i); }
        (ml+mh*pv + d.carry)*power(pv,d.i)
            + BEWordSeqToInt(SelectDigitRange(g.Ps, d.i+d.shiftd, d.shiftd));
            { lemma_mul_is_distributive_add_other_way(power(pv,d.i), ml + d.carry, mh*pv); }
        (ml+ d.carry)*power(pv,d.i)+mh*pv *power(pv,d.i)
            + BEWordSeqToInt(SelectDigitRange(g.Ps, d.i+d.shiftd, d.shiftd));
            { //- apply the first 32-bit add
                lemma_mul_is_mul_boogie(acarry, pv);
            }
        (sl+acarry*pv)*power(pv,d.i)+mh*pv *power(pv,d.i)
            + BEWordSeqToInt(SelectDigitRange(g.Ps, d.i+d.shiftd, d.shiftd));
            { lemma_mul_is_distributive_add_other_way(power(pv,d.i), sl, acarry*pv); }
        sl*power(pv,d.i)+acarry*pv*power(pv,d.i)+mh*pv*power(pv,d.i)
            + BEWordSeqToInt(SelectDigitRange(g.Ps, d.i+d.shiftd, d.shiftd));
            { lemma_mul_is_associative(mh, pv, power(pv,d.i)); }
            { lemma_mul_is_associative(acarry, pv, power(pv,d.i)); }
            { lemma_mul_is_distributive_add_other_way(pv*power(pv,d.i), acarry, mh); }
            { lemma_mul_is_associative(acarry + mh, pv, power(pv,d.i)); }
        sl*power(pv,d.i)+(acarry+mh)*pv*power(pv,d.i)
            + BEWordSeqToInt(SelectDigitRange(g.Ps, d.i+d.shiftd, d.shiftd));
            { //- apply the second 32-bit add
                lemma_mul_basics_forall();
                assert carry == carry+zero*pv == mh+acarry; }
        sl*power(pv,d.i)
            + BEWordSeqToInt(SelectDigitRange(g.Ps, d.i+d.shiftd, d.shiftd))
            +carry*pv*power(pv,d.i);
            //- re-prime
        sl*power(pv,d.i) + BEWordSeqToInt(ML) +carry*pv*power(pv,d.i);
        {
            lemma_SelectSingletonRange(g'.Ps, d'.i+d.shiftd, d.i+d.shiftd);
            lemma_BEDigitSeqToInt_singleton(pv, sl);
        }
        BEWordSeqToInt(HM)*power(pv,d.i) + BEWordSeqToInt(ML)
            +carry*pv*power(pv,d.i);
            { 
                lemma_SelectDigitSubrange(g'.Ps, d'.i+d.shiftd, d.i+d.shiftd, d.shiftd);
                assert HL == HM+ML;
                lemma_BEInterpretation(pv, HL, d.i);
                assert BEWordSeqToInt(HL)
                    == BEWordSeqToInt(HM)*power(pv,d.i) + BEWordSeqToInt(ML);
            }
        BEWordSeqToInt(SelectDigitRange(g'.Ps, d'.i+d.shiftd, d.shiftd))
            +carry*pv*power(pv,d.i);
            //- assignment of local into d'
        BEWordSeqToInt(SelectDigitRange(g'.Ps, d'.i+d.shiftd, d.shiftd))
            +d'.carry*pv*power(pv,d.i);
            { lemma_mul_is_associative_forall(); }
        BEWordSeqToInt(SelectDigitRange(g'.Ps, d'.i+d.shiftd, d.shiftd))
            +d'.carry*(pv*power(pv,d.i));
            { lemma_power_1(pv); }
        BEWordSeqToInt(SelectDigitRange(g'.Ps, d'.i+d.shiftd, d.shiftd))
            +d'.carry*(power(pv,1)*power(pv,d.i));
            { lemma_power_adds(pv,1,d.i); }
        BEWordSeqToInt(SelectDigitRange(g'.Ps, d'.i+d.shiftd, d.shiftd))
            +d'.carry*power(pv,d'.i);
            { lemma_power2_unfolding(32, d'.i);
                lemma_mul_is_mul_boogie(32, d'.i); }
        BEWordSeqToInt(SelectDigitRange(g'.Ps, d'.shiftd+d'.i, d'.shiftd)) + d'.carry * power2(32*d'.i);
    }
}

method M1conclusion(d:M1Data, ghost g:M1Ghost) returns (pp:array<int>)
    requires M1invariant(d, g);
    requires d.i == |g.Bs|;
    modifies d.pp;
    ensures pp!=null;
    ensures IsDigitSeq(power2(32), pp[..]);
    ensures d.a * power2(32*d.shiftd) * BEWordSeqToInt(d.b[..]) == BEWordSeqToInt(pp[..]);
    ensures d.a * power(power2(32),d.shiftd) * BEWordSeqToInt(d.b[..]) == BEWordSeqToInt(pp[..]);
    ensures pp == d.pp; //- used to propagate fresh()
{
    ghost var pv:=power2(32);
    lemma_2toX();

    var db_ref := d.b; //- do something real to d.b so dafnycc will realize that d.b is allocated, and thus that d.b is unaffected by methods that don't affect allocated parts of the heap

    pp := d.pp;
    pp[0] := d.carry;

    ghost var Ps := pp[..];
//-    assert IsWordSeq(SelectDigitRange(g.Ps, d.shiftd+d.i, d.shiftd));
    forall (j | 0<=j<|Ps|)
        ensures 0<=Ps[j]<pv;
    {
        ghost var i := |Ps|-1-j;
        assert Ps[j] == DigitAt(Ps, i);
        if (i<d.shiftd)
        {
            assert DigitAt(g.Ps,i)==DigitAt(Ps,i);  //- OBSERVE
        } else {
            var ii := i-d.shiftd;
            if (i<d.shiftd+d.i) {
                ghost var mantissa := SelectDigitRange(Ps, d.shiftd+d.i, d.shiftd);
                assert 0 <= DigitAt(mantissa, ii) < pv; //- OBSERVE
            } else {
            }
        }
    }
    assert IsWordSeq(Ps);

    ghost var HMs := Ps[..|Ps|-d.shiftd];
    ghost var MLs := Ps[|Ps|-d.shiftd..];
    assert Ps == HMs + MLs;   //- OBSERVE
    forall (i | 0<=i<|MLs|)
        ensures MLs[i]==0;
    {
        assert MLs[i] == DigitAt(g.Ps, |MLs|-1-i); //- OBSERVE
    }
    assert forall i :: 0<=i<|MLs| ==> MLs[i]==0;
    calc {
        BEWordSeqToInt(pp[..]);
        BEWordSeqToInt(Ps);
            { lemma_BEInterpretation(pv, Ps, d.shiftd); }
        BEDigitSeqToInt(pv, HMs) * power(pv,d.shiftd) + BEDigitSeqToInt(pv, MLs);
            { lemma_LeadingZeros(pv, [], MLs); }
        BEDigitSeqToInt(pv, HMs) * power(pv,d.shiftd) + BEDigitSeqToInt(pv, []);
            { reveal_BEDigitSeqToInt_private(); }
        BEDigitSeqToInt(pv, HMs) * power(pv,d.shiftd);
    }

    ghost var HMi := HMs[..|HMs|-d.i];
    ghost var MLi := HMs[|HMs|-d.i..];
    assert HMs == HMi+MLi;
    calc {
        BEWordSeqToInt(HMs);
            { lemma_BEInterpretation(pv, HMs, d.i); }
        BEWordSeqToInt(HMi)*power(pv,d.i)+BEWordSeqToInt(MLi);
            { assert HMi==[d.carry]; //- OBSERVE
              lemma_BEDigitSeqToInt_singleton(pv, d.carry); }
        d.carry*power(pv,d.i)+BEWordSeqToInt(MLi);
            { lemma_power2_unfolding(32, d.i);
              lemma_mul_is_mul_boogie(32, d.i); }
        d.carry*power2(32*d.i)+BEWordSeqToInt(MLi);
            { assert MLi == SelectDigitRange(g.Ps, d.shiftd+d.i, d.shiftd); //- OBSERVE
            }
        d.carry*power2(32*d.i)
            +BEWordSeqToInt(SelectDigitRange(g.Ps, d.shiftd+d.i, d.shiftd));
        d.a * BEWordSeqToInt(SelectDigits(g.Bs, d.i));
            { assert g.Bs[0..|g.Bs|] == g.Bs; //- OBSERVE
            }
        d.a * BEWordSeqToInt(g.Bs);
        d.a * BEWordSeqToInt(d.b[..]);
    }
    calc {
        BEWordSeqToInt(pp[..]);
        d.a * BEWordSeqToInt(d.b[..]) * power(pv,d.shiftd);
            { lemma_mul_is_associative(d.a, BEWordSeqToInt(d.b[..]), power(pv,d.shiftd));
              lemma_mul_is_commutative(BEWordSeqToInt(d.b[..]), power(pv,d.shiftd));
              lemma_mul_is_associative(d.a, power(pv,d.shiftd), BEWordSeqToInt(d.b[..])); }
        d.a * power(pv,d.shiftd) * BEWordSeqToInt(d.b[..]);
    }
    lemma_power2_unfolding(32, d.shiftd);
    lemma_mul_is_mul_boogie(32, d.shiftd);
}

method MultiplyOneRow(b:array<int>, a:int, shiftd:int) returns (pp:array<int>)
    requires b!=null;
    requires IsDigitSeq(power2(32), b[..]);
    requires 0<=a<power2(32);
    requires 0<=shiftd;
    ensures pp!=null;
    ensures fresh(pp);
    ensures IsDigitSeq(power2(32), pp[..]);
    ensures a * power2(32*shiftd) * BEWordSeqToInt(b[..]) == BEWordSeqToInt(pp[..]);
    ensures a * power(power2(32),shiftd) * BEWordSeqToInt(b[..]) == BEWordSeqToInt(pp[..]);
{
    var d;
    ghost var g;
    d,g := M1init(b, a, shiftd);
    var l_pp := d.pp;
    assert fresh(l_pp);
    while (d.i < d.b.Length)
        invariant M1invariant(d,g);
        invariant d.pp == l_pp;
        invariant d.a == a;
        invariant d.shiftd == shiftd;
        invariant d.b == b;
    {
        d,g := M1step(d, g);
    }
    pp := M1conclusion(d,g);
    assert pp == l_pp;
}

//-////////////////////////////////////////////////////////////////////////////

method MultiplyOneRowWrapper(b:array<int>, ghost Bs:seq<int>, a:int, shiftd:int) returns (pp:array<int>, ghost Ps:seq<int>)
    requires b!=null;
    requires Bs == b[..];
    requires IsDigitSeq(power2(32), Bs);
    requires 0<=a<power2(32);
    requires 0<=shiftd;
    ensures pp!=null;
    ensures fresh(pp);
    ensures Ps == pp[..];
    ensures IsDigitSeq(power2(32), Ps);
    ensures a * power2(32*shiftd) * BEWordSeqToInt(Bs) == BEWordSeqToInt(Ps);
    ensures a * power(power2(32),shiftd) * BEWordSeqToInt(Bs) == BEWordSeqToInt(Ps);
{
    pp := MultiplyOneRow(b, a, shiftd);
    Ps := pp[..];
}


method PNAddWrapper(a:array<int>, ghost As:seq<int>, b:array<int>, ghost Bs:seq<int>) returns (c:array<int>, ghost Cs:seq<int>)
    requires a!=null;
    requires As == a[..];
    requires b!=null;
    requires Bs == b[..];
    requires IsDigitSeq(power2(32), As);
    requires IsDigitSeq(power2(32), Bs);
    ensures c!=null;
    ensures Cs == c[..];
    ensures IsDigitSeq(power2(32), Cs);
    ensures BEWordSeqToInt(As) + BEWordSeqToInt(Bs) == BEWordSeqToInt(Cs);
{
    c := FatNatAdd(a, b);
//-    c := new int[0];
//    
//    
//    
//-    c := FleetNatAdd(c, a, b);
    Cs := c[..];
}

predicate FNMultiply_loop_invariant(pv:int, As:seq<int>, Bs:seq<int>, Rs:seq<int>, wks:seq<MulRow>, i:int)
{
       1<pv
    && IsDigitSeq(pv, As)
    && IsDigitSeq(pv, Bs)
    && IsDigitSeq(pv, Rs)
    && 0 < i == |wks| <= |As|
    && IsDigitSeq(pv, Rs)
    && FNMulProblemValid_partial(wks, BEDigitSeqToInt(pv, Bs), 0)
    && PNWksReflectsBEDigits(pv, wks, As)
    && wks[|wks|-1].product == BEDigitSeqToInt(pv, Rs)
}

lemma lemma_FNMultiply_base_case(pv:int, As:seq<int>, Bs:seq<int>, Rs:seq<int>, wks:seq<MulRow>)
    requires 1<pv;
    requires IsDigitSeq(pv, As);
    requires 0<|As|;
    requires IsDigitSeq(pv, Bs);
    requires IsDigitSeq(pv, Rs);
    requires BEDigitSeqToInt(pv, Rs) == DigitAt(As,0) * BEDigitSeqToInt(pv, Bs);
    requires wks==[MulRow_c(DigitAt(As,0), DigitAt(As,0), BEDigitSeqToInt(pv, Rs))];
    ensures FNMultiply_loop_invariant(pv, As, Bs, Rs, wks, 1);
{
    ghost var Astail := [As[|As|-1]];
    ghost var Astrunc := As[|As|-1..];
    reveal_BEDigitSeqToInt_private();
    lemma_mul_basics_forall();
    calc {
        wks[0].a_partial_sum;
        DigitAt(As,0);
        As[|As|-1];
        BEDigitSeqToInt(pv, Astail[0..|Astail|-1])*pv + Astail[|Astail|-1];
            { assert Astail[0..|Astail|-1] == []; }     //- OBSERVE
        BEDigitSeqToInt(pv, Astail);
            { assert As[|As|-1..] == [As[|As|-1]]; }    //- OBSERVE
        BEDigitSeqToInt(pv, As[|As|-1..]);
    }
    assert Astrunc[|Astrunc|-1-0..] == As[|As|-1..];    //- OBSERVE

    assert FNMultiply_loop_invariant(pv, As, Bs, Rs, wks, 1);
}

lemma lemma_FNMultiply_inductive_step(pv:int, As:seq<int>, Bs:seq<int>,
    old_Rs:seq<int>, old_wks:seq<MulRow>, old_i:int,
    Ms:seq<int>, a_fragment:int, a_partial_sum:int, rowi:MulRow,
    Rs:seq<int>, wks:seq<MulRow>, i:int)
    requires FNMultiply_loop_invariant(pv, As, Bs, old_Rs, old_wks, old_i);
    requires IsDigitSeq(pv, Ms);
    requires i==old_i+1;
    requires old_i < |As|;
    requires BEDigitSeqToInt(pv,Ms) == DigitAt(As,old_i) * power(pv,old_i) * BEDigitSeqToInt(pv,Bs);
    requires IsDigitSeq(pv, Rs);
    requires BEDigitSeqToInt(pv,Rs) == BEDigitSeqToInt(pv,old_Rs) + BEDigitSeqToInt(pv,Ms);
    requires wks == old_wks + [rowi];
    requires a_fragment == DigitAt(As,old_i)*power(pv,old_i);
    requires a_partial_sum == a_fragment + old_wks[|old_wks|-1].a_partial_sum;
    requires rowi == MulRow_c(a_fragment, a_partial_sum, BEDigitSeqToInt(pv,Rs));
    ensures FNMultiply_loop_invariant(pv, As, Bs, Rs, wks, i);
{
    assert IsDigitSeq(pv, Rs);
    assert 0 < i == |wks| <= |As|;
    assert IsDigitSeq(pv, Rs);

    var Bv := BEDigitSeqToInt(pv,Bs);
    assert 0<|wks|;
    forall (j | 0<=j<|wks|)
        ensures FNMulRelation(wks[j], Bv, 0);
    {
        if (j<|old_wks|)
        {
            assert FNMulRelation(old_wks[j], Bv, 0);
        }
        else
        {
            calc {
                wks[j].product;
                rowi.product;
                BEDigitSeqToInt(pv,Rs);
                BEDigitSeqToInt(pv,old_Rs) + BEDigitSeqToInt(pv,Ms);
                old_wks[|old_wks|-1].a_partial_sum*Bv + BEDigitSeqToInt(pv,Ms);
                old_wks[|old_wks|-1].a_partial_sum*Bv +
                    DigitAt(As,old_i) * power(pv,old_i) * Bv;
                DigitAt(As,old_i)*power(pv,old_i)*Bv
                    + old_wks[|old_wks|-1].a_partial_sum*Bv;
                a_fragment*Bv + old_wks[|old_wks|-1].a_partial_sum*Bv;
                    { lemma_mul_is_distributive_forall(); }
                (a_fragment + old_wks[|old_wks|-1].a_partial_sum) * Bv;
                rowi.a_partial_sum * Bv;
                wks[j].a_partial_sum * Bv + 0;
            }
            assert FNMulRelation(wks[j], Bv, 0);
        }
    }
    assert FNMulBase(wks[0]);
    forall (j | 1<=j<|wks|)
        ensures FNMulNext(wks[j-1], wks[j]);
    {
        if (j<|old_wks|)
        {
            assert FNMulNext(old_wks[j-1], old_wks[j]);
        }
        else
        {
            assert FNMulNext(wks[j-1], wks[j]);
        }
    }

    assert FNMulProblemValid_partial(wks, Bv, 0);

    forall (j | 0<=j<|wks|)
        ensures FNMulRowReflectsBEDigits(pv, wks, j, As);
    {
        if (j<|old_wks|)
        {
            assert FNMulRowReflectsBEDigits(pv, old_wks, j, As);
        }
        else
        {
            assert j==|old_wks|==|wks|-1==i-1;
            var As1j := As[|As|-1-j..];
            assert |As1j| == j+1;
            calc {
                BEDigitSeqToInt(pv, As[|As|-1-j..]);
                BEDigitSeqToInt(pv, As1j);
                    { lemma_BEInterpretation(pv, As1j, j); }
                BEDigitSeqToInt(pv, As1j[..|As1j|-j]) * power(pv,j) + BEDigitSeqToInt(pv, As1j[|As1j|-j..]);
                    {
                        assert As1j[..|As1j|-j] == As[|As|-1-j..|As|-j];
                        assert As1j[|As1j|-j..] == As[|As|-j..];
                    }
                BEDigitSeqToInt(pv, As[|As|-1-j..|As|-j]) * power(pv,j) + BEDigitSeqToInt(pv, As1j[|As1j|-j..]);

            }
            ghost var Astail := As[|As|-1-j..];
            calc {
                wks[j].a_partial_sum;
                a_partial_sum;
                a_fragment + old_wks[|old_wks|-1].a_partial_sum;
                DigitAt(As,old_i)*power(pv,old_i) + old_wks[|old_wks|-1].a_partial_sum;
                    { assert FNMulRowReflectsBEDigits(pv, old_wks, j-1, As); }
                DigitAt(As,old_i)*power(pv,old_i) + BEDigitSeqToInt(pv, As[|As|-j..]);
                    { assert As[|As|-j..] == Astail[|Astail|-old_i..]; }
                DigitAt(As,old_i)*power(pv,old_i) + BEDigitSeqToInt(pv, Astail[|Astail|-old_i..]);
                {
                    assert Astail[..|Astail|-old_i] == [DigitAt(As,old_i)];
                    lemma_mul_basics_forall();
                    reveal_BEDigitSeqToInt_private();
                    assert [DigitAt(As,old_i)][0..|[DigitAt(As,old_i)]|-1] == [];
                    
                    calc  {
                        DigitAt(As,old_i);
                        mul(0,power(pv,1)) + DigitAt(As,old_i);
                        BEDigitSeqToInt(pv, [])*power(pv,1) + DigitAt(As,old_i);
                        BEDigitSeqToInt(pv, [DigitAt(As,old_i)]);
                        BEDigitSeqToInt(pv, Astail[..|Astail|-old_i]);
                    }
                }
                BEDigitSeqToInt(pv, Astail[..|Astail|-old_i]) * power(pv,old_i) + BEDigitSeqToInt(pv, Astail[|Astail|-old_i..]);
                    { lemma_BEInterpretation(pv, Astail, old_i); }
                BEDigitSeqToInt(pv, As[|As|-1-j..]);
            }
            assert FNMulRowReflectsBEDigits(pv, wks, j, As);
        }
    }
    assert PNWksReflectsBEDigits(pv, wks, As);
    assert wks[|wks|-1].product == BEDigitSeqToInt(pv,Rs);
}

datatype FNMulData = FNMulData_c(a:array<int>, b:array<int>, running_sum:array<int>, i:int);
datatype FNMulGhost = FNMulGhost_c(As:seq<int>, Bs:seq<int>, Rs:seq<int>, wks:seq<MulRow>);

predicate {:heap} FNMultiply_loop_invariant_kit(d:FNMulData, g:FNMulGhost)
    reads d.a;
    reads d.b;
    reads d.running_sum;
{
       d.a != null
    && d.a[..] == g.As
    && d.b != null
    && d.b[..] == g.Bs
    && d.running_sum != null
    && d.running_sum[..] == g.Rs
    && FNMultiply_loop_invariant(power2(32), g.As, g.Bs, g.Rs, g.wks, d.i)
}

method FNMultiply_init_kit(a:array<int>, b:array<int>) returns (d:FNMulData, ghost g:FNMulGhost)
    requires a!=null;
    requires 0<a.Length;
    requires b!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires IsDigitSeq(power2(32), b[..]);
    ensures FNMultiply_loop_invariant_kit(d, g);
    ensures a[..] == g.As;
    ensures b[..] == g.Bs;
    ensures d.a == a;
    ensures d.b == b;
{
    lemma_2toX();
    ghost var pv := power2(32);
    ghost var As := a[..];
    ghost var Bs := b[..];

    lemma_power2_0_is_1();
    lemma_power_0(pv);
    lemma_mul_basics_forall();
    var running_sum := MultiplyOneRow(b, ArrayDigitAt_mul(a,0), 0);
    ghost var Rs := running_sum[..];
    d := FNMulData_c(a, b, running_sum, 1);

    ghost var row0 := MulRow_c(DigitAt(As,0), DigitAt(As,0), BEWordSeqToInt(Rs));
    ghost var wks := [row0];
    g := FNMulGhost_c(As, Bs, Rs, wks);

    assert BEDigitSeqToInt(pv, g.Rs) == DigitAt(g.As,0) * BEDigitSeqToInt(pv, g.Bs);
    lemma_FNMultiply_base_case(pv, g.As, g.Bs, g.Rs, g.wks);
}

method FNMultiply_step_kit(d:FNMulData, ghost g:FNMulGhost) returns (d':FNMulData, ghost g':FNMulGhost)
    requires FNMultiply_loop_invariant_kit(d, g);
    requires d.i < |g.As|;
    ensures FNMultiply_loop_invariant_kit(d', g');
    ensures g'.As == g.As;
    ensures g'.Bs == g.Bs;
    ensures d'.a == d.a;
    ensures d'.b == d.b;
{
    var db_ref := d.b; //- do something real to d.b so dafnycc will realize that d.b is allocated, and thus that d.b is unaffected by methods that don't affect allocated parts of the heap
    var da_ref := d.a; //- do something real to d.a for the same reason as d.b above
    var drunning_sum_ref := d.running_sum; //- do something real to d.running_sum for the same reason as d.b above

    ghost var pv := power2(32);


    var d_a := d.a;
    var digit := ArrayDigitAt_mul(d_a,d.i);
    var middle_sum,Ms := MultiplyOneRowWrapper(d.b, g.Bs, digit, d.i);

    assert BEDigitSeqToInt(pv,Ms) == DigitAt(g.As,d.i) * power(pv,d.i) * BEDigitSeqToInt(pv,g.Bs);

    var running_sum,Rs' := PNAddWrapper(d.running_sum, g.Rs, middle_sum, Ms);
    assert BEDigitSeqToInt(pv,Rs') == BEDigitSeqToInt(pv,g.Rs) + BEDigitSeqToInt(pv,Ms);

    ghost var a_fragment := ArrayDigitAt(d.a,d.i)*power(pv,d.i);
    assert a_fragment == DigitAt(g.As,d.i)*power(pv,d.i);
    ghost var a_partial_sum := a_fragment + g.wks[|g.wks|-1].a_partial_sum;
    ghost var rowi := MulRow_c(
        a_fragment, a_partial_sum, BEWordSeqToInt(Rs'));
    ghost var wks' := g.wks + [rowi];

    d' := FNMulData_c(d.a, d.b, running_sum, d.i+1);
    g' := FNMulGhost_c(g.As, g.Bs, Rs', wks');

    lemma_FNMultiply_inductive_step(pv, g.As, g.Bs, g.Rs, g.wks, d.i, Ms, a_fragment, a_partial_sum, rowi, g'.Rs, g'.wks, d'.i);
}

method FNMultiply_conclusion_kit(d:FNMulData, ghost g:FNMulGhost) returns (p:array<int>)
    requires FNMultiply_loop_invariant_kit(d, g);
    requires d.i == |g.As|;
    ensures p!=null;
    ensures IsWordSeq(p[..]);
    ensures BEWordSeqToInt(d.a[..]) * BEWordSeqToInt(d.b[..]) == BEWordSeqToInt(p[..]);
{
    ghost var pv := power2(32);
    p := d.running_sum;
    assert g.As[|g.As|-d.i..] == g.As;    //- OBSERVE
    assert g.As == d.a[..]; //- OBSERVE

    assert PNWksReflectsBEDigits(pv, g.wks, g.As);
    assert FNMulRowReflectsBEDigits(pv, g.wks, |g.wks|-1, g.As);  //- OBSERVE
    ghost var Av := BEDigitSeqToInt(pv, g.As);
    ghost var Bv := BEDigitSeqToInt(pv, g.Bs);
//-    calc {
//-        wks[|wks|-1].a_partial_sum;
//-        BEDigitSeqToInt(pv, As[|As|-1-(|wks|-1)..]);
//-        Av;
//-    }
//-    assert g.wks[|g.wks|-1].a_partial_sum == Av;
//-    assert FNMulEnd(g.wks[|g.wks|-1], BEDigitSeqToInt(pv, g.Rs), Av);
//-    assert FNMulProblemValid(g.wks, BEDigitSeqToInt(pv, g.Rs), Av, Bv, 0);
    reveal_BEDigitSeqToInt_private();
//-    assert FNMulProblemValid(g.wks, BEDigitSeqToInt(pv, g.Rs), BEDigitSeqToInt(pv, g.As), BEDigitSeqToInt(pv, g.Bs), BEDigitSeqToInt(pv, []));
//-    assert FNMulProblemReflectsBESeq(pv, g.wks, g.Rs, g.As, g.Bs, []);
//-    assert FNMulProblemReflectsBESeq(pv, g.wks, p[..], d.a[..], d.b[..], []);
    lemma_FNMultiplication_BE(pv, g.wks, p[..], d.a[..], d.b[..], []);
}

method FatNatMul(a:array<int>, b:array<int>) returns (p:array<int>)
    requires a!=null;
    requires b!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires IsDigitSeq(power2(32), b[..]);
    ensures p!=null;
    ensures IsDigitSeq(power2(32), p[..]);
    ensures BEWordSeqToInt(a[..]) * BEWordSeqToInt(b[..]) == BEWordSeqToInt(p[..]);
{
    ProfileTally(Tally_FatNatMul(), 1);

    //- 0* case
    if (a.Length==0)
    {
        lemma_2toX32();
        reveal_BEDigitSeqToInt_private();
        lemma_mul_basics_forall();
        lemma_mul_nonnegative_forall();
        p := new int[0];
        return;
    }

    var d:FNMulData;
    ghost var g:FNMulGhost;
    d,g := FNMultiply_init_kit(a, b);

    while (d.i < a.Length)
        invariant a[..] == g.As;
        invariant b[..] == g.Bs;
        invariant FNMultiply_loop_invariant_kit(d, g);
        invariant d.a == a;
        invariant d.b == b;
    {
        d,g := FNMultiply_step_kit(d, g);
    }

    p := FNMultiply_conclusion_kit(d, g);
    calc {
        BEWordSeqToInt(a[..]) * BEWordSeqToInt(b[..]);
        BEWordSeqToInt(d.a[..]) * BEWordSeqToInt(d.b[..]);
        BEWordSeqToInt(p[..]);
    }
}
