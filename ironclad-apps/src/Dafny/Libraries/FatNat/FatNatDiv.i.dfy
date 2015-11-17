include "../Util/seqs_canonical.i.dfy"
include "FatNatDivDefs.i.dfy"
include "FatNatDivEstTrivial.i.dfy"
include "FatNatDivEstDiv32.i.dfy"
include "FatNatReciprocal.i.dfy"
include "../FleetNat/FleetNatMul.i.dfy"
include "../FleetNat/FleetNatSub.i.dfy"
include "CanonicalArrays.i.dfy"

method FNDivision_init(n:array<int>, dv:array<int>) returns (d:FNDivData, ghost g:FNDivGhost)
    requires n!=null;
    requires IsWordSeq(n[..]);
//-    requires n.Length < power2(27);
    requires dv!=null;
    requires IsWordSeq(dv[..]);
    requires 1<BEWordSeqToInt(dv[..]);
    ensures d.n == n;
    ensures d.dv == dv;
    ensures n[..] == g.Ns;
    ensures dv[..] == g.Ds;
    ensures FNDivision_invariant(d, g);
{
    var q := new int[0];
    ghost var Ds := dv[..];
//-    var r := CanonicalizeArray(n);    //- UNDONE length constraints
    var r := n;
    d := FNDivData_c(n, dv, r, q);
    ghost var base_row := MulRow_c(0, 0, 0);
    lemma_mul_basics_forall();
    g := FNDivGhost_c(n[..], Ds, r[..], [], [base_row], [BEWordSeqToInt(n[..])]);
    reveal_BEDigitSeqToInt_private();
}

method FNDivision_step(d:FNDivData, ghost g:FNDivGhost, reciprocal:FNDivReciprocal) returns (d':FNDivData, ghost g':FNDivGhost)
    requires FNDivision_invariant(d, g);
    requires BEWordSeqToInt(g.Ds) <= BEWordSeqToInt(g.Rs);
    requires FNDivReciprocalValid(reciprocal, d.dv);
    ensures FNDivision_invariant(d', g');
    ensures d'.n == d.n;
    ensures d'.dv == d.dv;
    ensures g'.Ns == g.Ns;
    ensures g'.Ds == g.Ds;
    ensures BEWordSeqToInt(d'.r[..]) < BEWordSeqToInt(d.r[..]);
    ensures FNDivReciprocalValid(reciprocal, d'.dv);
{
    ghost var Rs := d.r[..];
    ghost var Rv := BEWordSeqToInt(Rs);
    ghost var Ds := d.dv[..];
    ghost var Dv := BEWordSeqToInt(Ds);
    ghost var Qs := d.q[..];
    ghost var Qv := BEWordSeqToInt(Qs);
//-    var delq := FNDivision_Estimate_Q_trivial(d.r, d.dv);

//-    calc {
//-        BEDigitSeqToInt(power2(32), g.Rs);
//-        <=
//-        BEDigitSeqToInt(power2(32), g.Ns);
//-        <  { lemma_BEDigitSeqToInt_bound(power2(32), g.Ns); }
//-            power(power2(32), |g.Ns|);
//-        <= { lemma_power_increases(power2(32), |g.Ns|, power2(27)-1); }
//-            power(power2(32), power2(27)-1);
//-    }
//-    lemma_CanonicalLengthBound(power2(32), g.Rs, power2(27)-1);
//-    assert d.r.Length < power2(27);

    var dq_ref := d.q; //- do something real to d.q so dafnycc will realize that d.q is allocated, and thus that d.q is unaffected by methods that don't affect allocated parts of the heap
    var dr_ref := d.r; //- do something real to d.r
    var dn_ref := d.n; //- do something real to d.n
    var ddv_ref := d.dv; //- do something real to d.dv
    var recip_ref := if reciprocal.FNDivKnownReciprocal? then reciprocal.TwoTo32wDividedByD else d.q; //- do something real to reciprocal.TwoTo32wDividedByD

    var delq;
    if (reciprocal.FNDivKnownReciprocal?)
    {
        delq := FNDivision_Estimate_Q_Reciprocal(d.r, d.dv, reciprocal);
    }
    else
    {
        delq := FNDivision_Estimate_Q_div32(d.r, d.dv);
    }

    ghost var delQs := delq[..];
    ghost var delQv := BEWordSeqToInt(delQs);
    assert delQv * Dv <= Rv;
    ghost var last_row := g.wks[|g.wks|-1];
    ghost var new_row := MulRow_c(delQv, delQv+last_row.a_partial_sum, last_row.product+delQv*Dv);

    var local_product := FleetNatMul(delq, d.dv);
    ghost var local_product_s := local_product[..];
    ghost var local_product_v := BEWordSeqToInt(local_product_s);

    var r' := ICantBelieveItsNotFatNatSub(d.r, local_product);
    ghost var Rs' := r'[..];
    ghost var Rv' := BEWordSeqToInt(Rs');
    assert Rv' == Rv - local_product_v;

    
    
//-    var r'c := CanonicalizeArray(r');   //- UNDONE length constraints
    var r'c := r';

    ghost var Rs'c := r'c[..];
    ghost var Rs'v := BEWordSeqToInt(Rs'c);

    var q' := ICantBelieveItsNotFatNatAdd(d.q, delq);
    ghost var Qs' := q'[..];
    ghost var Qv' := BEWordSeqToInt(Qs');
    assert Qv' == Qv + delQv;

    
    d' := FNDivData_c(d.n, d.dv, r'c, q');
    g' := FNDivGhost_c(g.Ns, g.Ds, r'c[..], Qs', g.wks + [new_row], g.remainders+[Rv']);

    calc {
        g'.wks[|g.wks|].product;
        last_row.a_partial_sum * Dv + delQv * Dv;
        { lemma_mul_is_distributive_add_other_way(Dv, last_row.a_partial_sum, delQv); }
        (delQv+last_row.a_partial_sum) * Dv;
        g'.wks[|g.wks|].a_partial_sum * BEWordSeqToInt(g'.Ds);
    }
}

method FNDivision_conclusion(d:FNDivData, ghost g:FNDivGhost) returns (q:array<int>, r:array<int>)
    requires FNDivision_invariant(d, g);
    requires BEWordSeqToInt(g.Rs) < BEWordSeqToInt(g.Ds);
    ensures q!=null;
    ensures r!=null;
    ensures FNDivision_invariant(d, g); //- we don't lose any structure here
    ensures IsWordSeq(q[..]);
    ensures IsWordSeq(r[..]);
    ensures 0 <= BEWordSeqToInt(r[..]) < BEWordSeqToInt(d.dv[..]);
    ensures BEWordSeqToInt(d.n[..]) ==
        BEWordSeqToInt(d.dv[..]) * BEWordSeqToInt(q[..]) + BEWordSeqToInt(r[..]);
{
    q := d.q;
    r := d.r;

    lemma_BEDigitSeqToInt_bound(power2(32), r[..]);
    lemma_mul_is_commutative_forall();
}

method FNDivision_trivial(n:array<int>, dv:array<int>) returns (success:bool, q:array<int>, r:array<int>)
    requires n!=null;
    requires dv!=null;
    requires IsWordSeq(n[..]);
    requires IsWordSeq(dv[..]);
    ensures !success ==> 1!=BEWordSeqToInt(dv[..]);
    ensures success ==> q!=null && IsWordSeq(q[..]);
    ensures success ==> r!=null && IsWordSeq(r[..]);
    ensures success ==> 0 <= BEWordSeqToInt(r[..]) < BEWordSeqToInt(dv[..]);
    ensures success ==> BEWordSeqToInt(n[..]) ==
        BEWordSeqToInt(dv[..]) * BEWordSeqToInt(q[..]) + BEWordSeqToInt(r[..]);
    ensures success ==> BEWordSeqToInt(q[..]) == BEWordSeqToInt(n[..]) / BEWordSeqToInt(dv[..]);
    ensures success ==> BEWordSeqToInt(r[..]) == BEWordSeqToInt(n[..]) % BEWordSeqToInt(dv[..]);
    ensures n[..]==old(n[..]);
    ensures dv[..]==old(dv[..]);
{
    
    lemma_2toX();
    var one := MakeBELiteralArray(1);
    ghost var ones := one[..];
    assert BEWordSeqToInt(ones) == 1;
    ghost var divs := dv[..];
    var one_cmp:Cmp := FatNatCompare(one, dv);
    if (one_cmp.CmpEq?)
    {
        success := true;
        q := n;
        r := new int[0];
        reveal_BEDigitSeqToInt_private();
        lemma_mul_basics_forall();
        lemma_mul_is_commutative(BEWordSeqToInt(dv[..]), BEWordSeqToInt(q[..]));
        lemma_fundamental_div_mod_converse(BEWordSeqToInt_premium(n[..]), BEWordSeqToInt_premium(dv[..]), BEWordSeqToInt_premium(q[..]), BEWordSeqToInt_premium(r[..]));
        return;
    } else {
        q := new int[0];    //- dafnycc.
                            
        r := q;
        success := false;
    }
}

method FatNatDivUsingReciprocal(n:array<int>, dv:array<int>, reciprocal:FNDivReciprocal) returns (q:array<int>, r:array<int>)
    requires n!=null;
    requires dv!=null;
//-    requires n.Length < power2(27);
    requires IsWordSeq(n[..]);
    requires IsWordSeq(dv[..]);
    requires 0<BEWordSeqToInt(dv[..]);
    requires FNDivReciprocalValid(reciprocal, dv);
    ensures q!=null;
    ensures r!=null;
    ensures IsWordSeq(q[..]);
    ensures IsWordSeq(r[..]);
    ensures 0 <= BEWordSeqToInt(r[..]) < BEWordSeqToInt(dv[..]);
    ensures BEWordSeqToInt(n[..]) ==
        BEWordSeqToInt(dv[..]) * BEWordSeqToInt(q[..]) + BEWordSeqToInt(r[..]);
    ensures BEWordSeqToInt(q[..]) == BEWordSeqToInt(n[..]) / BEWordSeqToInt(dv[..]);
    ensures BEWordSeqToInt(r[..]) == BEWordSeqToInt(n[..]) % BEWordSeqToInt(dv[..]);
{
    var d;
    ghost var g;

    var recip_ref := if reciprocal.FNDivKnownReciprocal? then reciprocal.TwoTo32wDividedByD else n;

    var trivial;
    trivial,q,r := FNDivision_trivial(n, dv);
    if (trivial) {
        return;
    }

    d,g := FNDivision_init(n,dv);
    var r_ref := d.r; //- do something real to d.r to convince dafyncc it's allocated
    var q_ref := d.q; //- do something real to d.q to convince dafyncc it's allocated
    var r_d_cmp:Cmp := FatNatCompare(d.r, d.dv);
    assert FNDivReciprocalValid(reciprocal, dv);
    while (!r_d_cmp.CmpLt?)
        invariant d.n == n;
        invariant d.dv == dv;
        invariant FNDivision_invariant(d, g);
        invariant n[..] == g.Ns;    //- OBSERVE
        invariant dv[..] == g.Ds;  //- OBSERVE
        invariant FNDivReciprocalValid(reciprocal, d.dv);
        invariant (r_d_cmp==CmpLt) <==> (BEWordSeqToInt(g.Rs) < BEWordSeqToInt(g.Ds));
        decreases BEWordSeqToInt(d.r[..]);
    {
        ghost var old_d := d;
        d,g := FNDivision_step(d,g,reciprocal);
        var r_ref := d.r; //- do something real to d.r to convince dafyncc it's allocated
        var q_ref := d.q; //- do something real to d.q to convince dafyncc it's allocated
        assert BEWordSeqToInt(d.r[..]) < BEWordSeqToInt(old_d.r[..]);   //- OBSERVE
        r_d_cmp := FatNatCompare(d.r, d.dv);
    }
    q,r := FNDivision_conclusion(d, g);
    assert n[..] == g.Ns;   //- OBSERVE
    assert dv[..] == g.Ds; //- OBSERVE
    lemma_mul_is_commutative(BEWordSeqToInt(dv[..]), BEWordSeqToInt(q[..]));
    lemma_fundamental_div_mod_converse(BEWordSeqToInt_premium(n[..]), BEWordSeqToInt_premium(dv[..]), BEWordSeqToInt_premium(q[..]), BEWordSeqToInt_premium(r[..]));
}


method FatNatDiv(n:array<int>, dv:array<int>) returns (q:array<int>, r:array<int>)
    requires n!=null;
    requires dv!=null;
//-    requires n.Length < power2(27);
    requires IsWordSeq(n[..]);
    requires IsWordSeq(dv[..]);
    requires 0<BEWordSeqToInt(dv[..]);
    ensures q!=null;
    ensures r!=null;
    ensures IsWordSeq(q[..]);
    ensures IsWordSeq(r[..]);
    ensures 0 <= BEWordSeqToInt(r[..]) < BEWordSeqToInt(dv[..]);
    ensures BEWordSeqToInt(n[..]) ==
        BEWordSeqToInt(dv[..]) * BEWordSeqToInt(q[..]) + BEWordSeqToInt(r[..]);
    ensures BEWordSeqToInt(q[..]) == BEWordSeqToInt(n[..]) / BEWordSeqToInt(dv[..]);
    ensures BEWordSeqToInt(r[..]) == BEWordSeqToInt(n[..]) % BEWordSeqToInt(dv[..]);
{
    q, r := FatNatDivUsingReciprocal(n, dv, FNDivUnknownReciprocal());
}

lemma Lemma_OneFollowedByxZeroesIsPower2To32x(s:seq<int>)
    requires |s| > 0;
    requires s[0] == 1;
    requires forall i :: 1 <= i < |s| ==> s[i] == 0;
    requires IsWordSeq(s);
    ensures BEWordSeqToInt(s) == power2(32*(|s|-1));
{
    calc {
        BEWordSeqToInt(s);
        { reveal_BEDigitSeqToInt_private(); }
        BEWordSeqToInt(s[0..|s|-1])*power2(32) + s[|s|-1];
        { assert s[0..|s|-1] == s[..|s|-1]; }
        BEWordSeqToInt(s[..|s|-1])*power2(32) + s[|s|-1];
    }

    if |s| == 1 {
        calc {
            BEWordSeqToInt(s[..|s|-1])*power2(32) + s[|s|-1];
            { assert s[..|s|-1] == []; }
            BEWordSeqToInt([])*power2(32) + s[|s|-1];
            { reveal_BEDigitSeqToInt_private(); }
            { lemma_mul_is_mul_boogie(0, power2(32)); }
            0*power2(32) + s[|s|-1];
            s[|s|-1];
            s[0];
            1;
            { reveal_power2(); }
            power2(0);
            power2(32*(|s|-1));
        }
    }
    else {
        calc {
            BEWordSeqToInt(s[..|s|-1])*power2(32) + s[|s|-1];
            BEWordSeqToInt(s[..|s|-1])*power2(32);
            { Lemma_OneFollowedByxZeroesIsPower2To32x(s[..|s|-1]); }
            power2(32*(|s|-2)) * power2(32);
            { lemma_power2_adds(32*(|s|-2), 32); }
            power2(32*(|s|-2) + 32);
            power2(32*(|s|-1));
        }
     }
}

method FatNatPower2To32x(x:nat) returns (q:array<int>)
    ensures fresh(q);
    ensures q != null;
    ensures IsWordSeq(q[..]);
    ensures BEWordSeqToInt(q[..]) == power2(32 * x);
{
    q := new int[x+1];
    q[0] := 1;
    lemma_2toX();

    var i := 1;
    while i < q.Length
        invariant 1 <= i <= q.Length;
        invariant q[0] == 1;
        invariant forall j :: 1 <= j < i ==> q[j] == 0;
        invariant IsWordSeq(q[..i]);
    {
        q[i] := 0;
        i := i + 1;
    }

    assert q[..] == q[..q.Length];
    Lemma_OneFollowedByxZeroesIsPower2To32x(q[..]);
}

method FatNatComputeReciprocal(dv:array<int>) returns (reciprocal:FNDivReciprocal)
    requires dv != null;
    requires IsWordSeq(dv[..]);
    requires BEWordSeqToInt(dv[..]) > 0;
    ensures reciprocal.FNDivKnownReciprocal?;
    ensures FNDivReciprocalValid(reciprocal, dv);
{
    var w := dv.Length * 2;
    var two_to_32w := FatNatPower2To32x(w);
    var q,r := FatNatDiv(two_to_32w, dv);
    reciprocal := FNDivKnownReciprocal(w, q);
}
