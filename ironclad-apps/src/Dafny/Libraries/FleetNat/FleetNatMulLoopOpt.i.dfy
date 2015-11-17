include "FleetNatMulOpt.i.dfy"
include "FleetNatMulLoopOptLemmas.i.dfy"

// Bryan, here's the most important loop we run. This is a working
// implementation that calls out to your FleetNatMulMathOpt inner-loop
// to exploit adc propagation.
// Your goal is to optimize the loop, in particular by inlining the
// mul/add/adc bit. I think we'll get a bunch of benefit even without
// unrolling.

method FleetNatMul_one_loop_opt(c:array<int>, bi:nat, a:array<int>, adigits:int, bv:int) returns (carry:int)
    requires c!=null;
    requires IsDigitSeq(power2(32), c[..]);
    requires a!=c;
    requires a!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires 0<adigits<=a.Length;
    requires adigits + bi <= c.Length;
    requires c.Length - 1 - bi >= 0;
    requires a.Length > 0;
    requires c.Length > 0;
    requires 0 <= bv < power2(32);
    modifies c;
    ensures 0 <= carry < power2(32);
    ensures IsDigitSeq(power2(32), c[..]);
    ensures BEWordSeqToInt(c[..]) + carry*power(power2(32), adigits+bi)
        == BEWordSeqToInt(old(c[..]))
         + BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0)) * bv * power(power2(32), bi);
    ensures forall k :: 0 <= k < c.Length-1-(adigits+bi) ==> c[k] == old(c[k]);
{
    ghost var pv := power2(32);
    lemma_2toX();
    ghost var oldcs := c[..];

    var alenm1 := a.Length-1;
    var clenm1 := c.Length-1;
    var j := 0;
    carry := 0;
    lemma_BEWordSeqToInt_SelectDigitRange_empty(a[..]); //- establish partial sum invariant

    while (j < adigits)
        invariant 0<=j<=adigits;
        invariant IsDigitSeq(pv, c[..]);
        invariant 0<=carry<pv;
        //- partial sum invariant:
        invariant BEWordSeqToInt(c[..]) + carry*power(pv, j+bi)
            == BEWordSeqToInt(oldcs)
             + BEWordSeqToInt(SelectDigitRange(a[..], j, 0)) * bv * power(pv, bi);
        invariant forall k :: 0 <= k < c.Length-1-(j+bi) ==> c[k] == old(c[k]);
    {
        ghost var lastj := j;
        ghost var lastcarry := carry;
        ghost var lastcs := c[..];
        ghost var asq := a[..];

        var ci := clenm1 - (j+bi);
        var ai := alenm1 - j;
        var aj := a[ai];
        var lastcj := c[ci];
        var newcj;

//- #if opt
        newcj,carry := FleetNatMulMathOpt(aj, bv, lastcj, carry);
//- #endif opt
//- #if standard
//-        //- mul
//-        lemma_mod_properties();
//-        lemma_word32(aj);
//-        lemma_word32(bv);
//-        var mhi,mlo := asm_Mul64(aj, bv);
//-        lemma_asm_Mul64(aj, bv, mhi, mlo);
//-
//-        //- add1
//-        lemma_word32(mlo);
//-        lemma_word32(lastcarry);
//-        var add1 := asm_Add(mlo, carry);
//-        var carry1 := 0;
//-        if (add1 < carry) { carry1 := 1; }
//-        lemma_asm_Add_properties(mlo, lastcarry, add1, carry1);
//-
//-        //- add2
//-        lemma_word32(lastcj);
//-        newcj := asm_Add(add1, lastcj);
//-        var carry2 := 0;
//-        if (newcj < lastcj) { carry2 := 1; }
//-        lemma_asm_Add_properties(add1, lastcj, newcj, carry2);
//-
//-        //- add3
//-        lemma_word32(carry1);
//-        lemma_word32(carry2);
//-        var add3 := asm_Add(carry1, carry2);
//-        ghost var carry3 := 0;
//-        if (add3 < carry2) { carry3 := 1; }
//-        lemma_asm_Add_properties(carry1, carry2, add3, carry3);
//-
//-        //- add4
//-        carry := asm_Add(add3, mhi);
//-        ghost var carry4 := 0;
//-        if (carry < mhi) { carry4 := 1; }
//-        lemma_asm_Add_properties(add3, mhi, carry, carry4);
//-
//-        lemma_FleetNatMul_one_element_properties(pv,
//-            aj, bv, mhi, mlo,
//-            lastcarry, add1, carry1,
//-            lastcj, newcj, carry2,
//-            add3, carry3,
//-            carry, carry4);
//- #endif standard

        c[ci] := newcj;
        j := j + 1;

        lemma_FleetNatMul_one_partial_sum_induction(
            pv, oldcs, lastcs, c[..], a[..], adigits, bi, bv, j, lastj, carry, lastcarry,
            lastcj, newcj);
    }
}

