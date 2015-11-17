include "FatNatDivDefs.i.dfy"
include "../FleetNat/FleetNatMul.i.dfy"
include "CanonicalArrays.i.dfy"

datatype FNDivReciprocal = FNDivKnownReciprocal(w:int, TwoTo32wDividedByD:array<int>) |
                           FNDivUnknownReciprocal();

predicate FNDivReciprocalValid(reciprocal:FNDivReciprocal, dv:array<int>)
    reads dv;
    reads if reciprocal.FNDivKnownReciprocal? then reciprocal.TwoTo32wDividedByD else dv;
{
    dv != null &&
    IsWordSeq(dv[..]) &&
    BEWordSeqToInt(dv[..]) != 0 &&
    (reciprocal.FNDivKnownReciprocal? ==>
        (reciprocal.w >= dv.Length * 2 &&
         reciprocal.TwoTo32wDividedByD != null &&
         IsWordSeq(reciprocal.TwoTo32wDividedByD[..]) &&
         BEWordSeqToInt(reciprocal.TwoTo32wDividedByD[..]) == power2(32*reciprocal.w) / BEWordSeqToInt(dv[..])))
}

lemma Lemma_RemovingLastWordDividesBy2To32(s:seq<int>)
    requires |s| > 0;
    requires IsWordSeq(s);
    ensures BEWordSeqToInt(s[..|s|-1]) == BEWordSeqToInt(s) / power2(32);
{
    var pv := power2(32);
    lemma_2toX();
    lemma_BEInterpretation(pv, s, 1);
    lemma_power2_unfolding(32, 1);
    lemma_BEDigitSeqToInt_bound(pv, s[|s|-1..]);
    lemma_fundamental_div_mod_converse(
        BEDigitSeqToInt(pv, s),
        pv,
        BEDigitSeqToInt(pv, s[..|s|-1]),
        BEDigitSeqToInt(pv, s[|s|-1..]));
}

lemma Lemma_RemovingLastNWordsDividesBy2To32n(s:seq<int>, n:nat)
    requires |s| >= n;
    requires IsWordSeq(s);
    ensures BEWordSeqToInt(s[..|s|-n]) == BEWordSeqToInt(s) / power2(32 * n);
    decreases n;
{
    if n == 0 {
        calc {
            BEWordSeqToInt(s[..|s|-n]);
            { assert s == s[..|s|]; }
            BEWordSeqToInt(s);
            BEWordSeqToInt(s) / 1;
            { reveal_power2(); lemma_div_is_div_boogie(BEWordSeqToInt(s), 1); }
            BEWordSeqToInt(s) / power2(0);
            BEWordSeqToInt(s) / power2(32 * n);
        }
    }
    else {
        Lemma_RemovingLastNWordsDividesBy2To32n(s, n-1);
        assert BEWordSeqToInt(s[..|s|-(n-1)]) == BEWordSeqToInt(s) / power2(32 * (n-1));
        calc {
            BEWordSeqToInt(s[..|s|-n]);
            { Lemma_RemovingLastWordDividesBy2To32(s[..|s|-(n-1)]); assert var q := s[..|s|-(n-1)]; q[..|q|-1] == s[..|s|-n]; }
            BEWordSeqToInt(s[..|s|-(n-1)]) / power2(32);
            { Lemma_RemovingLastNWordsDividesBy2To32n(s, n-1); }
            (BEWordSeqToInt(s) / power2(32 * (n-1))) / power2(32);
            { assert BEWordSeqToInt_premium(s) >= 0;
              lemma_div_denominator(BEWordSeqToInt(s), power2(32 * (n-1)), power2(32));
              lemma_power2_positive();
              lemma_mul_strictly_positive(power2(32 * (n-1)), power2(32)); }
            BEWordSeqToInt(s) / (power2(32 * (n-1)) * power2(32));
            { lemma_power2_adds(32 * (n-1), 32); }
            BEWordSeqToInt(s) / power2(32 * (n-1) + 32);
            BEWordSeqToInt(s) / power2(32 * n);
        }
    }
}

method FNShiftRightByWords(n:array<int>, w:nat) returns (r:array<int>)
    requires n != null;
    requires IsWordSeq(n[..]);
    ensures r != null;
    ensures fresh(r);
    ensures IsWordSeq(r[..]);
    ensures BEWordSeqToInt(r[..]) == BEWordSeqToInt(n[..]) / power2(32*w);
{
    if n.Length <= w {
        lemma_BEDigitSeqToInt_bound(power2(32), n[..]);
        calc {
            BEWordSeqToInt(n[..]);
            < power(power2(32), n.Length);
            { lemma_power2_is_power_2(32); }
            power(power(2, 32), n.Length);
            { lemma_power_multiplies(2, 32, n.Length); lemma_mul_is_mul_boogie(32, n.Length); }
            power(2, 32 * n.Length);
            { lemma_power2_is_power_2(32 * n.Length); }
            power2(32 * n.Length);
            <= { lemma_mul_is_commutative_forall();
                 lemma_mul_is_mul_boogie(32, n.Length);
                 lemma_mul_is_mul_boogie(32, w);
                 lemma_mul_inequality(n.Length, w, 32);
                 lemma_power2_increases(32 * n.Length, 32 * w); }
               power2(32 * w);
        }
        r := new int[0];
        calc {
            BEWordSeqToInt(r[..]);
            { assert r[..] == []; }
            BEWordSeqToInt([]);
            { reveal_BEDigitSeqToInt_private(); }
            0;
            { lemma_small_div(); }
            BEWordSeqToInt(n[..]) / power2(32*w);
        }
        return;
    }

    r := new int[n.Length - w];

    var i := 0;
    assert IsWordSeq(n[..]);
    while i < r.Length
        invariant 0 <= i <= r.Length;
        invariant r[..i] == n[..i];
        invariant IsWordSeq(r[..i]);
    {
        r[i] := n[i];
        assert r[..i+1] == r[..i] + [r[i]];
        assert n[..i+1] == n[..i] + [n[i]];
        i := i + 1;
    }

    assert r[..] == n[..r.Length];
    Lemma_RemovingLastNWordsDividesBy2To32n(n[..], w);
    assert BEWordSeqToInt(r[..]) == BEWordSeqToInt(n[..]) / power2(32*w);
}

lemma Lemma_AnyDigitNonzeroMakesValueNonzero(s:seq<int>, i:int)
    requires IsWordSeq(s);
    requires 0 <= i < |s|;
    requires s[i] != 0;
    ensures BEWordSeqToInt(s) != 0;
    decreases |s|;
{
    reveal_BEDigitSeqToInt_private();
    if i == |s| - 1 {
        calc {
            BEWordSeqToInt_premium(s);
            BEWordSeqToInt_premium(s[0..|s|-1])*power2(32) + s[|s|-1];
            >= { lemma_mul_inequality(0, BEWordSeqToInt_premium(s[0..|s|-1]), power2(32)); lemma_mul_is_mul_boogie(0, power2(32)); }
               0*power2(32) + s[|s|-1];
            s[|s|-1];
            > 0;
        }
    }
    else {
        Lemma_AnyDigitNonzeroMakesValueNonzero(s[0..|s|-1], i);
        calc {
            BEWordSeqToInt_premium(s);
            BEWordSeqToInt_premium(s[0..|s|-1])*power2(32) + s[|s|-1];
            > { lemma_mul_strict_inequality(0, BEWordSeqToInt_premium(s[0..|s|-1]), power2(32)); lemma_mul_is_mul_boogie(0, power2(32)); }
              0*power2(32) + s[|s|-1];
            s[|s|-1];
            >= 0;
        }
    }
}

method IsFatNatZero(n:array<int>) returns (b:bool)
    requires n != null;
    requires IsWordSeq(n[..]);
    ensures b == (BEWordSeqToInt(n[..]) == 0);
{
    var i := 0;

    calc {
        BEWordSeqToInt(n[..0]);
        { assert n[..0] == []; }
        BEWordSeqToInt([]);
        { reveal_BEDigitSeqToInt_private(); }
        0;
    }

    while i < n.Length
        invariant 0 <= i <= n.Length;
        invariant forall j :: 0 <= j < i ==> n[j] == 0;
        invariant BEWordSeqToInt(n[..i]) == 0;
    {
        if n[i] != 0 {
            b := false;
            Lemma_AnyDigitNonzeroMakesValueNonzero(n[..], i);
            return;
        }
        calc {
            BEWordSeqToInt(n[..i+1]);
            { assert |n[..i+1]| == i+1; assert n[..i+1][0..i] == n[..i]; reveal_BEDigitSeqToInt_private(); }
            BEWordSeqToInt(n[..i])*power2(32) + n[i];
            { lemma_mul_is_mul_boogie(0, power2(32)); }
            0*power2(32) + n[i];
            n[i];
            0;
        }
        i := i + 1;
    }

    b := true;
    assert n[..] == n[..i];
}

lemma Lemma_VerySpecificDivisionInequality(x:int, y:int, z:int)
    requires x >= 0;
    requires y > 0;
    requires z > 0;
    ensures (x * (y / z) / y) * z <= x;
{
    var y_div_z := y / z;
    var y_mod_z := y % z;
    var w := x * y_div_z;
    var w_div_y := w / y;
    var w_mod_y := w % y;

    calc {
         x * y + z * w_mod_y + x * y_mod_z;
         >= { lemma_mod_properties(); lemma_mul_nonnegative(z, w_mod_y); lemma_mul_nonnegative(x, y_mod_z); }
            x * y;
         { lemma_fundamental_div_mod(y, z); }
         x * (z * y_div_z + y_mod_z);
         { lemma_mul_is_distributive_add(x, z * y_div_z, y_mod_z); }
         x * (z * y_div_z) + x * y_mod_z;
    }
    calc {
        x * y + z * w_mod_y;
        >= x * (z * y_div_z);
        { lemma_mul_is_commutative(z, y_div_z); }
        x * (y_div_z * z);
        { lemma_mul_is_associative(x, y_div_z, z); }
        (x * y_div_z) * z;
        w * z;
        { lemma_fundamental_div_mod(w, y); }
        (y * w_div_y + w_mod_y) * z;
        { lemma_mul_is_commutative(y * w_div_y + w_mod_y, z); }
        z * (y * w_div_y + w_mod_y);
        { lemma_mul_is_distributive_add(z, y * w_div_y, w_mod_y); }
        z * (y * w_div_y) + z * w_mod_y;
    }
    calc {
        x * y;
        >= z * (y * w_div_y);
        { lemma_mul_is_commutative(y, w_div_y); }
        z * (w_div_y * y);
        { lemma_mul_is_associative(z, w_div_y, y); }
        (z * w_div_y) * y;
        { lemma_mul_is_commutative(z, w_div_y); }
        (w_div_y * z) * y;
    }
    if x < w_div_y * z {
        lemma_mul_strict_inequality(x, w_div_y * z, y);
    }
    assert x >= w_div_y * z;
}

method FNDivision_Estimate_Q_Reciprocal(n:array<int>, dv:array<int>, reciprocal:FNDivReciprocal) returns (q:array<int>)
    requires n!=null;
    requires IsWordSeq(n[..]);
    requires dv!=null;
    requires IsWordSeq(dv[..]);
    requires 1 < BEWordSeqToInt(dv[..]) <= BEWordSeqToInt(n[..]);
    requires reciprocal.FNDivKnownReciprocal?;
    requires FNDivReciprocalValid(reciprocal, dv);
    ensures q!=null;
    ensures IsWordSeq(q[..]);
    ensures 0 < BEWordSeqToInt(q[..])*BEWordSeqToInt(dv[..]);
    ensures BEWordSeqToInt(q[..])*BEWordSeqToInt(dv[..]) <= BEWordSeqToInt(n[..]);
{
    ghost var g_x := BEWordSeqToInt(reciprocal.TwoTo32wDividedByD[..]);
    ghost var g_two_to_32w := power2(32 * reciprocal.w);
    ghost var g_dv := BEWordSeqToInt(dv[..]);
    ghost var w := reciprocal.w;
    ghost var g_y := g_two_to_32w - g_x * g_dv;
    ghost var g_n := BEWordSeqToInt(n[..]);
    ghost var g_nx := g_n * g_x;

    assert g_x == g_two_to_32w / g_dv;
    assert g_x * g_dv + g_y == g_two_to_32w;

    var nx := FleetNatMul(n, reciprocal.TwoTo32wDividedByD);

    assert BEWordSeqToInt(nx[..]) == g_nx;

    q := FNShiftRightByWords(nx, reciprocal.w);
    ghost var g_q := BEWordSeqToInt(q[..]);
    assert g_q == g_nx / power2(32*w);

    var q_is_zero := IsFatNatZero(q);
    if q_is_zero {
        lemma_2toX();
        q := MakeBELiteralArray(1);
        assert BEWordSeqToInt(q[..]) == 1;
        calc {
            BEWordSeqToInt_premium(q[..])*BEWordSeqToInt_premium(dv[..]);
            { lemma_mul_is_mul_boogie(1, BEWordSeqToInt_premium(dv[..])); }
            1*BEWordSeqToInt_premium(dv[..]);
            <= BEWordSeqToInt_premium(n[..]);
        }
    }
    else {
        calc {
            BEWordSeqToInt_premium(q[..])*BEWordSeqToInt_premium(dv[..]);
            g_q * g_dv;
            (g_nx / power2(32*w)) * g_dv;
            (g_n * g_x / power2(32*w)) * g_dv;
            (g_n * (power2(32*w) / g_dv) / power2(32*w)) * g_dv;
            <= { Lemma_VerySpecificDivisionInequality(g_n, power2(32*w), g_dv); }
            g_n;
        }
    }

    calc {
        BEWordSeqToInt_premium(q[..])*BEWordSeqToInt_premium(dv[..]);
        >= { lemma_mul_inequality(1, BEWordSeqToInt_premium(q[..]), BEWordSeqToInt_premium(dv[..]));
             lemma_mul_is_mul_boogie(1, BEWordSeqToInt_premium(dv[..])); }
           1*BEWordSeqToInt_premium(dv[..]);
        BEWordSeqToInt_premium(dv[..]);
        > 1;
    }
}
