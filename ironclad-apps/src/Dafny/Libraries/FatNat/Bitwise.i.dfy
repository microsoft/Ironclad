include "FatNatCommon.i.dfy"
include "FatNatMul.i.dfy"
include "CanonicalArrays.i.dfy"
include "../Math/power2methods.i.dfy"
include "../Util/seqs_common.i.dfy"
include "../Util/seqs_and_ints.i.dfy"



method BitShiftRight_Word(x:nat, b:nat) returns (xb:nat)
    requires IsWord(x);
    ensures IsWord(xb);
    ensures xb == x/power2(b);
{
    if (b>=32)
    {
        xb := 0;
        lemma_power2_increases(32,b);
        lemma_small_div();
        return;
    }
    lemma_power2_strictly_increases(b,32);
    var p2b := MakePower2(b);
    var r_discard;
    xb,r_discard := Divide32(x, p2b);
    lemma_fundamental_div_mod_converse(x, p2b, xb, r_discard);
}

method BitShiftLeft_Word(x:nat, b:nat) returns (xb:nat)
    requires IsWord(x);
    ensures IsWord(xb);
    ensures xb == (x*power2(b)) % power2(32);
{
    if (b>=32)
    {
        xb := 0;
        calc {
            (x*power2(b)) % power2(32);
                { lemma_power2_adds(b-32,32);
                  lemma_mul_is_associative_forall(); }
            (x*power2(b-32)*power2(32)) % power2(32);
                { lemma_mul_is_commutative_forall(); }
            power2(32)*(x*power2(b-32)) % power2(32);
                { lemma_mod_multiples_vanish(x*power2(b-32), 0, power2(32));
                  lemma_small_mod(0, power2(32));
                }
            0;
        }
        return;
    }
    lemma_power2_strictly_increases(b,32);
    var p2b := MakePower2(b);
    var r_discard;
    xb,r_discard := Product32(x, p2b);
    calc {
        (x*power2(b)) % power2(32);
        (xb + r_discard * power2(32)) % power2(32);
                { lemma_mul_is_commutative_forall(); }
        (power2(32)*r_discard + xb) % power2(32);
            { lemma_mod_multiples_vanish(r_discard, xb, power2(32));
              lemma_small_mod(xb, power2(32)); }
        xb;
    }
}

method {:dafnycc_conservative_seq_triggers} TakeTopBits_first_word_ge_p2b(n:array<int>, top_word:int, b:nat, first_word:int, n_length:int,
                                                                          ghost pv:int, ghost Ns_all:seq<int>, ghost Ns:seq<int>,
                                                                          ghost Nv:int) returns (s:int, e:nat)
    requires n!=null;
    requires IsWordSeq(n[..]);
    requires 0<=top_word<n.Length;
    requires forall j::0<=j<top_word ==> n[j]==0;
    requires 0<n.Length;
    requires n[top_word]!=0;
    requires 0 < b <= 32;
    requires n[top_word] >= power2(b);
    requires first_word == n[top_word];
    requires n_length == n.Length - top_word;
    requires pv == power2(32);
    requires Ns == n[top_word..];
    requires Ns_all == n[..];
    requires Nv == BEWordSeqToInt(Ns);
    requires BEDigitSeqToInt(pv, Ns) == BEDigitSeqToInt(pv, Ns_all);
    requires 0 < BEDigitSeqToInt(pv, Ns);
    ensures 0 < s < power2(b);
    ensures s == BEWordSeqToInt(n[..]) / power2(e);
    ensures b>0 && e>0 ==> power2(b-1) <= s;
{
    //- shift right a smidgen and we're done.
    var ne := CountBits(first_word);
    if (b > ne)
    {
        lemma_power2_strictly_increases(ne, b);
        assert false;
    }
    calc {
        b;
        <
        ne;
    }
    var shift := ne - b;
    s := BitShiftRight_Word(first_word, shift);
    e := 32*(n_length-1) + shift;
    assert e == 32*(|Ns|-1) + shift;
    if (0==s)
    {
        calc {
            first_word;
                { lemma_fundamental_div_mod(first_word, power2(shift)); }
            power2(shift) * (first_word/power2(shift)) + first_word%power2(shift);
            power2(shift) * s + first_word%power2(shift);
                { lemma_mul_basics(power2(shift)); }
            first_word%power2(shift);
            <   { lemma_mod_properties(); }
            power2(shift);
            <=  { lemma_power2_increases(shift, ne-1); }
            power2(ne-1);
            <=
            first_word;
        }
        assert false;
    }
    assert first_word < power2(ne);
    calc {
        s;
        first_word / power2(shift);
        first_word / power2(ne-b);
        <  { lemma_power2_adds(b, ne-b);
             lemma_div_by_multiple_is_strongly_ordered(first_word, power2(ne), power2(b), power2(ne-b)); }
        power2(ne) / power2(ne-b);
            { lemma_power2_div_is_sub(ne-b, ne); }
        power2(b);
    }
    assert 0 < s < power2(b);
    calc {
        BEWordSeqToInt(n[..]) / power2(e);
        BEWordSeqToInt(Ns_all) / power2(e);
        BEWordSeqToInt(Ns) / power2(e);
            { lemma_BEInterpretation(pv, Ns, |Ns|-1);
                assert Ns[..1] == [Ns[0]];  //- OBSERVE
                lemma_BEDigitSeqToInt_singleton(pv, Ns[0]);
            }
        (Ns[0]*power(pv, |Ns|-1) + BEWordSeqToInt(Ns[1..]))
            / power2(e);
            { lemma_power2_unfolding(32, |Ns|-1);
                lemma_mul_is_mul_boogie(32, |Ns|-1); }
        (Ns[0]*power2(32*(|Ns|-1)) + BEWordSeqToInt(Ns[1..]))
            / power2(e);
            { lemma_fundamental_div_mod(Ns[0], power2(shift)); }
        ((power2(shift)*(Ns[0]/power2(shift)) + Ns[0]%power2(shift))
         *power2(32*(|Ns|-1)) + BEWordSeqToInt(Ns[1..]))
            / power2(e);
            { lemma_mul_is_distributive_add_other_way(power2(32*(|Ns|-1)), power2(shift)*(Ns[0]/power2(shift)), Ns[0]%power2(shift)); }
        (power2(shift)*(Ns[0]/power2(shift))*power2(32*(|Ns|-1))
         + (Ns[0]%power2(shift))*power2(32*(|Ns|-1))
         + BEWordSeqToInt(Ns[1..]))
            / power2(e);
            { lemma_mul_is_associative(power2(shift), Ns[0]/power2(shift), power2(32*(|Ns|-1))); }
            { lemma_mul_is_commutative(Ns[0]/power2(shift), power2(32*(|Ns|-1))); }
            { lemma_mul_is_associative(power2(shift), power2(32*(|Ns|-1)), Ns[0]/power2(shift)); }
            { lemma_power2_adds(shift, 32*(|Ns|-1)); }
        (power2(e)*(Ns[0]/power2(shift))
         + (Ns[0]%power2(shift))*power2(32*(|Ns|-1))
         + BEWordSeqToInt(Ns[1..]))
            / power2(e);
            { lemma_mod_properties();
              lemma_mul_nonnegative(Ns[0]%power2(shift),power2(32*(|Ns|-1)));
              assert 0<=Ns[0]%power2(shift);
              assert 0<=power2(32*(|Ns|-1));
              calc {
                  (Ns[0]%power2(shift))*power2(32*(|Ns|-1))
                      + BEWordSeqToInt(Ns[1..]);
                  <=  { lemma_mod_properties();
                        lemma_mul_inequality(Ns[0]%power2(shift), power2(shift)-1, power2(32*(|Ns|-1))); }
                     (power2(shift)-1) * power2(32*(|Ns|-1))
                      + BEWordSeqToInt(Ns[1..]);
                  <   { lemma_BEDigitSeqToInt_bound(pv, Ns[1..]);
                        lemma_power2_unfolding(32, |Ns|-1);
                        lemma_mul_is_mul_boogie(32, |Ns|-1); }
                    (power2(shift)-1)* power2(32*(|Ns|-1))
                      + power2(32*(|Ns|-1));
                    { lemma_mul_basics_forall(); }
                  (power2(shift)-1)* power2(32*(|Ns|-1))
                      + mul(1,power2(32*(|Ns|-1)));
                    { lemma_mul_is_distributive_add_other_way(power2(32*(|Ns|-1)), power2(shift)-1, 1); }
                  power2(shift)*power2(32*(|Ns|-1));
                    { lemma_power2_adds(shift, 32*(|Ns|-1)); }
                  power2(e);
              }
              assert (Ns[0]%power2(shift))*power2(32*(|Ns|-1)) + BEWordSeqToInt(Ns[1..]) < power2(e);
              lemma_BEDigitSeqToInt_bound(pv, Ns[1..]);
              lemma_div_multiples_vanish_fancy(
                  Ns[0]/power2(shift),
                  (Ns[0]%power2(shift))*power2(32*(|Ns|-1)) + BEWordSeqToInt(Ns[1..]),
                  power2(e)); }
        Ns[0]/power2(shift);
        s;
    }
    if (0<b && 0<e)
    {
//-ensures x>0 ==> 0<e && power2(e-1) <= x;
        assert power2(ne-1) <= Ns[0];
        calc {
            power2(b-1);
                { lemma_power2_div_is_sub(ne-b,ne-1); }
            power2(ne-1)/power2(ne-b);
            <=  { lemma_div_is_ordered(power2(ne-1), Ns[0], power2(ne-b)); }
            Ns[0]/power2(ne-b);
            s;
        }
    }
}

method {:dafnycc_conservative_seq_triggers} TakeTopBits_inner(n:array<int>, top_word:int, b:nat) returns (s:int, e:nat)
    requires n!=null;
    requires IsWordSeq(n[..]);
    requires 0<=top_word<n.Length;
    requires forall j::0<=j<top_word ==> n[j]==0;
    requires 0<n.Length;
    requires n[top_word]!=0;
    requires 0 < b <= 32;
    ensures 0 < s < power2(b);
    ensures s == BEWordSeqToInt(n[..]) / power2(e);
    ensures b>0 && e>0 ==> power2(b-1) <= s;
{
    lemma_2toX();
    ghost var pv := power2(32);
    ghost var Ns_all := n[..];
    ghost var Ns := n[top_word..];
    lemma_LeadingZeros(pv, Ns, Ns_all);
    ghost var Nv := BEWordSeqToInt(Ns);
    assert Nv == BEWordSeqToInt(Ns_all);
    calc {
        0;
        <   { lemma_power_positive(pv, |Ns|-1);
              lemma_mul_strictly_positive(Ns[0], power(pv, |Ns|-1)); }
        Ns[0] * power(pv, |Ns|-1);
        <=  { lemma_BEDigitSeqToInt_bound(pv, Ns); }
        BEDigitSeqToInt(pv, Ns);
    }

    var first_word := n[top_word];
    var n_length := n.Length - top_word;
    var first_word_ge_p2b:bool;

    if (b==32) {
        first_word_ge_p2b := false;
        assert first_word < power2(b);
    } else {
        var p2b := MakePower2(b);
        first_word_ge_p2b := (first_word >= p2b);
    }
    assert first_word_ge_p2b == (first_word >= power2(b));

    if (first_word_ge_p2b)
    {
        s, e := TakeTopBits_first_word_ge_p2b(n, top_word, b, first_word, n_length, pv, Ns_all, Ns, Nv);
    }
    else if (n_length == 1)
    {
        s := first_word;
        lemma_BEDigitSeqToInt_singleton(pv, s);
        assert Ns==[s]; //- OBSERVE SEQS
        assert BEWordSeqToInt(n[..])==s;
        e := 0;
        lemma_power2_0_is_1();
        lemma_div_basics(BEWordSeqToInt(n[..]));
    }
    else
    {
        //- Need a left shift and some high bits from next word down.
        //- This is a lot like the case above, but even longer since
        //- we have to shuffle more power2()s around.
        var ne := CountBits(first_word);

        if (b <= ne-1)
        {
            lemma_power2_increases(b, ne-1);
//-            assert p2b <= power2(ne-1) <= first_word < p2b;
        }

        assert 0 < ne <= b;

        var left_shift := b - ne;
        var hi_s := BitShiftLeft_Word(first_word, left_shift);

        calc {
            first_word*power2(left_shift);
            <   { lemma_mul_strict_inequality(first_word, power2(ne), power2(left_shift)); }
            power2(ne)*power2(left_shift);
                { lemma_power2_adds(ne, left_shift); }
            power2(b);
            <=   { lemma_power2_increases(b,32); }
            power2(32);
        }
        lemma_mul_nonnegative(first_word, power2(left_shift));
        lemma_small_mod(first_word*power2(left_shift), power2(32));

        var second_word := n[top_word+1];
        var right_shift := 32 - left_shift;
        var low_s := BitShiftRight_Word(second_word, right_shift);

        s := hi_s + low_s;
        e := 32*(n_length-1) - left_shift;

        lemma_mul_strictly_positive(first_word, power2(left_shift));
        assert 0 < hi_s;

        assert 0 <= low_s;
        calc {
            low_s;
            second_word/power2(right_shift);
            <  { lemma_power2_adds(32-right_shift, right_shift);
                 lemma_div_by_multiple_is_strongly_ordered(second_word, power2(32), power2(32 - right_shift), power2(right_shift)); }
            power2(32)/power2(right_shift);
                { lemma_power2_div_is_sub(right_shift, 32); }
            power2(left_shift);
        }
        calc {
            s;
            hi_s + low_s;
            first_word*power2(left_shift) + low_s;
            <
            first_word*power2(left_shift) + power2(left_shift);
                { lemma_mul_basics_forall(); }
            first_word*power2(left_shift) + mul(1,power2(left_shift));
                { lemma_mul_is_distributive_add_other_way(power2(left_shift), first_word, 1); }
            (first_word+1)*power2(left_shift);
            <=  { lemma_mul_inequality(first_word+1, power2(ne), power2(left_shift)); }
            power2(ne)*power2(left_shift);
                { lemma_power2_adds(ne, left_shift); }
            power2(b);
        }
        assert 0 < s < power2(b);
        calc {
            BEWordSeqToInt(Ns);
                { lemma_BEInterpretation(pv, Ns, n_length-1);
                  assert Ns[..1] == [Ns[0]];  //- OBSERVE
                  lemma_BEDigitSeqToInt_singleton(pv, Ns[0]);
                  lemma_power2_unfolding(32, n_length-1);
                  lemma_mul_is_mul_boogie(32, n_length-1); }
            first_word*power2(32*(n_length-1)) + BEWordSeqToInt(Ns[1..]);
                { lemma_BEInterpretation(pv, Ns[1..], n_length-2);
                  assert Ns[1..][..1] == [Ns[1]];  //- OBSERVE
                  assert Ns[1..][1..] == Ns[2..];  //- OBSERVE
                  lemma_BEDigitSeqToInt_singleton(pv, Ns[1]);
                  lemma_power2_unfolding(32, n_length-2);
                  lemma_mul_is_mul_boogie(32, n_length-2); }
            first_word*power2(32*(n_length-1))
                + second_word*power2(32*(n_length-2))
                + BEWordSeqToInt(Ns[2..]);
                { lemma_power2_adds(left_shift, 32*(n_length-1)-left_shift);
                  lemma_mul_is_associative_forall(); }
            hi_s*power2(e)
                + second_word*power2(32*(n_length-2))
                + BEWordSeqToInt(Ns[2..]);
                { lemma_fundamental_div_mod(second_word, power2(right_shift)); }

            hi_s*power2(e)
                + (power2(right_shift)*low_s + second_word%power2(right_shift))
                    *power2(32*(n_length-2))
                + BEWordSeqToInt(Ns[2..]);
            {
              calc {
                (power2(right_shift)*low_s + second_word%power2(right_shift))
                    *power2(32*(n_length-2));
                    { lemma_mul_is_distributive_add_other_way(power2(32*(n_length-2)), power2(right_shift)*low_s, second_word%power2(right_shift)); }
                (power2(right_shift)*low_s)*power2(32*(n_length-2))
                    +(second_word%power2(right_shift))*power2(32*(n_length-2));
                    { lemma_mul_is_commutative(power2(right_shift), low_s); }
                (low_s*power2(right_shift))*power2(32*(n_length-2))
                    +(second_word%power2(right_shift))*power2(32*(n_length-2));
                    { lemma_mul_is_associative(low_s, power2(right_shift), power2(32*(n_length-2))); }
                low_s*(power2(right_shift)*power2(32*(n_length-2)))
                    +(second_word%power2(right_shift))*power2(32*(n_length-2));
                    { lemma_power2_adds(right_shift, 32*(n_length-2)); }
                low_s*power2(e)
                    +(second_word%power2(right_shift))*power2(32*(n_length-2));
              }
            }
            hi_s*power2(e)
                + low_s*power2(e)
                + (second_word%power2(right_shift)) * power2(32*(n_length-2))
                + BEWordSeqToInt(Ns[2..]);
                { lemma_mul_is_distributive_add_other_way(power2(e), hi_s, low_s); }
            s*power2(e)
                + (second_word%power2(right_shift)) * power2(32*(n_length-2))
                + BEWordSeqToInt(Ns[2..]);
        }

        calc {
            0;
            <= { lemma_mod_properties(); assert(power2(right_shift) > 0); }
            second_word%power2(right_shift);
        }
        lemma_mul_nonnegative(
            second_word%power2(right_shift),
            power2(32*(n_length-2)));
        lemma_BEDigitSeqToInt_bound(pv, Ns[2..]);
        calc {
            (second_word%power2(right_shift)) * power2(32*(n_length-2))
                + BEWordSeqToInt(Ns[2..]);
            <   { lemma_power2_unfolding(32, n_length-2);
                  lemma_mul_is_mul_boogie(32, n_length-2); }
            (second_word%power2(right_shift)) * power2(32*(n_length-2))
                + power2(32*(n_length-2));
            <=  { lemma_mod_properties();
                  lemma_mul_inequality(
                    second_word%power2(right_shift),
                    (power2(right_shift)-1),
                    power2(32*(n_length-2))); }
            (power2(right_shift)-1) * power2(32*(n_length-2))
                + power2(32*(n_length-2));
                { lemma_mul_basics_forall(); }
            (power2(right_shift)-1) * power2(32*(n_length-2))
                + mul(1,power2(32*(n_length-2)));   //- OBSERVE
                { lemma_mul_is_distributive_add_other_way(power2(32*(n_length-2)), power2(right_shift)-1, 1); }
            power2(right_shift) * power2(32*(n_length-2));
                { lemma_power2_adds(right_shift, 32*(n_length-2)); }
            power2(e);
        }
        lemma_div_multiples_vanish_fancy(s,
                (second_word%power2(right_shift)) * power2(32*(n_length-2))
                    + BEWordSeqToInt(Ns[2..]),
                power2(e));
        lemma_mul_is_commutative_forall();
        assert s == BEWordSeqToInt(n[..]) / power2(e);

        if (b>0 && e>0)
        {
            calc {
                power2(b-1);
                    { lemma_power2_adds(ne-1, left_shift); }
                power2(ne-1)*power2(left_shift);
                <=  { lemma_mul_inequality(power2(ne-1), first_word, power2(left_shift)); }
                first_word*power2(left_shift);
                <=
                s;
            }
        }
    }
}

method {:dafnycc_conservative_seq_triggers} TakeTopBits(n:array<int>, b:nat) returns (s:int, e:nat)
    requires n!=null;
    requires IsWordSeq(n[..]);
    requires BEWordSeqToInt(n[..])!=0;
    requires 0 < b <= 32;
    ensures 0 < s < power2(b);
    ensures s == BEWordSeqToInt(n[..]) / power2(e);
    ensures b>0 && e>0 ==> power2(b-1) <= s;
{
    lemma_2to32();
    ghost var Ns := n[..];

    if (n.Length==0)
    {
        reveal_BEDigitSeqToInt_private();
//-        assert n[..] == Ns;
        assert BEWordSeqToInt(n[..])==0;
        assert false;
    }
    var top_word := CountTopZeroWords(n);
    if (top_word==n.Length)
    {
        lemma_LeadingZeros(power2(32), [], Ns);
        reveal_BEDigitSeqToInt_private();
//-        assert BEWordSeqToInt(Ns)==0;
//-        assert BEWordSeqToInt(n[..])==0;
        s := 0; e := 0; //- dafnycc
        assert false;
        return;
    }
    s,e := TakeTopBits_inner(n, top_word, b);
}

method BitShiftLeft_Array(x:array<int>, b:nat) returns (xb:array<int>)
    requires x!=null;
    requires IsWordSeq(x[..]);
    requires IsWord(b);
    ensures xb!=null;
    ensures IsWordSeq(xb[..]);
    ensures BEWordSeqToInt(xb[..]) == BEWordSeqToInt(x[..])*power2(b);
    
{
    lemma_2toX();
    var s_words, s_bits := Divide32(b, 32);
    lemma_mul_is_mul_boogie(s_words, 32);
    lemma_mod_properties();
    var base_word := MakePower2(s_bits);
    lemma_power2_strictly_increases(s_bits, 32);
    var Xs := x[..];

    xb := MultiplyOneRow(x, base_word, s_words);
    calc {
        BEWordSeqToInt(xb[..]);
        base_word * power2(32*s_words) * BEWordSeqToInt(x[..]);
        base_word * power2(32*s_words) * BEWordSeqToInt(Xs);
        power2(s_bits) * power2(32*s_words) * BEWordSeqToInt(Xs);
            { lemma_power2_adds(s_bits, 32*s_words); }
        power2(s_bits + 32*s_words) * BEWordSeqToInt(Xs);
        power2(b) * BEWordSeqToInt(Xs);
            { lemma_mul_is_commutative_forall(); }
        BEWordSeqToInt(Xs) * power2(b);
        BEWordSeqToInt(x[..]) * power2(b);
    }
}

predicate FatNatBitCount(X:seq<int>, e:nat)
    requires IsWordSeq(X);
{
    true
    && (e>0 ==> 0<BEWordSeqToInt(X))
    && (e>0 ==> power2(e-1) <= BEWordSeqToInt(X))
    && (BEWordSeqToInt(X)>0
        ==> 0<e && power2(e-1) <= BEWordSeqToInt(X))
    && (BEWordSeqToInt(X) < power2(e))
}

method FatNatCountBits(x:array<int>) returns (e:nat)
    requires x!=null && IsWordSeq(x[..]);
    ensures FatNatBitCount(x[..], e);
    ensures e == NatNumBits(BEWordSeqToInt_premium(x[..]));
{
    ghost var pv := power2(32);
    lemma_2toX();
    ghost var Xs := x[..];

    var t := CountTopZeroWords(x);
    ghost var Xss := x[t..];
    ghost var Xv := BEWordSeqToInt(Xss);
    lemma_LeadingZeros(power2(32), Xss, Xs);
    if (t==x.Length)
    {
        e := 0;
        reveal_BEDigitSeqToInt_private();
        lemma_power2_0_is_1();
        lemma_Power2BoundIsNatNumBits(e, Xv);
        return;
    }
    var b := CountBits(x[t]);
    e := 32*(x.Length - t - 1) + b;

    calc {
        BEWordSeqToInt(x[..]);
        BEWordSeqToInt(Xs);
        BEWordSeqToInt(Xss);
        Xv;
    }

    assert Xss[0] == x[t];
    assert 0<b;
    assert power2(b-1) <= Xss[0];
    assert Xss[0] < power2(b);

    calc {
        power2(e-1);
        power2(b-1 + 32*(|Xss|-1));
            { lemma_power2_adds(b-1, 32*(|Xss|-1)); }
        power2(b-1) * power2(32*(|Xss|-1));
            { lemma_power2_unfolding(32, |Xss|-1);
              lemma_mul_is_mul_boogie(32, |Xss|-1); }
        power2(b-1) * power(pv, |Xss|-1);
        <=  { lemma_power_positive(pv, |Xss|-1);
              lemma_mul_inequality(power2(b-1), Xss[0], power(pv, |Xss|-1)); }
        Xss[0] * power(pv, |Xss|-1);
        <=  { lemma_BEDigitSeqToInt_bound(power2(32), Xss); }
        Xv;
    }
    calc {
        Xv;
            { lemma_BEInterpretation(pv, Xss, |Xss|-1); }
        BEWordSeqToInt(Xss[..1]) * power(pv, |Xss|-1) + BEWordSeqToInt(Xss[1..]);
            { assert Xss[..1] == [Xss[0]];
                lemma_BEDigitSeqToInt_singleton(pv, Xss[0]); }
        Xss[0] * power(pv, |Xss|-1) + BEWordSeqToInt(Xss[1..]);
        <=  { lemma_power_positive(pv, |Xss|-1);
              lemma_mul_inequality_forall(); }
        (power2(b)-1) * power(pv, |Xss|-1) + BEWordSeqToInt(Xss[1..]);
        <   { lemma_BEDigitSeqToInt_bound(power2(32), Xss[1..]); }
        (power2(b)-1) * power(pv, |Xss|-1) + power(pv, |Xss|-1);
            { lemma_mul_basics_forall(); }
        (power2(b)-1) * power(pv, |Xss|-1) + mul(1, power(pv, |Xss|-1));
            { lemma_mul_is_distributive_forall(); }
        power2(b) * power(pv, |Xss|-1);
            { lemma_power2_unfolding(32, |Xss|-1);
              lemma_mul_is_mul_boogie(32, |Xss|-1); }
        power2(b) * power2(32*(|Xss|-1));
            { lemma_power2_adds(b, 32*(|Xss|-1)); }
        power2(b+32*(|Xss|-1));
        power2(e);
    }

    lemma_Power2BoundIsNatNumBits(e, Xv);
}

method FatPower2(exp:nat) returns (S:array<int>)
    requires Word32(exp);
    ensures WellformedFatNat(S);
    ensures J(S) == power2(exp);
{
    lemma_2toX();
    var one := MakeBELiteralArray(1); 
    S := BitShiftLeft_Array(one, exp);
    lemma_mul_basics_forall();
}
