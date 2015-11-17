include "integer_sequences.s.dfy"
include "../Math/div.i.dfy"
include "../Math/power.i.dfy"
include "../Math/power2.i.dfy"
include "seqs_simple.i.dfy"
include "seqs_and_ints.i.dfy"
include "repeat_digit.i.dfy"
include "../../Drivers/CPU/assembly.i.dfy"
include "arrays.i.dfy"

//-////////////////////////////////////////////////////////////////////////////
//- This file is focused on methods and lemmas that relate sequences of
//- different digit place values, eg Bit and Byte sequences.
//- It builds on seqs_and_ints, which establishes more fundamental lemmas
//- about the meanings of digit sequences.

static lemma lemma_power2_8_and_32()
    ensures power2(8)*power2(8)*power2(8)*power2(8) == power2(32);
{
    lemma_mul_is_associative_forall();
    lemma_power2_adds(8,8);
    lemma_power2_adds(16,16);
}

//-////////////////////////////////////////////////////////////////////////////

static lemma lemma_BEByteSeqToInt_unpack_four(m:seq<int>, prefix:seq<int>)
    requires IsByteSeq(m);
    requires 4<=|m|;
    requires IsByteSeq(prefix);
    requires prefix + m[|m|-4..] == m;
    ensures BEByteSeqToInt(m) == BEByteSeqToInt(prefix)*power2(32)
        + (((m[|m|-4])*power2(8) + m[|m|-3])*power2(8) + m[|m|-2])*power2(8) + m[|m|-1];
{
    reveal_BEDigitSeqToInt_private();
    lemma_mul_basics_forall();
    assert m[0..|m|-4] == prefix;
    calc {
        BEByteSeqToInt(m);
        BEDigitSeqToInt(power2(8), m);
        BEDigitSeqToInt_private(power2(8), m);
        BEDigitSeqToInt_private(power2(8), m);
        BEDigitSeqToInt_private(power2(8), m[0..|m|-1])*power2(8) + m[|m|-1];
        (BEDigitSeqToInt_private(power2(8), m[0..|m|-1][0..|m[0..|m|-1]|-1])*power2(8) + m[0..|m|-1][|m[0..|m|-1]|-1])*power2(8) + m[|m|-1];
            { lemma_sequence_reduction(m, |m|-1); }
        (BEDigitSeqToInt_private(power2(8), m[0..|m|-2])*power2(8) + m[|m|-2])*power2(8) + m[|m|-1];
        ((BEDigitSeqToInt_private(power2(8), m[0..|m|-2][0..|m[0..|m|-2]|-1])*power2(8) + m[0..|m|-2][|m[0..|m|-2]|-1])*power2(8) + m[|m|-2])*power2(8) + m[|m|-1];
            { lemma_sequence_reduction(m, |m|-2); }
        ((BEDigitSeqToInt_private(power2(8), m[0..|m|-3])*power2(8) + m[|m|-3])*power2(8) + m[|m|-2])*power2(8) + m[|m|-1];
        (((BEDigitSeqToInt_private(power2(8), m[0..|m|-3][0..|m[0..|m|-3]|-1])*power2(8) + m[0..|m|-3][|m[0..|m|-3]|-1])*power2(8) + m[|m|-3])*power2(8) + m[|m|-2])*power2(8) + m[|m|-1];
            { lemma_sequence_reduction(m, |m|-3); }
        (((BEDigitSeqToInt_private(power2(8), m[0..|m|-4])*power2(8) + m[|m|-4])*power2(8) + m[|m|-3])*power2(8) + m[|m|-2])*power2(8) + m[|m|-1];
            {
                lemma_mul_is_distributive_forall();
                lemma_mul_is_commutative_forall();
                lemma_mul_is_associative_forall();
            }
        BEDigitSeqToInt_private(power2(8), prefix)*(power2(8)*power2(8)*power2(8)*power2(8)) + (((m[|m|-4])*power2(8) + m[|m|-3])*power2(8) + m[|m|-2])*power2(8) + m[|m|-1];
        BEByteSeqToInt(prefix)*(power2(8)*power2(8)*power2(8)*power2(8)) + (((m[|m|-4])*power2(8) + m[|m|-3])*power2(8) + m[|m|-2])*power2(8) + m[|m|-1];
            { lemma_power2_8_and_32(); }
        BEByteSeqToInt(prefix)*power2(32) + (((m[|m|-4])*power2(8) + m[|m|-3])*power2(8) + m[|m|-2])*power2(8) + m[|m|-1];
    }
}

static lemma lemma_BEByteSeqToInt_strip_four(m:seq<int>, prefix:seq<int>, suffix:seq<int>)
    requires IsByteSeq(m);
    requires IsByteSeq(prefix);
    requires IsByteSeq(suffix);
    requires 4<=|m|;
    requires prefix == m[0..|m|-4];
    requires suffix == m[|m|-4..];
    ensures BEByteSeqToInt(m) == BEByteSeqToInt(prefix) * power2(32) + BEByteSeqToInt(suffix);
    ensures 0 <= BEByteSeqToInt(suffix) < power2(32);
{
    reveal_BEDigitSeqToInt_private();
    lemma_mul_basics_forall();
    lemma_BEByteSeqToInt_unpack_four(m, prefix);
    calc {
        BEByteSeqToInt(suffix);
        BEDigitSeqToInt_private(power2(8), suffix);
        BEDigitSeqToInt_private(power2(8), suffix[0..|suffix|-1])*power2(8) + suffix[|suffix|-1];
        (BEDigitSeqToInt_private(power2(8), suffix[0..|suffix|-1][0..|suffix[0..|suffix|-1]|-1])*power2(8) + suffix[0..|suffix|-1][|suffix[0..|suffix|-1]|-1])*power2(8) + suffix[|suffix|-1];
            { lemma_sequence_reduction(suffix, |suffix|-1); }
        (BEDigitSeqToInt_private(power2(8), suffix[0..|suffix|-2])*power2(8) + suffix[|suffix|-2])*power2(8) + suffix[|suffix|-1];
        ((BEDigitSeqToInt_private(power2(8), suffix[0..|suffix|-2][0..|suffix[0..|suffix|-2]|-1])*power2(8) + suffix[0..|suffix|-2][|suffix[0..|suffix|-2]|-1])*power2(8) + suffix[|suffix|-2])*power2(8) + suffix[|suffix|-1];
            { lemma_sequence_reduction(suffix, |suffix|-2); }
        ((BEDigitSeqToInt_private(power2(8), suffix[0..|suffix|-3])*power2(8) + suffix[|suffix|-3])*power2(8) + suffix[|suffix|-2])*power2(8) + suffix[|suffix|-1];
        (((BEDigitSeqToInt_private(power2(8), suffix[0..|suffix|-3][0..|suffix[0..|suffix|-3]|-1])*power2(8) + suffix[0..|suffix|-3][|suffix[0..|suffix|-3]|-1])*power2(8) + suffix[|suffix|-3])*power2(8) + suffix[|suffix|-2])*power2(8) + suffix[|suffix|-1];
            { lemma_sequence_reduction(suffix, |suffix|-3); }
        (((BEDigitSeqToInt_private(power2(8), suffix[0..|suffix|-4])*power2(8) + suffix[|suffix|-4])*power2(8) + suffix[|suffix|-3])*power2(8) + suffix[|suffix|-2])*power2(8) + suffix[|suffix|-1];
        (((BEDigitSeqToInt_private(power2(8), [])*power2(8) + suffix[0])*power2(8) + suffix[1])*power2(8) + suffix[2])*power2(8) + suffix[3];
        ((suffix[0]*power2(8) + suffix[1])*power2(8) + suffix[2])*power2(8) + suffix[3];
        (((m[|m|-4])*power2(8) + m[|m|-3])*power2(8) + m[|m|-2])*power2(8) + m[|m|-1];
    }

    lemma_mul_nonnegative_forall();
    assert 0 <= BEByteSeqToInt(suffix);
    calc {
        (m[|m|-4])*power2(8);
        <= { lemma_mul_inequality(m[|m|-4], power2(8)-1, power2(8)); }
        (power2(8)-1)*power2(8);
            { lemma_mul_is_distributive_forall(); }
        power2(8)*power2(8) - mul(1,power2(8));
        power2(8)*power2(8) - power2(8);
    }
    calc {
        ((m[|m|-4])*power2(8) + m[|m|-3])*power2(8);
        <= { lemma_mul_inequality(((m[|m|-4])*power2(8) + m[|m|-3]), (power2(8)*power2(8) - power2(8) + m[|m|-3]), power2(8)); }
        (power2(8)*power2(8) - power2(8) + m[|m|-3])*power2(8);
        <= { lemma_mul_inequality((power2(8)*power2(8) - power2(8) + m[|m|-3]), (power2(8)*power2(8)-1), power2(8)); }
        (power2(8)*power2(8)-1)*power2(8);
            { lemma_mul_is_distributive_forall(); }
        (power2(8)*power2(8))*power2(8) - mul(1,power2(8));
        (power2(8)*power2(8))*power2(8) - power2(8);
    }
    calc {
        (((m[|m|-4])*power2(8) + m[|m|-3])*power2(8) + m[|m|-2])*power2(8);
        <= { lemma_mul_inequality((((m[|m|-4])*power2(8) + m[|m|-3])*power2(8) + m[|m|-2]), ((power2(8)*power2(8))*power2(8) - power2(8) + m[|m|-2]), power2(8)); }
        ((power2(8)*power2(8))*power2(8) - power2(8) + m[|m|-2])*power2(8);
        <= { lemma_mul_inequality(((power2(8)*power2(8))*power2(8) - power2(8) + m[|m|-2]), ((power2(8)*power2(8))*power2(8) - 1), power2(8)); }
        ((power2(8)*power2(8))*power2(8) - 1)*power2(8);
            { lemma_mul_is_distributive_forall(); }
        ((power2(8)*power2(8))*power2(8))*power2(8) - mul(1,power2(8));
        ((power2(8)*power2(8))*power2(8))*power2(8) - power2(8);
    }
    calc {
        BEByteSeqToInt(suffix);
        (((m[|m|-4])*power2(8) + m[|m|-3])*power2(8) + m[|m|-2])*power2(8) + m[|m|-1];
        <=
        ((power2(8)*power2(8))*power2(8))*power2(8) - 1;
            { lemma_power2_adds(8,8); }
        (power2(16)*power2(8))*power2(8) - 1;
            { lemma_power2_adds(16,8); }
        power2(24)*power2(8) - 1;
            { lemma_power2_adds(24,8); }
        power2(32) - 1;
    }
}

static lemma lemma_BEIntToDigitSeq_produces_DigitSeq(pv:int, mp:int, x:int)
    requires 1<pv;
    requires 0<=x;
    ensures IsDigitSeq(pv, BEIntToDigitSeq(pv, mp, x));
    decreases if mp > x then mp else x;
{
    reveal_BEIntToDigitSeq_private();

    if (1<pv && (0<x || 0<mp))
    {
        lemma_div_pos_is_pos(x,pv);
        if (x>0)    //- prove decreases
        {
            lemma_div_decreases(x,pv);
        }
        else
        {
            lemma_small_div();
        }

        forall (i | 0<=i<|BEIntToDigitSeq(pv, mp, x)|)
            ensures 0 <= BEIntToDigitSeq(pv, mp, x)[i] < pv;
        {
            if (i<|BEIntToDigitSeq(pv, mp, x)|-1)
            {
                lemma_BEIntToDigitSeq_produces_DigitSeq(pv, mp-1, x/pv);
            }
            else
            {
                lemma_mod_properties();
            }
        }
        assert IsDigitSeq(pv, BEIntToDigitSeq(pv, mp, x));
//-        BEIntToDigitSeq_private(pv, mp-1, x/pv) + [ x % pv ]
    }
    else
    {
        assert IsDigitSeq(pv, BEIntToDigitSeq(pv, mp, x));
    }
}

static lemma lemma_BEIntToDigitSeq_private_properties(pv:int, mp:int, x:int)
    requires 1<pv;
    requires 0<=mp;
    requires 0<=x;
    requires x < power(pv, mp);
    decreases mp;
    ensures |BEIntToDigitSeq_private(pv,mp,x)| == mp;
    ensures forall i :: 0<=i<mp ==> 0 <= BEIntToDigitSeq_private(pv,mp,x)[i] < pv;
    ensures IsDigitSeq(pv, BEIntToDigitSeq_private(pv,mp,x));
{
    reveal_BEIntToDigitSeq_private();

    if (mp==0)
    {
        lemma_power_0(pv);
        assert x == 0;
        assert BEIntToDigitSeq_private(pv,mp,x) == [];
    }
    else
    {
        assert pv!=0;
        assert mp>0;
        calc {
            BEIntToDigitSeq_private(pv,mp,x);
            BEIntToDigitSeq_private(pv, mp-1, x/pv) + [ x % pv ];
        }
        if (x/pv >= power(pv,mp-1))
        {
            calc {
                x;
                >=    { lemma_remainder_lower(x, pv); }
                (x/pv)*pv;
                >=    { lemma_mul_inequality(power(pv,mp-1), x/pv, pv); }
                power(pv,mp-1)*pv;
                    { reveal_power(); lemma_mul_is_commutative_forall(); }
                power(pv,mp);
            }
            assert false;
        }
        lemma_div_pos_is_pos(x,pv);
        lemma_BEIntToDigitSeq_private_properties(pv, mp-1, x/pv);
        assert |BEIntToDigitSeq_private(pv,mp,x)| == mp;
        forall (i | 0<=i<mp)
            ensures 0 <= BEIntToDigitSeq_private(pv,mp,x)[i] < pv;
        {
            var elt := BEIntToDigitSeq_private(pv,mp,x)[i];
            if (i<mp-1)
            {
                calc {
                    elt;
                    (BEIntToDigitSeq_private(pv, mp-1, x/pv) + [ x % pv ])[i];
                    BEIntToDigitSeq_private(pv, mp-1, x/pv)[i];
                }
                assert 0 <= elt < pv;
            }
            else
            {
                assert elt == x % pv;
                lemma_mod_properties();
                assert 0 <= elt < pv;
            }
        }
    }
}

static lemma lemma_SeqTransform_structure(inseq:seq<int>, outbits:nat, scale:nat, inbits:nat)
    requires IsDigitSeq(power2(inbits), inseq);
    requires 0<scale;
    requires 0<outbits;
    requires outbits*scale == inbits;
    decreases |inseq|;
    ensures IsDigitSeq(power2(outbits),
        BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq)));
    ensures
        |BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq))| == |inseq|*scale;
{
    var x := BEDigitSeqToInt(power2(inbits), inseq);
    var mp := |inseq|*scale;
    lemma_mul_nonnegative(|inseq|,scale);
    lemma_mul_nonnegative(scale,|inseq|);
    lemma_BEDigitSeqToInt_bound(power2(inbits), inseq);
    lemma_power_positive(2, outbits);
    calc {
        x;
        < power(power2(inbits), |inseq|);
        power(power2(outbits*scale), |inseq|);
            { lemma_power2_is_power_2(outbits*scale); }
        power(power(2, outbits*scale), |inseq|);
            { lemma_power_multiplies(2, outbits, scale); }
        power(power(power(2, outbits), scale), |inseq|);
            { lemma_power_multiplies(power(2, outbits), scale, |inseq|); }
        power(power(2, outbits), scale*|inseq|);
            { lemma_power2_is_power_2(outbits); }
        power(power2(outbits), scale*|inseq|);
            { lemma_mul_is_commutative_forall(); }
        power(power2(outbits), |inseq|*scale);
    }
    lemma_power2_nonzero_bigger_than_one();
    assert 1<power2(outbits);
    lemma_BEIntToDigitSeq_private_properties(power2(outbits), mp, x);
}

static lemma lemma_adding_one_outbits(outbits:nat, delta:nat)
    requires 0<outbits;
    requires 1<delta;
    ensures 0<outbits*delta;
    ensures 0<outbits*(delta-1);
    ensures power2(outbits)*power2(outbits*(delta-1)) == power2(outbits*delta);
    ensures power2(outbits*(delta-1))*power2(outbits)== power2(outbits*delta);
{
    lemma_mul_strictly_positive_forall();
    assert 0<outbits*delta;
    assert 0<outbits*(delta-1);

    calc {
        outbits*delta-outbits;
            { lemma_mul_basics_forall(); }
        outbits*delta-mul(outbits,1);
            { lemma_mul_is_distributive_forall(); }
        outbits*(delta-1);
    }
    lemma_power2_adds(outbits*delta-outbits, outbits);
    lemma_mul_is_commutative_forall();
}

static lemma lemma_horrific_ways_to_truncate(outbits:nat, delta:nat, v:int)
    requires 0<outbits;
    requires 1<delta;
    requires 0<=v;
    ensures 0<outbits*delta;
    ensures 0<outbits*(delta-1);
    ensures (v%power2(outbits*delta))/power2(outbits) == (v/power2(outbits))%power2(outbits*(delta-1));
{
    lemma_adding_one_outbits(outbits, delta);    //- introduced broadly to get 0< ensures
    var left := (v%power2(outbits*delta))/power2(outbits);
    var right := (v/power2(outbits))%power2(outbits*(delta-1));

    var top_stuff := power2(outbits*(delta-1))*(v/(power2(outbits*delta)));
    calc {
        v/power2(outbits);
            { lemma_fundamental_div_mod(v/power2(outbits), power2(outbits*(delta-1))); }
        power2(outbits*(delta-1))*((v/power2(outbits)) / power2(outbits*(delta-1))) + right;
            { lemma_div_denominator(v, power2(outbits), power2(outbits*(delta-1))); }
        power2(outbits*(delta-1))*(v/(power2(outbits)*power2(outbits*(delta-1)))) + right;
        power2(outbits*(delta-1))*(v/(power2(outbits*delta))) + right;
        top_stuff + right;
    }

    var a := power2(outbits*delta)*(v/power2(outbits*delta));
    var b := v%power2(outbits*delta);
    var d := power2(outbits);
    var R := a%d + b%d - ((a+b)%d);
    var k := power2(outbits*(delta-1))*(v/power2(outbits*delta));
    calc {
        a;
        power2(outbits*delta)*(v/power2(outbits*delta));
            //- another application of lemma_adding_one_outbits
        (power2(outbits)*power2(outbits*(delta-1)))*(v/power2(outbits*delta));
            { lemma_mul_is_associative_forall(); }
        power2(outbits)*k;
    }
    calc {
        a%d;
            { lemma_mod_multiples_vanish(k, 0, d); }
        mod(0, d);
            { lemma_small_mod(0,d); }
        0;
    }
    calc {
        (a+b)%d;
            { lemma_mod_multiples_vanish(k, b, d); }
        b%d;
    }
    assert R==0;

    calc ==> {
        true;
            { lemma_fundamental_div_mod(v, power2(outbits*delta)); }
        v == power2(outbits*delta)*(v/power2(outbits*delta)) + v%power2(outbits*delta);
        v/power2(outbits) == (power2(outbits*delta)*(v/power2(outbits*delta)) + v%power2(outbits*delta))/power2(outbits);
        v/d == (a + b)/d;
        {
            calc {
                d*((a+b)/d);
                d*((a+b)/d) - R;
                    { lemma_dividing_sums(a, b, d, R); }
                d*(a/d) + d*(b/d);
                    { lemma_mul_is_distributive_forall(); }
                d*(a/d + b/d);
            }
            lemma_mul_one_to_one_pos(d, (a+b)/d, a/d+b/d);
        }
        v/d == a/d + b/d;
        v/d == a/d + left;
    }
    calc {
        a/d;
        (power2(outbits*delta)*(v/power2(outbits*delta))) / d;
            //- another application of lemma_adding_one_outbits
        ((d*power2(outbits*(delta-1)))*(v/power2(outbits*delta))) / d;
            { lemma_mul_is_associative_forall(); }
        (d*(power2(outbits*(delta-1))*(v/power2(outbits*delta)))) / d;
            { lemma_mul_is_commutative_forall(); }
        ((power2(outbits*(delta-1))*(v/power2(outbits*delta)))*d) / d;
            {
                lemma_div_pos_is_pos(v, power2(outbits*delta));
                lemma_mul_nonnegative_forall();
                assert 0<=power2(outbits*(delta-1))*(v/power2(outbits*delta));
                assert 0<d;
                lemma_div_by_multiple((power2(outbits*(delta-1))*(v/power2(outbits*delta))), d);
            }
        power2(outbits*(delta-1))*(v/power2(outbits*delta));
        top_stuff;
    }
    assert left == right;
}

static lemma lemma_BEIntToDigitSeq_private_chop_proper(outbits:nat, count:nat, delta:nat, v:int)
    //- count is count of output words
    requires 0<outbits;
    requires 0<delta;
    requires delta <= count;
    requires 0<delta+count;
    requires 0<=outbits*count;
    requires 0 <= v < power2(outbits*count);
    decreases count;
    ensures 0 <= outbits*delta;
    ensures BEIntToDigitSeq_private(power2(outbits), count-delta, v/power2(outbits*delta))
            + BEIntToDigitSeq_private(power2(outbits), delta, v%power2(outbits*delta))
            == BEIntToDigitSeq_private(power2(outbits), count, v);
{
    lemma_mul_nonnegative(outbits, delta);
    lemma_mul_nonnegative(outbits, delta-1);
    lemma_power2_increases(0,outbits);
    lemma_power2_0_is_1();
    lemma_power2_nonzero_bigger_than_one();
    assert 1 < power2(outbits);

    assert 0 <= outbits*(delta-1);
    if (delta==1)
    {
        lemma_mul_basics(outbits);
        calc {
            BEIntToDigitSeq_private(power2(outbits), count-delta, v/power2(outbits*delta))
                + BEIntToDigitSeq_private(power2(outbits), delta, v%power2(outbits*delta));
                { lemma_mul_basics_forall(); }
            BEIntToDigitSeq_private(power2(outbits), count-1, v/power2(outbits))
                + BEIntToDigitSeq_private(power2(outbits), 1, v%power2(outbits));
            {
                calc {
                    BEIntToDigitSeq_private(power2(outbits), 1, v%power2(outbits));
                        { reveal_BEIntToDigitSeq_private(); }
                    BEIntToDigitSeq_private(power2(outbits), 1-1, (v%power2(outbits))/power2(outbits)) + [ (v % power2(outbits)) % power2(outbits) ];
                        { lemma_mod_properties(); }
                    BEIntToDigitSeq_private(power2(outbits), 0, (v%power2(outbits))/power2(outbits)) + [ v % power2(outbits) ];
                        {
                            lemma_mod_properties();
                            lemma_small_div();
                            assert 0==(v%power2(outbits))/power2(outbits);
                            reveal_BEIntToDigitSeq_private();
                        }
                    [] + [ v % power2(outbits) ];
                    [ v % power2(outbits) ];
                }
            }
            BEIntToDigitSeq_private(power2(outbits), count-1, v/power2(outbits)) + [ v % power2(outbits) ];
                {
                assert 0<power2(outbits);
                assert 0<count;
                reveal_BEIntToDigitSeq_private(); }
            BEIntToDigitSeq_private(power2(outbits), count, v);
        }
    }
    else
    {
        calc {
            BEIntToDigitSeq_private(power2(outbits), count-delta, v/power2(outbits*delta))
                + BEIntToDigitSeq_private(power2(outbits), delta, v%power2(outbits*delta));

            {
                calc {
                    BEIntToDigitSeq_private(power2(outbits), delta, v%power2(outbits*delta));
                        { reveal_BEIntToDigitSeq_private(); }
                    BEIntToDigitSeq_private(power2(outbits), delta-1, (v%power2(outbits*delta))/power2(outbits))
                        + [ (v%power2(outbits*delta)) % power2(outbits) ];
                        { lemma_horrific_ways_to_truncate(outbits, delta, v); }
                    BEIntToDigitSeq_private(power2(outbits), (delta-1), (v/power2(outbits))%power2(outbits*(delta-1)))
                        + [ (v%power2(outbits*delta)) % power2(outbits) ];
                        {    lemma_adding_one_outbits(outbits, delta); }
                    BEIntToDigitSeq_private(power2(outbits), (delta-1), (v/power2(outbits))%power2(outbits*(delta-1)))
                        + [ v%(power2(outbits)*power2(outbits*(delta-1))) % power2(outbits) ];
                        {
                            lemma_mod_mod(v, power2(outbits), power2(outbits*(delta-1)));
//-                            assert v%(power2(outbits)*power2(outbits*(delta-1))) % power2(outbits)
//-                                == v % power2(outbits);
                        }
                    BEIntToDigitSeq_private(power2(outbits), (delta-1), (v/power2(outbits))%power2(outbits*(delta-1)))
                        + [ v % power2(outbits) ];
                }
            }

            BEIntToDigitSeq_private(power2(outbits), count-delta, v/power2(outbits*delta))
                + BEIntToDigitSeq_private(power2(outbits), (delta-1), (v/power2(outbits))%power2(outbits*(delta-1)))
                + [ v % power2(outbits) ];

            calc {
                BEIntToDigitSeq_private(power2(outbits), count-delta, v/power2(outbits*delta))
                    + BEIntToDigitSeq_private(power2(outbits), (delta-1), (v/power2(outbits))%power2(outbits*(delta-1)));
                {
                    lemma_mul_strictly_positive_forall();
//-                    assert 0<power2(outbits)*power2(outbits*(delta-1));     //- preclude div by zero
                    calc {
                        (v/power2(outbits))/power2(outbits*(delta-1));
                        { lemma_div_denominator(v, power2(outbits), power2(outbits*(delta-1))); }
                        v/(power2(outbits)*power2(outbits*(delta-1)));
                        {    lemma_adding_one_outbits(outbits, delta); }
                        v/power2(outbits*delta);
                    }
                }
                BEIntToDigitSeq_private(power2(outbits), count-delta, (v/power2(outbits))/power2(outbits*(delta-1)))
                    + BEIntToDigitSeq_private(power2(outbits), (delta-1), (v/power2(outbits))%power2(outbits*(delta-1)));
                {
                    lemma_mul_nonnegative(outbits, count-1);
                    assert 0<=outbits*(count-1);
                    lemma_div_pos_is_pos(v, power2(outbits));
                    assert 0 <= v/power2(outbits);
                    if (v/power2(outbits) >= power2(outbits*(count-1)))
                    {
                        calc ==> {
                            v/power2(outbits) >= power2(outbits*(count-1));
                                { lemma_mul_inequality(power2(outbits*(count-1)), v/power2(outbits), power2(outbits)); }
                            (v/power2(outbits))*power2(outbits) >= power2(outbits*(count-1))*power2(outbits);
                                { lemma_power2_adds(outbits*(count-1), outbits); }
                            (v/power2(outbits))*power2(outbits) >= power2(outbits*(count-1)+outbits);
                                { lemma_mul_is_distributive_forall(); }
                            (v/power2(outbits))*power2(outbits) >= power2((outbits*count-mul(outbits,1))+outbits);
                                { lemma_mul_basics_forall(); }
                            (v/power2(outbits))*power2(outbits) >= power2(outbits*count);
                                { lemma_mod_properties(); }
                            (v/power2(outbits))*power2(outbits) + v%power2(outbits) >= power2(outbits*count);
                            {
                                lemma_fundamental_div_mod(v, power2(outbits));
                                lemma_mul_is_commutative_forall();
                            }
                            v >= power2(outbits*count);
                        }
                    }
                    assert v/power2(outbits) < power2(outbits*(count-1));
                    lemma_BEIntToDigitSeq_private_chop_proper(outbits, count-1, delta-1, v/power2(outbits));
                }
                BEIntToDigitSeq_private(power2(outbits), count-1, v/power2(outbits));
            }

            BEIntToDigitSeq_private(power2(outbits), count-1, v/power2(outbits)) + [ v % power2(outbits) ];
                { reveal_BEIntToDigitSeq_private(); }
            BEIntToDigitSeq_private(power2(outbits), count, v);
        }
    }
}

static lemma lemma_BEIntToDigitSeq_private_chop(outbits:nat, count:nat, delta:nat, v:int)
    requires 0<outbits;
    requires 0<=delta;
    requires delta <= count;
    requires 0<=outbits*count;
    requires 0 <= v < power2(outbits*count);
    decreases count;
    ensures 0 <= outbits*delta;
    ensures BEIntToDigitSeq_private(power2(outbits), count-delta, v/power2(outbits*delta))
            + BEIntToDigitSeq_private(power2(outbits), delta, v%power2(outbits*delta))
            == BEIntToDigitSeq_private(power2(outbits), count, v);
{
    if (delta==0)
    {
        var L1 := 1;
        lemma_power2_0_is_1();
        lemma_mul_basics_forall();
        lemma_div_basics(v);
        lemma_mod_properties();
        calc {
            BEIntToDigitSeq_private(power2(outbits), count-delta, v/power2(outbits*delta))
                + BEIntToDigitSeq_private(power2(outbits), delta, v%power2(outbits*delta));
            BEIntToDigitSeq_private(power2(outbits), count, v/L1)
                + BEIntToDigitSeq_private(power2(outbits), 0, v%L1);
            BEIntToDigitSeq_private(power2(outbits), count, v)
                + BEIntToDigitSeq_private(power2(outbits), 0, 0);
                { reveal_BEIntToDigitSeq_private(); }
            BEIntToDigitSeq_private(power2(outbits), count, v) + [];
            BEIntToDigitSeq_private(power2(outbits), count, v);
        }
    }
    else
    {
        lemma_BEIntToDigitSeq_private_chop_proper(outbits, count, delta, v);
    }
}


static lemma lemma_SeqTransformSnip(inseq:seq<int>, headseq:seq<int>, tailseq:seq<int>, outbits:nat, scale:nat, inbits:nat)
    requires IsDigitSeq(power2(inbits), inseq);
    requires IsDigitSeq(power2(inbits), headseq);
    requires IsDigitSeq(power2(inbits), tailseq);
    requires inseq == headseq + tailseq;
    requires |tailseq| == 1;
    requires 0<outbits;
    requires 0<scale;
    requires outbits*scale == inbits;
    decreases |inseq|;
    ensures
        BEIntToDigitSeq(power2(outbits), |headseq|*scale, BEDigitSeqToInt(power2(inbits), headseq))
            + BEIntToDigitSeq(power2(outbits), |tailseq|*scale, BEDigitSeqToInt(power2(inbits), tailseq))
        == BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq));
{
    var bigv := BEDigitSeqToInt_private(power2(inbits), inseq[0..|inseq|-1])*power2(inbits) + inseq[|inseq|-1];
    reveal_BEDigitSeqToInt_private();
    lemma_fundamental_div_mod_converse(bigv, power2(inbits), BEDigitSeqToInt_private(power2(inbits), inseq[0..|inseq|-1]), inseq[|inseq|-1]);
    assert bigv/power2(inbits) == BEDigitSeqToInt_private(power2(inbits), inseq[0..|inseq|-1]);
    calc {
        BEDigitSeqToInt_private(power2(inbits), tailseq);
        BEDigitSeqToInt_private(power2(inbits), tailseq[0..|tailseq|-1])*power2(inbits) + tailseq[|tailseq|-1];
        BEDigitSeqToInt_private(power2(inbits), [])*power2(inbits) + tailseq[|tailseq|-1];
        mul(0,power2(inbits)) + tailseq[|tailseq|-1];
            { lemma_mul_basics_forall(); }
        tailseq[|tailseq|-1];
        inseq[|inseq|-1];
        bigv%power2(inbits);
    }

    lemma_mul_strictly_positive_forall();
    assert 0 < |inseq|*scale;
    calc ==> {
        true;
            { lemma_BEDigitSeqToInt_bound(power2(inbits), inseq[0..|inseq|-1]); }
        0 <= BEDigitSeqToInt_private(power2(inbits), inseq[0..|inseq|-1]) < power(power2(inbits), |inseq[0..|inseq|-1]|);
        0 <= BEDigitSeqToInt_private(power2(inbits), inseq[0..|inseq|-1]) < power(power2(inbits), |inseq|-1);
        0 <= BEDigitSeqToInt_private(power2(inbits), inseq[0..|inseq|-1]) <= power(power2(inbits), |inseq|-1)-1;
            { lemma_mul_inequality_forall(); }
        mul(0,power2(inbits)) <= mul(BEDigitSeqToInt_private(power2(inbits), inseq[0..|inseq|-1]),power2(inbits))
            <= mul(power(power2(inbits), |inseq|-1)-1, power2(inbits));
            { lemma_mul_basics_forall(); }
        0 <= mul(BEDigitSeqToInt_private(power2(inbits), inseq[0..|inseq|-1]),power2(inbits))
            <= mul(power(power2(inbits), |inseq|-1)-1, power2(inbits));
        0 <= mul(BEDigitSeqToInt_private(power2(inbits), inseq[0..|inseq|-1]),power2(inbits))
            <= mul(power(power2(inbits), |inseq|-1) - 1, power2(inbits));
            { lemma_mul_is_distributive_forall(); }
        0 <= mul(BEDigitSeqToInt_private(power2(inbits), inseq[0..|inseq|-1]),power2(inbits))
            <= mul(power(power2(inbits), |inseq|-1), power2(inbits))-mul(1,power2(inbits));
            { lemma_mul_basics_forall(); }
        0 <= mul(BEDigitSeqToInt_private(power2(inbits), inseq[0..|inseq|-1]),power2(inbits))
            <= mul(power(power2(inbits), |inseq|-1), power2(inbits))-power2(inbits);
        0 <= mul(BEDigitSeqToInt_private(power2(inbits), inseq[0..|inseq|-1]),power2(inbits)) + inseq[|inseq|-1]
            <= mul(power(power2(inbits), |inseq|-1), power2(inbits))-power2(inbits) + inseq[|inseq|-1];
        0 <= bigv < mul(power(power2(inbits), |inseq|-1), power2(inbits))-power2(inbits) + power2(inbits);
        0 <= bigv < mul(power(power2(inbits), |inseq|-1), power2(inbits));
            { lemma_power_1(power2(inbits)); }
        0 <= bigv < mul(power(power2(inbits), |inseq|-1), power(power2(inbits), 1));
            { lemma_power_adds(power2(inbits), |inseq|-1, 1); }
        0 <= bigv < power(power2(inbits), |inseq|-1+1);
            { lemma_power2_is_power_2(inbits); }
        0 <= bigv < power(power(2, inbits), |inseq|-1+1);
        0 <= bigv < power(power(2, inbits), |inseq|);
            { lemma_power_multiplies(2, inbits, |inseq|); }
        0 <= bigv < power(2, inbits*|inseq|);
            { lemma_power2_is_power_2(inbits*|inseq|); }
        0 <= bigv < power2(inbits*|inseq|);
            { lemma_mul_is_commutative_forall(); }
        0 <= bigv < power2(|inseq|*inbits);
        0 <= bigv < power2(|inseq|*(outbits*scale));
            { lemma_mul_is_commutative_forall(); lemma_mul_is_associative_forall(); }
        0 <= bigv < power2(outbits*(|inseq|*scale));
    }

    calc {
        BEIntToDigitSeq(power2(outbits), |headseq|*scale, BEDigitSeqToInt(power2(inbits), headseq))
            + BEIntToDigitSeq(power2(outbits), |tailseq|*scale, BEDigitSeqToInt(power2(inbits), tailseq));
        BEIntToDigitSeq_private(power2(outbits), |headseq|*scale, BEDigitSeqToInt_private(power2(inbits), headseq))
            + BEIntToDigitSeq_private(power2(outbits), |tailseq|*scale, BEDigitSeqToInt_private(power2(inbits), tailseq));
            {
                assert |headseq| == |inseq|-1;
                assert |tailseq|==1;
                lemma_mul_basics(scale);
                assert |tailseq|*scale == scale;
            }
        BEIntToDigitSeq_private(power2(outbits), (|inseq|-1)*scale, BEDigitSeqToInt_private(power2(inbits), headseq))
            + BEIntToDigitSeq_private(power2(outbits), scale, BEDigitSeqToInt_private(power2(inbits), tailseq));
            {
                assert headseq == inseq[0..|inseq|-1];
            }
        BEIntToDigitSeq_private(power2(outbits), (|inseq|-1)*scale, bigv/power2(inbits))
            + BEIntToDigitSeq_private(power2(outbits), scale, bigv % power2(inbits));
        BEIntToDigitSeq_private(power2(outbits), (|inseq|-1)*scale, bigv/power2(inbits))
            + BEIntToDigitSeq_private(power2(outbits), scale, bigv % power2(inbits));
        BEIntToDigitSeq_private(power2(outbits), (|inseq|-1)*scale, bigv/(power2(outbits*scale)))
            + BEIntToDigitSeq_private(power2(outbits), scale, bigv % (power2(outbits*scale)));
        {
            calc {
                (|inseq|-1)*scale;
                    { lemma_mul_is_distributive_forall(); }
                |inseq|*scale-mul(1,scale);
                    { lemma_mul_basics_forall(); }
                |inseq|*scale-scale;
            }
        }
        BEIntToDigitSeq_private(power2(outbits), |inseq|*scale-scale, bigv/power2(outbits*scale))
            + BEIntToDigitSeq_private(power2(outbits), scale, bigv%power2(outbits*scale));
            {
                lemma_mul_nonnegative(|inseq|,scale);
                assert bigv < power2(outbits*(|inseq|*scale));
                lemma_mul_increases(|inseq|,scale);
                assert scale <= |inseq|*scale;
                lemma_BEIntToDigitSeq_private_chop_proper(outbits, |inseq|*scale, scale, bigv);
            }
        BEIntToDigitSeq_private(power2(outbits), |inseq|*scale, bigv);
        BEIntToDigitSeq_private(power2(outbits), |inseq|*scale,
            BEDigitSeqToInt_private(power2(inbits), inseq[0..|inseq|-1])*power2(inbits) + inseq[|inseq|-1]);
            //- expand defn BEIntToDigitSeq
        BEIntToDigitSeq(power2(outbits), |inseq|*scale,
            BEDigitSeqToInt_private(power2(inbits), inseq[0..|inseq|-1])*power2(inbits) + inseq[|inseq|-1]);
            { reveal_BEDigitSeqToInt_private(); }
        BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq));
    }
}

static lemma lemma_SeqTransformChop(inseq:seq<int>, headseq:seq<int>, tailseq:seq<int>, outbits:nat, scale:nat, inbits:nat)
    requires IsDigitSeq(power2(inbits), inseq);
    requires IsDigitSeq(power2(inbits), headseq);
    requires IsDigitSeq(power2(inbits), tailseq);
    requires inseq == headseq + tailseq;
    requires 0<outbits;
    requires 0<scale;
    requires outbits*scale == inbits;
    decreases |tailseq|;
    ensures
        BEIntToDigitSeq(power2(outbits), |headseq|*scale, BEDigitSeqToInt(power2(inbits), headseq))
            + BEIntToDigitSeq(power2(outbits), |tailseq|*scale, BEDigitSeqToInt(power2(inbits), tailseq))
        == BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq));
{
    lemma_power2_nonzero_bigger_than_one();
    if (|tailseq|==0)
    {
        lemma_mul_basics_forall();
        calc {
            BEIntToDigitSeq(power2(outbits), |headseq|*scale, BEDigitSeqToInt(power2(inbits), headseq))
                + BEIntToDigitSeq(power2(outbits), |tailseq|*scale, BEDigitSeqToInt(power2(inbits), tailseq));
                {
                    var x := BEDigitSeqToInt(power2(inbits), tailseq);
                    lemma_BEDigitSeqToInt_bound(power2(inbits), tailseq);
                    lemma_power_0(power2(inbits));
                    assert x == 0;

                    var mp := |tailseq|*scale;
                    lemma_mul_basics_forall();
                    lemma_power2_positive();
                    lemma_power_positive(power2(outbits), mp);
                    lemma_BEIntToDigitSeq_private_properties(power2(outbits), mp, x);
                    assert |BEIntToDigitSeq(power2(outbits), mp, x)| == 0;
                    assert |BEIntToDigitSeq(power2(outbits), |tailseq|*scale, BEDigitSeqToInt(power2(inbits), tailseq))| == 0;
                }
            BEIntToDigitSeq(power2(outbits), |headseq|*scale, BEDigitSeqToInt(power2(inbits), headseq));
                { assert headseq == inseq; }
            BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq));
        }
    }
    else if (|tailseq|==1)
    {
        lemma_SeqTransformSnip(inseq, headseq, tailseq, outbits, scale, inbits);
    }
    else
    {
        var midl := inseq[|headseq|..|headseq|+1];
        var subhead := inseq[..|headseq|+1];
        var subtail := inseq[|headseq|+1..];
        assert |subtail| == |tailseq| - 1;
        calc  {
            //- (A0 A1 A2) + (B0 C0 C1)
            BEIntToDigitSeq(power2(outbits), |headseq|*scale, BEDigitSeqToInt(power2(inbits), headseq))
                + BEIntToDigitSeq(power2(outbits), |tailseq|*scale, BEDigitSeqToInt(power2(inbits), tailseq));
                { lemma_SeqTransformChop(tailseq, midl, subtail, outbits, scale, inbits); }
            //- (A0 A1 A2) + B0 + (C0 C1)
            BEIntToDigitSeq(power2(outbits), |headseq|*scale, BEDigitSeqToInt(power2(inbits), headseq))
                + BEIntToDigitSeq(power2(outbits), |midl|*scale, BEDigitSeqToInt(power2(inbits), midl))
                + BEIntToDigitSeq(power2(outbits), |subtail|*scale, BEDigitSeqToInt(power2(inbits), subtail));
                { lemma_SeqTransformChop(subhead, headseq, midl, outbits, scale, inbits); }
            //- (A0 A1 A2 B0) + (C0 C1)
            BEIntToDigitSeq(power2(outbits), |subhead|*scale, BEDigitSeqToInt(power2(inbits), subhead))
                + BEIntToDigitSeq(power2(outbits), |subtail|*scale, BEDigitSeqToInt(power2(inbits), subtail));
                { lemma_SeqTransformChop(inseq, subhead, subtail, outbits, scale, inbits); }
            //- A0 A1 A2 B0 C0 C1
            BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq));
        }
    }
}

//-static lemma lemma_obvious_statement_about_sequence_concatenation(a:seq<int>, b:seq<int>, c:seq<int>)
//-    requires a == b + c;
//-    ensures a[|b|..] == c;
//-{
//-}

static lemma lemma_SeqTransformChopOne(inseq:seq<int>, head:int, tailseq:seq<int>, outbits:nat, scale:nat, inbits:nat)
    requires IsDigitSeq(power2(inbits), inseq);
    requires 0 <= head < power2(inbits);
    requires IsDigitSeq(power2(inbits), tailseq);
    requires inseq == [head] + tailseq;
    requires 0<outbits;
    requires 0<scale;
    requires outbits*scale == inbits;
    decreases |tailseq|;
    ensures
        BEIntToDigitSeq(power2(outbits), scale, head)
        + BEIntToDigitSeq(power2(outbits), |tailseq|*scale, BEDigitSeqToInt(power2(inbits), tailseq))
        == BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq));
{
    calc {
        BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq));
        { lemma_SeqTransformChop(inseq, [head], tailseq, outbits, scale, inbits); }
        BEIntToDigitSeq(power2(outbits), |[head]|*scale, BEDigitSeqToInt(power2(inbits), [head]))
            + BEIntToDigitSeq(power2(outbits), |tailseq|*scale, BEDigitSeqToInt(power2(inbits), tailseq));
        { assert |[head]| == 1; lemma_mul_is_mul_boogie(1, scale); }
        BEIntToDigitSeq(power2(outbits), scale, BEDigitSeqToInt(power2(inbits), [head]))
            + BEIntToDigitSeq(power2(outbits), |tailseq|*scale, BEDigitSeqToInt(power2(inbits), tailseq));
        calc {
            BEDigitSeqToInt(power2(inbits), [head]);
            { reveal_BEDigitSeqToInt_private(); }
            BEDigitSeqToInt(power2(inbits), [head][..0])*power2(inbits) + [head][|[head]|-1];
            { assert |[head][..0]| == 0; }
            BEDigitSeqToInt(power2(inbits), [])*power2(inbits) + [head][|[head]|-1];
            BEDigitSeqToInt(power2(inbits), [])*power2(inbits) + [head][0];
            BEDigitSeqToInt(power2(inbits), [])*power2(inbits) + head;
            { reveal_BEDigitSeqToInt_private(); lemma_mul_is_mul_boogie(0, power2(inbits)); }
            0*power2(inbits) + head;
            head;
        }
        BEIntToDigitSeq(power2(outbits), scale, head)
            + BEIntToDigitSeq(power2(outbits), |tailseq|*scale, BEDigitSeqToInt(power2(inbits), tailseq));
    }
}

static lemma lemma_WordSeqToBitSeqChop(inseq:seq<int>, headseq:seq<int>, tailseq:seq<int>)
    requires IsWordSeq(inseq);
    requires IsWordSeq(headseq);
    requires IsWordSeq(tailseq);
    requires inseq == headseq + tailseq;
    ensures BEWordSeqToBitSeq(headseq) + BEWordSeqToBitSeq(tailseq) == BEWordSeqToBitSeq(inseq);
{
    lemma_mul_is_mul_boogie(1, 32);
    lemma_mul_is_mul_boogie(|inseq|, 32);
    lemma_mul_is_mul_boogie(|headseq|, 32);
    lemma_mul_is_mul_boogie(|tailseq|, 32);
    lemma_SeqTransformChop(inseq, headseq, tailseq, 1, 32, 32);
}

static lemma lemma_WordSeqToBitSeqChopOne(inseq:seq<int>, head:int, tailseq:seq<int>)
    requires IsWordSeq(inseq);
    requires Word32(head);
    requires IsWordSeq(tailseq);
    requires inseq == [head] + tailseq;
    ensures BEWordToBitSeq(head) + BEWordSeqToBitSeq(tailseq) == BEWordSeqToBitSeq(inseq);
{
    lemma_mul_is_mul_boogie(1, 32);
    lemma_mul_is_mul_boogie(|inseq|, 32);
    lemma_mul_is_mul_boogie(|tailseq|, 32);
    lemma_SeqTransformChopOne(inseq, head, tailseq, 1, 32, 32);
}

static lemma lemma_WordSeqToBitSeqChopHead(inseq:seq<int>)
    requires IsWordSeq(inseq);
    requires |inseq| > 0;
    ensures BEWordToBitSeq(inseq[0]) + BEWordSeqToBitSeq(inseq[1..]) == BEWordSeqToBitSeq(inseq);
{
    lemma_WordSeqToBitSeqChopOne(inseq, inseq[0], inseq[1..]);
}

static lemma lemma_SeqTransformContentsTail(inseq:seq<int>, tailseq:seq<int>, outbits:nat, scale:nat, inbits:nat)
    requires IsDigitSeq(power2(inbits), inseq);
    requires 0<|inseq|;
    requires IsDigitSeq(power2(inbits), tailseq);
    requires inseq[|inseq|-1..] == tailseq;
    requires 0<outbits;
    requires 0<scale;
    requires outbits*scale == inbits;
    decreases |inseq|;
    
    ensures 0 <= (|inseq|-1)*scale;
    ensures (|inseq|-1)*scale < |BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq))|;
    ensures BEIntToDigitSeq(power2(outbits), scale, BEDigitSeqToInt(power2(inbits), tailseq))
        == BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq))[(|inseq|-1)*scale..];
{
    var headseq := inseq[..|inseq|-1];
    assert |tailseq| == 1;

    var outseq := BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq));
    var outheadseq := BEIntToDigitSeq(power2(outbits), |headseq|*scale, BEDigitSeqToInt(power2(inbits), headseq));
    var outtailseq := BEIntToDigitSeq(power2(outbits), |tailseq|*scale, BEDigitSeqToInt(power2(inbits), tailseq));

    assert |headseq| == |inseq|-1;
    calc {
        |outheadseq|;
        { lemma_SeqTransform_structure(headseq, outbits, scale, inbits); }
        |headseq|*scale;
        (|inseq|-1)*scale;
    }

    calc {
        outheadseq + outtailseq;
            { lemma_SeqTransformSnip(inseq, headseq, tailseq, outbits, scale, inbits); }
        outseq;
    }
    assert outseq[|outheadseq|..] == outtailseq;

    calc {
        BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq))[(|inseq|-1)*scale..];
        outseq[|outheadseq|..];
        outtailseq;
        BEIntToDigitSeq(power2(outbits), |tailseq|*scale, BEDigitSeqToInt(power2(inbits), tailseq));
            { lemma_mul_basics(scale); }
        BEIntToDigitSeq(power2(outbits), scale, BEDigitSeqToInt(power2(inbits), tailseq));
    }

    calc {
        (|inseq|-1)*scale;
        <    { lemma_mul_strict_inequality_forall(); }
        |inseq|*scale;
        { lemma_SeqTransform_structure(inseq, outbits, scale, inbits); }
        |outseq|;
        |BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq))|;
    }
}

static lemma lemma_SeqTransformContentsLeft(inseq:seq<int>, truncseq:seq<int>, outbits:nat, scale:nat, inbits:nat)
    requires IsDigitSeq(power2(inbits), inseq);
    requires 0<|inseq|;
    requires IsDigitSeq(power2(inbits), truncseq);
    requires inseq[..|inseq|-1] == truncseq;
    requires 0<outbits;
    requires 0<scale;
    requires outbits*scale == inbits;
    decreases |inseq|;
    ensures 0 <= (|inseq|-1)*scale <= |BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq))|;
    ensures
        BEIntToDigitSeq(power2(outbits), |truncseq|*scale, BEDigitSeqToInt(power2(inbits), truncseq))
        == BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq))[..(|inseq|-1)*scale];
{
    lemma_mul_nonnegative(|inseq|-1,scale);
    calc {
        (|inseq|-1)*scale;
            { lemma_mul_is_distributive_forall(); }
        |inseq|*scale-mul(1,scale);
            { lemma_mul_basics_forall(); }
        |inseq|*scale - scale;
        < |inseq|*scale;
            { lemma_SeqTransform_structure(inseq, outbits, scale, inbits); }
        |BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq))|;
    }

    var tailseq := inseq[|inseq|-1..];

    var outseq := BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq));
    var outtruncseq := BEIntToDigitSeq(power2(outbits), |truncseq|*scale, BEDigitSeqToInt(power2(inbits), truncseq));
    var outtailseq := BEIntToDigitSeq(power2(outbits), |tailseq|*scale, BEDigitSeqToInt(power2(inbits), tailseq));
    lemma_SeqTransformSnip(inseq, truncseq, tailseq, outbits, scale, inbits);
    assert outseq == outtruncseq + outtailseq;
    calc {
        |outtruncseq|;
            { lemma_SeqTransform_structure(truncseq, outbits, scale, inbits); }
        |truncseq|*scale;
        (|inseq|-1)*scale;
    }
    calc {
        BEIntToDigitSeq(power2(outbits), |truncseq|*scale, BEDigitSeqToInt(power2(inbits), truncseq));
        outtruncseq;
        outseq[..|outtruncseq|];
        BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq))[..(|inseq|-1)*scale];
    }
}

static lemma lemma_BEByteSeqToBitSeq_ensures(byteseq:seq<int>)
    ensures IsByteSeq(byteseq) ==> IsBitSeq(BEByteSeqToBitSeq(byteseq));
    ensures IsByteSeq(byteseq) ==> |BEByteSeqToBitSeq(byteseq)| == |byteseq|*8;
{
    if (IsByteSeq(byteseq))
    {
        lemma_mul_is_mul_boogie(1,8);
        lemma_SeqTransform_structure(byteseq, 1, 8, 8);
        lemma_mul_is_mul_boogie(|byteseq|,8);
    }
}

static lemma lemma_BEWordSeqToByteSeq_ensures(wordseq:seq<int>)
    ensures IsWordSeq(wordseq) ==> IsByteSeq(BEWordSeqToByteSeq(wordseq));
    ensures IsWordSeq(wordseq) ==> |BEWordSeqToByteSeq(wordseq)| == |wordseq|*4;
{
    if (IsWordSeq(wordseq))
    {
        lemma_mul_is_mul_boogie(8,4);
        lemma_SeqTransform_structure(wordseq, 8, 4, 32);
        lemma_mul_is_mul_boogie(|wordseq|,4);
    }
}

static lemma lemma_BEWordSeqToBitSeq_ensures(wordseq:seq<int>)
    ensures IsWordSeq(wordseq) ==> IsBitSeq(BEWordSeqToBitSeq(wordseq));
    ensures IsWordSeq(wordseq) ==> |BEWordSeqToBitSeq(wordseq)| == |wordseq|*32;
{
    if (IsWordSeq(wordseq))
    {
        lemma_mul_is_mul_boogie(1,32);
        lemma_SeqTransform_structure(wordseq, 1, 32, 32);
        lemma_mul_is_mul_boogie(|wordseq|,32);
    }
}

static lemma lemma_concat_preserves_IsByteSeq(x:seq<int>, y:seq<int>)
    requires IsByteSeq(x);
    requires IsByteSeq(y);
    ensures IsByteSeq(x + y);
{
}

static lemma lemma_BEByteSeqToBitSeq_BEWordSeqToByteSeq(wordseq:seq<int>)
    requires IsWordSeq(wordseq);
    ensures IsByteSeq(BEWordSeqToByteSeq(wordseq));
    ensures BEByteSeqToBitSeq(BEWordSeqToByteSeq(wordseq)) == BEWordSeqToBitSeq(wordseq);
{
    var wordvalue := BEDigitSeqToInt(power2(32), wordseq);
    lemma_BEDigitSeqToInt_bound(power2(32), wordseq);
    var byteseq := BEIntToDigitSeq(power2(8), |wordseq|*4, wordvalue);

    assert byteseq == BEWordSeqToByteSeq(wordseq);
    lemma_power2_nonzero_bigger_than_one();

    calc {
        BEDigitSeqToInt(power2(32), wordseq);
        <   { lemma_BEDigitSeqToInt_bound(power2(32), wordseq); }
        power(power2(32), |wordseq|);
            {
                lemma_mul_is_mul_boogie(8, 4);
                lemma_pull_out_powers_of_2(8, 4, |wordseq|);
                lemma_mul_is_mul_boogie(4, |wordseq|);
            }
        power(power2(8), |wordseq|*4);
    }
    lemma_BEIntToDigitSeq_private_properties(power2(8), |wordseq|*4, BEDigitSeqToInt(power2(32), wordseq));
    assert IsByteSeq(byteseq);

    var bytevalue := BEDigitSeqToInt(power2(8), byteseq);
    var bitseq := BEIntToDigitSeq(power2(1), |byteseq|*8, bytevalue);


    lemma_mul_is_mul_boogie(|wordseq|,4);
    calc {
        BEWordSeqToByteSeq(wordseq);
        BEIntToDigitSeq(power2(8), |wordseq|*4, wordvalue);
    }

    lemma_mul_is_mul_boogie(8,4);
    lemma_SeqTransform_structure(wordseq, 8, 4, 32);
    assert |byteseq| == |wordseq|*4;
    assert |byteseq|*8 == |wordseq|*32;

    calc {
        bytevalue;
        BEDigitSeqToInt(power2(8), byteseq);
        {
            lemma_2toX();
            lemma_BEIntToDigitSeq_invertibility(power2(8), wordvalue, byteseq);
        }
        wordvalue;
    }

    calc {
        BEByteSeqToBitSeq(BEWordSeqToByteSeq(wordseq));
        BEByteSeqToBitSeq(byteseq);
        BEIntToDigitSeq(power2(1), |byteseq|*8, BEDigitSeqToInt(power2(8), byteseq));
        BEIntToDigitSeq(power2(1), |byteseq|*8, bytevalue);

        BEIntToDigitSeq(power2(1), |wordseq|*32, wordvalue);
        BEWordSeqToBitSeq(wordseq);
    }
}

static lemma lemma_BEIntToWordSeq_decomposition(data:seq<int>, i:int)
    requires IsWordSeq(data);
    requires 0<=i<|data|*32;
    decreases |data|;
    ensures |BEIntToDigitSeq(2, 32, data[i/32])| == 32;
    ensures |BEIntToDigitSeq(2, |data|*32, BEDigitSeqToInt(power2(32), data))| == |data| * 32;
    ensures BEIntToDigitSeq(2, 32, data[i/32])[i%32]
        == BEIntToDigitSeq(2, |data|*32, BEDigitSeqToInt(power2(32), data))[i];
{
    lemma_2toX();
    lemma_BEDigitSeqToInt_bound(power2(32), data);
    calc {
        power(power2(32), |data|);
            { lemma_power2_is_power_2(32); }
        power(power(2,32), |data|);
            { lemma_power_multiplies(2, 32, |data|); }
        power(2, mul(32,|data|));
            { lemma_mul_is_mul_boogie(32,|data|); }
        power(2, |data|*32);
    }
    lemma_power2_is_power_2(32);
    assert data[i/32] < power(2,32);
    calc {
        32;
            { lemma_BEIntToDigitSeq_private_properties(2, 32, data[i/32]); }
        |BEIntToDigitSeq(2, 32, data[i/32])|;
    }
    assert BEDigitSeqToInt(power2(32), data) < power(power2(32), |data|);
    calc {
        |data|*32;
            { lemma_BEIntToDigitSeq_private_properties(2, |data|*32, BEDigitSeqToInt(power2(32), data)); }
        |BEIntToDigitSeq(2, |data|*32, BEDigitSeqToInt(power2(32), data))|;
    }

    lemma_power2_1_is_2();

    assert 0<|data|;
    if (|data|*32-32 <= i)
    {
        //- i points into last word. Collapse away front of sequence.
        var tailseq := data[|data|-1..];

        lemma_mul_is_mul_boogie(1, 32);
        lemma_SeqTransform_structure(tailseq, 1, 32, 32);
        lemma_mul_is_mul_boogie(|tailseq|,32);
        assert |tailseq| == 1;
        assert IsDigitSeq(power2(32), tailseq);

        calc {
            BEIntToDigitSeq(2, 32, data[i/32]);
            BEIntToDigitSeq(2, 32, tailseq[0]);
                { lemma_mul_basics_forall(); }
            BEIntToDigitSeq(2, 32, mul(0,power2(32)) + tailseq[0]);
                { reveal_BEDigitSeqToInt_private(); }
            BEIntToDigitSeq(2, 32, mul(BEDigitSeqToInt_private(power2(32), []),power2(32)) + tailseq[0]);
                { assert [] == tailseq[0..|tailseq|-1]; }
            BEIntToDigitSeq(2, 32,
                BEDigitSeqToInt_private(power2(32), tailseq[0..|tailseq|-1])*power2(32) + tailseq[|tailseq|-1] );
                { reveal_BEDigitSeqToInt_private(); }
            BEIntToDigitSeq(2, 32, BEDigitSeqToInt_private(power2(32), tailseq));
            BEIntToDigitSeq(2, 32, BEDigitSeqToInt(power2(32), tailseq));
        }

        calc {
            BEIntToDigitSeq(2, 32, data[i/32])[i%32];
            BEIntToDigitSeq(2, 32, BEDigitSeqToInt(power2(32), tailseq))[i%32];
            BEIntToDigitSeq(2, 32, BEDigitSeqToInt(power2(32), tailseq))[i-(|data|-1)*32];
            {
                lemma_mul_basics_forall();
                lemma_SeqTransformContentsTail(data, tailseq, 1, 32, 32);
                lemma_mul_is_mul_boogie(|data|,32);
                lemma_mul_is_mul_boogie(|data|-1,32);
            }
            BEIntToDigitSeq(2, |data|*32, BEDigitSeqToInt(power2(32), data))[(|data|-1)*32..][i-(|data|-1)*32];

            BEIntToDigitSeq(2, |data|*32, BEDigitSeqToInt(power2(32), data))[i];

        }
    }
    else
    {
        //- i doesn't point to last word; strip it off and recurse.
        //- i points to last word
        var truncseq := data[0..|data|-1];

        calc {
            BEIntToDigitSeq(2, 32, data[i/32])[i%32];
            BEIntToDigitSeq(2, 32, truncseq[i/32])[i%32];
                { lemma_BEIntToWordSeq_decomposition(truncseq, i); }
            BEIntToDigitSeq(2, |truncseq|*32, BEDigitSeqToInt(power2(32), truncseq))[i];
            {
                lemma_mul_basics_forall();
                lemma_SeqTransformContentsLeft(data, truncseq, 1, 32, 32);
                lemma_mul_is_mul_boogie(|truncseq|,32);
                lemma_mul_is_mul_boogie(|data|,32);
            }
            BEIntToDigitSeq(2, |data|*32, BEDigitSeqToInt(power2(32), data))[..(|data|-1)*32][i];
            BEIntToDigitSeq(2, |data|*32, BEDigitSeqToInt(power2(32), data))[i];
        }
    }
}

//- converse of lemma_BEWordSeqToInt_BEIntToByteSeq
static lemma lemma_BEIntToByteSeq_BEWordSeqToInt(byteseq:seq<int>, wordseq:seq<int>)
    requires IsByteSeq(byteseq);
    requires IsWordSeq(wordseq);
    requires BEByteSeqToInt(byteseq) == BEWordSeqToInt(wordseq);
    requires |byteseq| == |wordseq|*4;
    ensures BEWordSeqToByteSeq(wordseq) == byteseq;
{
    lemma_2toX();
    var intvalue := BEByteSeqToInt(byteseq);
    lemma_BEDigitSeqToInt_bound(power2(8), byteseq);
    assert 0<=intvalue;

    lemma_BEDigitSeqToInt_invertibility(power2(8), intvalue, byteseq);
    assert byteseq == BEIntToDigitSeq(power2(8), |byteseq|, intvalue);

    lemma_BEDigitSeqToInt_invertibility(power2(32), intvalue, wordseq);
    assert wordseq == BEIntToDigitSeq(power2(32), |wordseq|, intvalue);

    calc {
        BEWordSeqToByteSeq(wordseq);
        BEIntToDigitSeq(power2(8), |wordseq|*4, BEDigitSeqToInt(power2(32), wordseq));
        BEIntToDigitSeq(power2(8), |byteseq|, BEDigitSeqToInt(power2(32), wordseq));
        BEIntToDigitSeq(power2(8), |byteseq|, BEDigitSeqToInt(power2(8), byteseq));
        BEIntToDigitSeq(power2(8), |byteseq|, intvalue);
        byteseq;
    }
}

//- converse of lemma_BEIntToByteSeq_BEWordSeqToInt
static lemma lemma_BEWordSeqToInt_BEIntToByteSeq(byteseq:seq<int>, wordseq:seq<int>)
    requires IsByteSeq(byteseq);
    requires IsWordSeq(wordseq);
    requires BEWordSeqToByteSeq(wordseq) == byteseq;
    requires |byteseq| == |wordseq|*4;
    ensures BEByteSeqToInt(byteseq) == BEWordSeqToInt(wordseq);
{
    lemma_2toX();
    lemma_BEDigitSeqToInt_bound(power2(32), wordseq);
    calc {
        BEByteSeqToInt(byteseq);
        BEByteSeqToInt(BEWordSeqToByteSeq(wordseq));
        BEDigitSeqToInt(power2(8), BEWordSeqToByteSeq(wordseq));
        BEDigitSeqToInt(power2(8),
            BEIntToDigitSeq(power2(8), |wordseq|*4, BEDigitSeqToInt(power2(32), wordseq)));
            { lemma_BEInt_decoding_general(power2(8), |byteseq|, BEDigitSeqToInt(power2(32), wordseq)); }
        BEDigitSeqToInt(power2(32), wordseq);
        BEWordSeqToInt(wordseq);
    }
}

static lemma BEByteSeqToWordSeq_base1(bs:seq<int>, ws:seq<int>)
    requires |bs|==1;
    requires IsByteSeq(bs);
    requires ws == [bs[0]];
    ensures IsWordSeq(ws);
    ensures BEWordSeqToInt(ws) == BEByteSeqToInt(bs);
{
    reveal_BEDigitSeqToInt_private();
    lemma_mul_basics_forall();
    lemma_power2_increases(8,32);
    lemma_2toX();
    calc {
        BEWordSeqToInt(ws);
        BEDigitSeqToInt(power2(32), ws[0..0])*power2(32) + ws[0];
        BEDigitSeqToInt(power2(8), bs[0..0])*power2(8) + bs[0];
        BEByteSeqToInt(bs);
    }
}

static lemma BEByteSeqToWordSeq_base2(bs:seq<int>, ws:seq<int>)
    requires |bs|==2;
    requires IsByteSeq(bs);
    requires ws == [bs[0] * 256 + bs[1]];
    ensures IsWordSeq(ws);
    ensures BEWordSeqToInt(ws) == BEByteSeqToInt(bs);
{
    reveal_BEDigitSeqToInt_private();
    lemma_mul_basics_forall();
    lemma_power2_increases(8,32);
    lemma_2toX();
    calc {
        BEWordSeqToInt(ws);
        BEDigitSeqToInt(power2(32), ws[0..0])*power2(32) + ws[0];
        bs[0] * 256 + bs[1];
            { lemma_mul_is_mul_boogie(bs[0], power2(8)); }
        bs[0] * power2(8) + bs[1];
        (BEDigitSeqToInt_private(power2(8), bs[0..0])*power2(8) + bs[0])*power2(8)+bs[1];
            { lemma_sequence_reduction(bs, 1); }
        BEDigitSeqToInt(power2(8), bs[0..1])*power2(8) + bs[1];
        BEByteSeqToInt(bs);
    }
}

static lemma BEByteSeqToWordSeq_base3(bs:seq<int>, ws:seq<int>)
    requires |bs|==3;
    requires IsByteSeq(bs);
    requires ws == [bs[0] * 256*256 + bs[1] * 256 + bs[2]];
    ensures IsWordSeq(ws);
    ensures BEWordSeqToInt(ws) == BEByteSeqToInt(bs);
{
    reveal_BEDigitSeqToInt_private();
    lemma_mul_basics_forall();
    lemma_power2_increases(8,32);
    lemma_2toX();
    calc {
        BEWordSeqToInt(ws);
        BEDigitSeqToInt(power2(32), ws[0..0])*power2(32) + ws[0];
        bs[0] * 256*256 + bs[1] * 256 + bs[2];
        (bs[0] * 256 + bs[1]) * 256 + bs[2];
            {
                lemma_mul_is_mul_boogie(bs[0], power2(8));
                lemma_mul_is_mul_boogie(bs[0] * power2(8) + bs[1], power2(8));
            }
        (bs[0] * power2(8) + bs[1]) * power2(8) + bs[2];
        ((BEDigitSeqToInt_private(power2(8), bs[0..0])*power2(8) + bs[0])*power2(8)+bs[1])*power2(8) + bs[2];
        (BEDigitSeqToInt_private(power2(8), bs[0..1])*power2(8)+bs[1])*power2(8) + bs[2];
            { lemma_sequence_reduction(bs, 2); }
        BEDigitSeqToInt_private(power2(8), bs[0..2])*power2(8) + bs[2];
//-            BEDigitSeqToInt_private(power2(8), bs);
//-            BEDigitSeqToInt(power2(8), bs);
        BEByteSeqToInt(bs);
    }
}

static lemma BEByteSeqToWordSeq_base4(bs:seq<int>, ws:seq<int>)
    requires |bs|==4;
    requires IsByteSeq(bs);
    requires ws == [bs[0] * 256*256*256 + bs[1] * 256*256 + bs[2] * 256 + bs[3]];
    ensures IsWordSeq(ws);
    ensures BEWordSeqToInt(ws) == BEByteSeqToInt(bs);
{
    reveal_BEDigitSeqToInt_private();
    lemma_mul_basics_forall();
    lemma_power2_increases(8,32);
    lemma_2toX();
    calc {
        BEWordSeqToInt(ws);
        BEDigitSeqToInt(power2(32), ws[0..0])*power2(32) + ws[0];
        bs[0] * 256*256*256 + bs[1] * 256*256 + bs[2] * 256 + bs[3];
        ((bs[0] * 256 + bs[1]) * 256 + bs[2]) * 256 + bs[3];
            {
                lemma_mul_is_mul_boogie(bs[0], power2(8));
                lemma_mul_is_mul_boogie(bs[0] * power2(8) + bs[1], power2(8));
                lemma_mul_is_mul_boogie((bs[0] * power2(8) + bs[1]) * power2(8) + bs[2], power2(8));
            }
        ((bs[0] * power2(8) + bs[1]) * power2(8) + bs[2])*power2(8) + bs[3];

        (((bs[0])*power2(8) + bs[1])*power2(8) + bs[2])*power2(8) + bs[3];
        (((bs[|bs|-4])*power2(8) + bs[|bs|-3])*power2(8) + bs[|bs|-2])*power2(8) + bs[|bs|-1];
        BEByteSeqToInt([])*power2(32)
            + (((bs[|bs|-4])*power2(8) + bs[|bs|-3])*power2(8) + bs[|bs|-2])*power2(8) + bs[|bs|-1];
            { lemma_BEByteSeqToInt_unpack_four(bs, []); }
        BEByteSeqToInt(bs);
    }
}

static predicate BEByteSeqToWordSeq_base_props(bs:seq<int>, ws:seq<int>, padbytes:seq<int>)
    requires IsByteSeq(bs);
{
    IsWordSeq(ws)
    && (|bs|>0 ==> |ws|>0)
    && |ws| == (|bs|+3)/4
    && BEByteSeqToInt(bs) == BEWordSeqToInt(ws)
    && |BEWordSeqToByteSeq(ws)| >= |bs|
    && padbytes == SequenceOfZeros(|ws|*4 - |bs|)
    && IsByteSeq(padbytes)
    && BEWordSeqToByteSeq(ws) == padbytes + bs
    && ((|bs|%4)==0 ==> BEWordSeqToByteSeq(ws) == bs)
    && |ws|<=1
}

static method BEByteSeqToWordSeq_base(bs:seq<int>) returns (ws:seq<int>, ghost padbytes:seq<int>)
//-    decreases |bs|;
    requires IsByteSeq(bs);
    requires |bs|<=4;
    ensures BEByteSeqToWordSeq_base_props(bs, ws, padbytes);
//-    ensures IsWordSeq(ws);
//-    ensures |bs|>0 ==> |ws|>0;
//-    ensures |ws| == (|bs|+3)/4;
//-    ensures BEByteSeqToInt(bs) == BEWordSeqToInt(ws);
//-    ensures |BEWordSeqToByteSeq(ws)| >= |bs|;
//-    ensures padbytes == SequenceOfZeros(|ws|*4 - |bs|);
//-    ensures IsByteSeq(padbytes);
//-    ensures BEWordSeqToByteSeq(ws) == padbytes + bs;
//-    ensures (|bs|%4)==0 ==> BEWordSeqToByteSeq(ws) == bs;
//-    ensures |ws|<=1;
{
    reveal_BEDigitSeqToInt_private();
    lemma_mul_basics_forall();
    lemma_power2_increases(8,32);
    lemma_2toX();

    if (|bs|==0) {
        ws := [];
    } else if (|bs|==1) {
        ws := [bs[0]];
        BEByteSeqToWordSeq_base1(bs, ws);
    } else if (|bs|==2) {
        ws := [bs[0] * 256 + bs[1]];
        BEByteSeqToWordSeq_base2(bs, ws);
    } else if (|bs|==3) {
        ws := [bs[0] * 256*256 + bs[1] * 256 + bs[2]];
        BEByteSeqToWordSeq_base3(bs, ws);
    } else if (|bs|==4) {
        ws := [bs[0] * 256*256*256 + bs[1] * 256*256 + bs[2] * 256 + bs[3]];
        BEByteSeqToWordSeq_base4(bs, ws);
    } else {
        assert false;
        ws := []; //- dafnycc
    }

    padbytes := SequenceOfZeros(|ws|*4 - |bs|);
    lemma_BEByteSeqToWordSeq_impl_helper(bs, ws, padbytes);
}



static lemma lemma_BEByteSeqToWordSeq_base_empty(bs:seq<int>) returns (ws:seq<int>, padbytes:seq<int>)
    requires IsByteSeq(bs);
    requires |bs|==0;
    ensures BEByteSeqToWordSeq_base_props(bs, ws, padbytes);
{
    ws := [];
    padbytes := [];
    reveal_BEDigitSeqToInt_private();
    lemma_BEWordSeqToByteSeq_ensures(ws);
}

static method BEByteSeqToWordSeq_base_arrays(ba:array<int>, a_off:nat, a_len:nat, ghost bs:seq<int>) returns (wv:int, ghost ws:seq<int>, ghost padbytes:seq<int>)
    decreases |bs|;
    requires ba!=null;
    requires a_off+a_len <= ba.Length;
    requires ba[a_off..a_off+a_len]==bs;
    requires IsByteSeq(bs);
    requires |bs|<=4;
    ensures IsWordSeq(ws);
    ensures |bs|>0 ==> |ws|>0;
    ensures |bs|>0 ==> ws==[wv];
    ensures |ws| == (|bs|+3)/4;
    ensures BEByteSeqToInt(bs) == BEWordSeqToInt(ws);
    ensures |BEWordSeqToByteSeq(ws)| >= |bs|;
    ensures padbytes == SequenceOfZeros(|ws|*4 - |bs|);
    ensures IsByteSeq(padbytes);
    ensures BEWordSeqToByteSeq(ws) == padbytes + bs;
    ensures (|bs|%4)==0 ==> BEWordSeqToByteSeq(ws) == bs;
    ensures |ws|<=1;
{
    reveal_BEDigitSeqToInt_private();
    lemma_mul_basics_forall();
    lemma_power2_increases(8,32);
    lemma_2toX();

    if (a_len==0) {
        wv := 0;
        ws := [];
    } else if (a_len==1) {
        wv := ba[a_off+0];
        ws := [wv];
        BEByteSeqToWordSeq_base1(bs, ws);
    } else if (a_len==2) {
        wv := ba[a_off+0] * 256 + ba[a_off+1];
        ws := [wv];
        BEByteSeqToWordSeq_base2(bs, ws);
    } else if (a_len==3) {
        wv := ba[a_off+0] * 256*256 + ba[a_off+1] * 256 + ba[a_off+2];
        ws := [wv];
        BEByteSeqToWordSeq_base3(bs, ws);
    } else if (a_len==4) {
        wv := ba[a_off+0] * 256*256*256 + ba[a_off+1] * 256*256 + ba[a_off+2] * 256 + ba[a_off+3];
        ws := [wv];
        BEByteSeqToWordSeq_base4(bs, ws);
    } else {
        assert false;
        wv := 0;  //- dafnycc
        ws := []; //- dafnycc
    }

    padbytes := SequenceOfZeros(|ws|*4 - |bs|);
    lemma_BEByteSeqToWordSeq_impl_helper(bs, ws, padbytes);
}

static lemma lemma_BEByteSeqToWordSeq_impl_helper(bs:seq<int>, ws:seq<int>, padbytes:seq<int>)
    requires IsByteSeq(bs);
    requires IsWordSeq(ws);
    requires IsByteSeq(padbytes);
    requires |bs| <= |ws|*4;
    requires |ws| == (|bs|+3)/4;
    requires BEWordSeqToInt(ws) == BEByteSeqToInt(bs);
    requires padbytes == SequenceOfZeros(|ws|*4 - |bs|);
    ensures |BEWordSeqToByteSeq(ws)| >= |bs|;
    ensures BEWordSeqToByteSeq(ws) == padbytes + bs;
    ensures (|bs|%4)==0 ==> BEWordSeqToByteSeq(ws) == bs;
{
    lemma_2toX();
    lemma_BEWordSeqToByteSeq_ensures(ws);
    assert |BEWordSeqToByteSeq(ws)| == |padbytes| + |bs|;
    ghost var padded_bs := padbytes + bs;

    calc {
        BEByteSeqToInt(padded_bs);
            { lemma_LeadingZeros(power2(8), bs, padded_bs); }
        BEByteSeqToInt(bs);
        BEWordSeqToInt(ws);
    }
    lemma_BEIntToByteSeq_BEWordSeqToInt(padded_bs, ws);
    assert BEWordSeqToByteSeq(ws) == padded_bs;
    assert BEWordSeqToByteSeq(ws) == padbytes + bs;

    
    
    if (|bs|%4==0)
    {
        lemma_round_down(|bs|, 3, 4);
        calc {
            |bs|;
            mul(4,div((|bs|+3),4));
            mul(4,(|bs|+3)/4);
                { assert |ws| == (|bs|+3)/4; }
            mul(4,|ws|);
                { lemma_mul_is_mul_boogie(4, |ws|); }
            4*|ws|;
        }
        lemma_BEIntToByteSeq_BEWordSeqToInt(bs, ws);
    }
}

static lemma lemma_BEByteSeqToInt_BEWordSeqToInt_concatenation(bsa:seq<int>, bsb:seq<int>, wsa:seq<int>, wsb:seq<int>)
    requires IsByteSeq(bsa);
    requires IsByteSeq(bsb);
    requires IsWordSeq(wsa);
    requires IsWordSeq(wsb);
//-    requires |bsa| == |wsa|*4;
    requires |bsb| == |wsb|*4;
    requires BEByteSeqToInt(bsa)==BEWordSeqToInt(wsa);
    requires BEByteSeqToInt(bsb)==BEWordSeqToInt(wsb);
    decreases |wsb|;
    ensures BEByteSeqToInt(bsa + bsb)==BEWordSeqToInt(wsa+wsb);
{
    if (|wsb|==0)
    {
        assert bsa + bsb == bsa;
        assert wsa + wsb == wsa;
    }
    else
    {
        reveal_BEDigitSeqToInt_private();

        var sub_bsb := bsb[..|bsb|-4];
        var tail_bsb := bsb[|bsb|-4..];
        assert sub_bsb + tail_bsb == bsb;

        var sub_wsb := wsb[..|wsb|-1];
        var tail_wsb := wsb[|wsb|-1..];
        assert sub_wsb + tail_wsb == wsb;

        lemma_BEByteSeqToInt_strip_four(bsb, sub_bsb, tail_bsb);
        assert BEByteSeqToInt(bsb) ==
            BEByteSeqToInt(sub_bsb)*power2(32) + BEByteSeqToInt(tail_bsb);
        assert 0 <= BEByteSeqToInt(tail_bsb) < power2(32);
        lemma_fundamental_div_mod_converse(BEByteSeqToInt(bsb), power2(32),
            BEByteSeqToInt(sub_bsb), BEByteSeqToInt(tail_bsb));

        calc {
            BEWordSeqToInt(tail_wsb);
            BEDigitSeqToInt_private(power2(32), tail_wsb[0..|tail_wsb|-1])*power2(32) + tail_wsb[|tail_wsb|-1];
            BEDigitSeqToInt_private(power2(32), [])*power2(32) + tail_wsb[|tail_wsb|-1];
                { lemma_mul_basics_forall(); }
            tail_wsb[|tail_wsb|-1];
            tail_wsb[0];
        }
        assert 0 <= BEWordSeqToInt(tail_wsb) < power2(32);
        calc {
            BEWordSeqToInt(wsb);
            BEDigitSeqToInt_private(power2(32), wsb[0..|wsb|-1])*power2(32) + wsb[|wsb|-1];
                { lemma_vacuous_statement_about_a_sequence(wsb, |wsb|-1); }
            BEDigitSeqToInt_private(power2(32), sub_wsb)*power2(32) + wsb[|wsb|-1];
            BEDigitSeqToInt_private(power2(32), sub_wsb)*power2(32) + tail_wsb[0];
            BEWordSeqToInt(sub_wsb)*power2(32) + tail_wsb[0];
            BEWordSeqToInt(sub_wsb)*power2(32) + BEWordSeqToInt(tail_wsb);
        }
        lemma_fundamental_div_mod_converse(BEWordSeqToInt(wsb), power2(32),
            BEWordSeqToInt(sub_wsb), BEWordSeqToInt(tail_wsb));

        assert BEByteSeqToInt(sub_bsb)==BEWordSeqToInt(sub_wsb);
        assert BEByteSeqToInt(tail_bsb)==BEWordSeqToInt(tail_wsb);

        calc {
            BEByteSeqToInt(bsa+bsb);
            BEByteSeqToInt(bsa+bsb);
            BEByteSeqToInt(bsa+(sub_bsb+tail_bsb));
                { lemma_seq_concatenation_associative(bsa, sub_bsb, tail_bsb); }
                //-{ assert bsa+(sub_bsb+tail_bsb) == (bsa+sub_bsb)+tail_bsb; }
            BEByteSeqToInt((bsa+sub_bsb)+tail_bsb);
            {
                lemma_BEByteSeqToInt_strip_four(
                    (bsa+sub_bsb)+tail_bsb,
                    bsa+sub_bsb,
                    tail_bsb);
            }
            BEByteSeqToInt(bsa+sub_bsb)*power2(32) + BEByteSeqToInt(tail_bsb);
            {
                assert BEByteSeqToInt(sub_bsb)==BEWordSeqToInt(sub_wsb);
                lemma_BEByteSeqToInt_BEWordSeqToInt_concatenation(bsa, sub_bsb, wsa, sub_wsb);
            }
            BEWordSeqToInt(wsa+sub_wsb)*power2(32) + BEByteSeqToInt(tail_bsb);
            {
                assert BEByteSeqToInt(tail_bsb)==BEWordSeqToInt(tail_wsb);
                lemma_mul_basics_forall();
                calc {
                    BEByteSeqToInt([]);
                    0;
                    BEWordSeqToInt([]);
                }
                lemma_BEByteSeqToInt_BEWordSeqToInt_concatenation(tail_bsb, [], tail_wsb, []);
            }
            BEWordSeqToInt(wsa+sub_wsb)*power2(32) + BEWordSeqToInt(tail_wsb);
            {
                reveal_BEDigitSeqToInt_private();
                var digits := (wsa+sub_wsb)+tail_wsb;
                assert digits[0..|digits|-1] == (wsa+sub_wsb);
                assert digits[|digits|-1..] == tail_wsb;
                calc {
                    digits[|digits|-1];
                    tail_wsb[0];
                        { lemma_mul_basics_forall(); }
                    mul(0,power2(32)) + tail_wsb[0];
                    BEDigitSeqToInt_private(power2(32), [])*power2(32) + tail_wsb[0];
                    BEDigitSeqToInt_private(power2(32), tail_wsb[0..|tail_wsb|-1])*power2(32) + tail_wsb[0];
                    BEDigitSeqToInt_private(power2(32), tail_wsb[0..|tail_wsb|-1])*power2(32) + tail_wsb[|tail_wsb|-1];
                    BEDigitSeqToInt_private(power2(32), tail_wsb);
                    BEWordSeqToInt(tail_wsb);
                }
                calc {
                    BEWordSeqToInt((wsa+sub_wsb)+tail_wsb);
                    BEDigitSeqToInt_private(power2(32), (wsa+sub_wsb))*power2(32) + tail_wsb[0];
                    BEWordSeqToInt(wsa+sub_wsb)*power2(32) + BEWordSeqToInt(tail_wsb);
                }
                assert IsWordSeq((wsa+sub_wsb)+tail_wsb);
            }
            BEWordSeqToInt((wsa+sub_wsb)+tail_wsb);
                { lemma_seq_concatenation_associative(wsa,sub_wsb,tail_wsb); }
            BEWordSeqToInt(wsa+(sub_wsb+tail_wsb));
            BEWordSeqToInt(wsa+wsb);
        }
    }
}

static predicate BEByteSeqToWordSeq_loop_invariants(
    bs:seq<int>, ptr:int, ws:seq<int>)
    requires IsByteSeq(bs);
    requires |bs|>0;
    requires ptr <= |bs|;
{
    ptr>0
    && IsWordSeq(ws)
    && |bs[ptr..]| <= |ws|*4
    && |ws| == (|bs[ptr..]|+3)/4
    && BEWordSeqToInt(ws) == BEByteSeqToInt(bs[ptr..])
    && (|bs|-ptr) % 4 == 0
    && |bs[ptr..]| == mul(|ws|,4)
}

static lemma lemma_BEByteSeqToWordSeq_iterative_loop(
    bs:seq<int>, prefix_bs:seq<int>, prefix_word:seq<int>,
    ptr:int, ws:seq<int>, ptr':int, ws':seq<int>)

    requires IsByteSeq(bs);
    requires |bs|>0;
    requires ptr <= |bs|;
    requires IsWordSeq(prefix_word);
    requires |prefix_word|==1;
    requires IsByteSeq(prefix_bs);
    requires ptr > 4;
    requires prefix_bs == bs[ptr-4..ptr];
    requires BEByteSeqToInt(prefix_bs) == BEWordSeqToInt(prefix_word);

    requires BEByteSeqToWordSeq_loop_invariants(bs, ptr, ws);

    requires ptr' == ptr - 4;
    requires ws' == prefix_word + ws;

    ensures BEByteSeqToWordSeq_loop_invariants(bs, ptr', ws');
{
    calc {
        BEWordSeqToInt(ws');
        BEWordSeqToInt(prefix_word + ws);
        {
            lemma_mul_is_mul_boogie(|ws|,4);
            assert |bs[ptr..]| == |ws|*4;
            lemma_BEByteSeqToInt_BEWordSeqToInt_concatenation(
                prefix_bs, bs[ptr..], prefix_word, ws);
        }
        BEByteSeqToInt(prefix_bs + bs[ptr..]);
        BEByteSeqToInt(prefix_bs + bs[ptr..]);
        BEByteSeqToInt(bs[ptr-4..ptr] + bs[ptr..]);
            { assert bs[ptr-4..ptr] + bs[ptr..] == bs[ptr-4..]; }
        BEByteSeqToInt(bs[ptr-4..]);
    }

    calc {
        (|bs| - ptr') % 4;
        (|bs| - (ptr-4)) % 4;
        (|bs| - ptr + 4) % 4;
        mod(|bs| - ptr + 4, 4);
            { lemma_mul_basics_forall(); lemma_mod_multiples_vanish(1, |bs|-ptr, 4); }
        mod(|bs| - ptr, 4);
        (|bs| - ptr) % 4;
        0;
    }
//-    assert |ws|+1 == |ws'|;
    calc {
        |bs[ptr'..]|;
        |bs[ptr..]|+4;
            { lemma_mul_basics_forall(); }
        mul(|ws|,4)+mul(1,4);
            { lemma_mul_is_distributive_forall(); }
        mul(|ws|+1,4);
        mul(|ws'|,4);
    }
}

static lemma lemma_BEByteSeqToWordSeq_loop_invariants_initial(bs:seq<int>, ptr:int, ws:seq<int>)
    requires |bs|==ptr;
    requires |ws|==0;
    requires IsByteSeq(bs);
    requires |bs|>0;
    ensures BEByteSeqToWordSeq_loop_invariants(bs, ptr, ws);
{
    calc {
        true;
        { reveal_BEDigitSeqToInt_private();
            calc {
                BEWordSeqToInt(ws);
                BEWordSeqToInt([]);
                0;
                BEByteSeqToInt([]);
                BEByteSeqToInt(bs[ptr..]);
            }
        }
        BEWordSeqToInt(ws) == BEByteSeqToInt(bs[ptr..]);
            { lemma_mul_basics(4); }
        BEByteSeqToWordSeq_loop_invariants(bs, ptr, ws);
    }
}

static lemma lemma_BEByteSeqToWordSeq_impl_final(bs:seq<int>, ws:seq<int>, padbytes:seq<int>, ptr:int, old_ws:seq<int>, prefix_bs:seq<int>, prefix_word:seq<int>)
    requires IsByteSeq(bs);
    requires IsByteSeq(prefix_bs);
    requires IsWordSeq(ws);
    requires IsWordSeq(prefix_word);
    requires 0 < ptr <= 4;
    requires (|bs|-ptr) % 4 == 0;
    requires ptr <= |bs|;
    requires BEByteSeqToWordSeq_loop_invariants(bs, ptr, old_ws);
    requires |old_ws| == (|bs[ptr..]|+3)/4;
    requires ws == prefix_word + old_ws;
    requires prefix_bs == bs[0..ptr];
    requires BEByteSeqToWordSeq_base_props(prefix_bs, prefix_word, padbytes);
    ensures |ws| == (|bs|+3)/4;
    ensures BEByteSeqToInt(bs) == BEWordSeqToInt(ws);
    ensures |BEWordSeqToByteSeq(ws)| >= |bs|;
    ensures padbytes == SequenceOfZeros(|ws|*4 - |bs|);
    ensures BEWordSeqToByteSeq(ws) == padbytes + bs;
    ensures (|bs|%4)==0 ==> BEWordSeqToByteSeq(ws) == bs;
{
    calc {
        |ws|;
        |prefix_word| + |old_ws|;
        |prefix_word| + (|bs[ptr..]|+3)/4;
        {
            assert BEByteSeqToWordSeq_base_props(prefix_bs, prefix_word, padbytes);
            assert |prefix_word| == (|prefix_bs|+3)/4;
            assert prefix_bs == bs[0..ptr];
        }
        (|bs[0..ptr]|+3)/4 + (|bs[ptr..]|+3)/4;
        (ptr+3)/4 + (|bs|-ptr+3)/4;
        1 + (|bs|-ptr)/4;
        (|bs|+3)/4;
        (|bs[0..]|+3)/4;
    }

    lemma_mul_is_mul_boogie(|old_ws|,4);
    assert |bs[ptr..]| == |old_ws|*4;
    lemma_BEByteSeqToInt_BEWordSeqToInt_concatenation(
        prefix_bs, bs[ptr..], prefix_word, old_ws);
    assert bs[0..ptr] + bs[ptr..] == bs[0..] + [] == bs;

    assert BEWordSeqToInt(ws) == BEByteSeqToInt(bs);
    calc {
        padbytes;
        SequenceOfZeros(|prefix_word|*4 - |bs[0..ptr]|);
        calc {
            |bs[0..ptr]|;
            ptr;
            |bs|-(|bs|-ptr);
            { assert (|bs|-ptr) % 4 == 0 ; }
            |bs|-((|bs|-ptr+3)/4)*4;
            |bs|-((|bs[ptr..]|+3)/4)*4;
            |bs|-|old_ws|*4;
        }
        SequenceOfZeros(|prefix_word|*4 + |old_ws|*4 - |bs|);
        SequenceOfZeros((|prefix_word| + |old_ws|)*4 - |bs|);
        SequenceOfZeros(|ws|*4 - |bs|);
    }
    lemma_BEByteSeqToWordSeq_impl_helper(bs, ws, padbytes);
}

static lemma lemma_WordsBytesEquivalence(bs:seq<int>, ws:seq<int>)
    requires IsByteSeq(bs);
    requires IsWordSeq(ws);
    requires BEByteSeqToInt(bs) == BEWordSeqToInt(ws);
    requires (|bs|%4)==0;
    requires |ws|*4==|bs|;
    ensures BEWordSeqToByteSeq(ws) == bs;
    ensures BEByteSeqToWordSeq(bs) == ws;
{
    lemma_2toX();
    lemma_BEDigitSeqToInt_bound(power2(8), bs);
    lemma_BEDigitSeqToInt_bound(power2(32), ws);
    lemma_BEDigitSeqToInt_invertibility(power2(8), BEByteSeqToInt(bs), bs);
    lemma_BEDigitSeqToInt_invertibility(power2(32), BEWordSeqToInt(ws), ws);
}

static method BEByteSeqToWordSeq_impl(bs:seq<int>) returns (ws:seq<int>, ghost padbytes:seq<int>)
//-    decreases |bs|;
    requires IsByteSeq(bs);
    ensures IsWordSeq(ws);
    ensures |bs|>0 ==> |ws|>0;
    ensures |ws| == (|bs|+3)/4;
    ensures BEByteSeqToInt(bs) == BEWordSeqToInt(ws);
    ensures |BEWordSeqToByteSeq(ws)| >= |bs|;
    ensures padbytes == SequenceOfZeros(|ws|*4 - |bs|);
    ensures IsByteSeq(padbytes);
    ensures BEWordSeqToByteSeq(ws) == padbytes + bs;
    ensures (|bs|%4)==0 ==> BEWordSeqToByteSeq(ws) == bs;
    ensures (|bs|%4)==0 ==> BEByteSeqToWordSeq(bs) == ws;
{
    lemma_mul_basics_forall();
    lemma_power2_increases(8,32);
    lemma_2toX();

    if (|bs|==0)
    {
        ws,padbytes := BEByteSeqToWordSeq_base([]);
    }
    else
    {
        ws := [];
        var prefix_bs;
        var prefix_word;
        ghost var old_ws;
        ghost var old_ptr;
        var ptr := |bs|;
        lemma_BEByteSeqToWordSeq_loop_invariants_initial(bs, ptr, ws);
        while (ptr > 4)
            invariant ptr <= |bs|;
            invariant BEByteSeqToWordSeq_loop_invariants(bs, ptr, ws);
        {
            prefix_bs := bs[ptr-4..ptr];
            prefix_word,padbytes := BEByteSeqToWordSeq_base(prefix_bs);
            old_ws := ws;
            old_ptr := ptr;
            ws := prefix_word + ws;

            ghost var old_ptr2 := ptr;
            ptr := ptr - 4;
            lemma_BEByteSeqToWordSeq_iterative_loop(
                bs, prefix_bs, prefix_word, old_ptr2, old_ws, ptr, ws);
        }
        assert {:split_here} true;
        prefix_bs := bs[0..ptr];
        prefix_word,padbytes := BEByteSeqToWordSeq_base(prefix_bs);
        old_ws := ws;
        assert |old_ws| == (|bs[ptr..]|+3)/4;
        ws := prefix_word + ws;

        lemma_BEByteSeqToWordSeq_impl_final(bs, ws, padbytes, ptr, old_ws, prefix_bs, prefix_word);
    }
    if ((|bs|%4)==0) {
        lemma_WordsBytesEquivalence(bs, ws);
    }
}

static method BEByteSeqToWordSeq_impl_arrays(ba:array<int>, ghost bs:seq<int>) returns (wa:array<int>, ghost ws:seq<int>, ghost padbytes:seq<int>)
    requires ba!=null;
    requires ba[..]==bs;
    requires IsByteSeq(bs);
    ensures wa!=null;
    ensures wa[..]==ws;
    ensures IsWordSeq(ws);
    ensures |bs|>0 ==> |ws|>0;
    ensures |ws| == (|bs|+3)/4;
    ensures BEByteSeqToInt(bs) == BEWordSeqToInt(ws);
    ensures |BEWordSeqToByteSeq(ws)| >= |bs|;
    ensures padbytes == SequenceOfZeros(|ws|*4 - |bs|);
    ensures IsByteSeq(padbytes);
    ensures BEWordSeqToByteSeq(ws) == padbytes + bs;
    ensures (|bs|%4)==0 ==> BEWordSeqToByteSeq(ws) == bs;
    ensures fresh(wa);
{
    if (ba.Length==0)
    {
        wa := new int[0];
        ws,padbytes := lemma_BEByteSeqToWordSeq_base_empty([]);
    }
    else
    {
        wa := new int[(ba.Length+3)/4];
        var ptr := ba.Length;
        var wptr := wa.Length;
        ws := wa[..wa.Length-wptr];
        var wv:int;
        ghost var prefix_bs;
        ghost var prefix_word;
        ghost var old_ws;
        ghost var old_ptr;

        assert |bs|==ptr;
        lemma_BEByteSeqToWordSeq_loop_invariants_initial(bs, ptr, ws);
        while (ptr > 4)
            invariant ptr <= |bs|;
            invariant BEByteSeqToWordSeq_loop_invariants(bs, ptr, ws);
            invariant wptr == (ptr+3)/4;
            invariant wa[wptr..] == ws;
        {
            prefix_bs := bs[ptr-4..ptr];
            wv,prefix_word,padbytes := BEByteSeqToWordSeq_base_arrays(ba, ptr-4, 4, prefix_bs);
            old_ws := ws;
            old_ptr := ptr;
            ws := prefix_word + ws;
            wptr := wptr - 1;
            wa[wptr] := wv;

            ghost var old_ptr2 := ptr;
            ptr := ptr - 4;

            lemma_BEByteSeqToWordSeq_iterative_loop(
                bs, prefix_bs, prefix_word, old_ptr2, old_ws, ptr, ws);
        }
        prefix_bs := bs[0..ptr];
        wv,prefix_word,padbytes := BEByteSeqToWordSeq_base_arrays(ba, 0, ptr, prefix_bs);
        if (ptr>0)
        {
            old_ws := ws;

            wa[0] := wv;
            ws := wa[..wa.Length];
            assert wv == prefix_word[0];    //- OBSERVE
                                            
            forall (i | 0<=i<wa.Length)
                ensures 0<=wa[i]<power2(32);
            {
                if (i==0) {
                    assert wa[i]==wv;
                } else {
                    assert wa[i] == old_ws[i-1];
                }
            }
            assert IsWordSeq(ws);   
        }
        else
        {
            old_ws := ws;
            assert IsWordSeq(ws);   
        }

        lemma_BEByteSeqToWordSeq_impl_final(bs, ws, padbytes, ptr, old_ws, prefix_bs, prefix_word);
    }
}

static method BEWordSeqToByteSeq_recursive(ws:seq<int>) returns (bs:seq<int>)
    requires IsWordSeq(ws);
    decreases |ws|;
    ensures IsByteSeq(bs);
    ensures |bs| == |ws|*4;
    ensures BEByteSeqToInt(bs) == BEWordSeqToInt(ws);
    ensures BEWordSeqToByteSeq(ws) == bs;
{
    reveal_BEDigitSeqToInt_private();
    lemma_2toX();
    lemma_mul_basics_forall();

    if (|ws|==0) {
        bs := [];
//-        calc {
//-            BEByteSeqToInt(bs);
//-            0;
//-            BEWordSeqToInt(ws);
//-        }
    } else if (|ws|==1) {
        var i := ws[0];
        bs := [ i / 16777216, (i / 65536) % 256, (i / 256) % 256, i % 256 ];

        calc {
            i;
                { lemma_fundamental_div_mod(i, 256); lemma_mul_is_commutative_forall(); }
            mul(div(i,256),256) + mod(i, 256);
                { lemma_fundamental_div_mod(div(i,256), 256); lemma_mul_is_commutative_forall(); }
            mul(mul(div(div(i,256),256),256) + mod(div(i,256),256),256) + mod(i, 256);
                { lemma_div_denominator_forall(); }
            mul(mul(div(i,mul(256,256)),256) + mod(div(i,256),256),256) + mod(i, 256);
                { lemma_mul_is_mul_boogie(256, 256); }
            mul(mul(div(i,65536),256) + mod(div(i,256),256),256) + mod(i, 256);
                { lemma_fundamental_div_mod(div(i,65536), 256); lemma_mul_is_commutative_forall(); }
            mul(mul(mul(div(div(i,65536),256),256) + mod(div(i,65536),256),256) + mod(div(i,256),256),256) + mod(i, 256);
                { lemma_div_denominator_forall(); }
            mul(mul(mul(div(i,mul(65536,256)),256) + mod(div(i,65536),256),256) + mod(div(i,256),256),256) + mod(i, 256);
                { lemma_mul_is_mul_boogie(65536, 256); }
            mul(mul(mul(div(i,16777216),256) + mod(div(i,65536),256),256) + mod(div(i,256),256),256) + mod(i, 256);
            mul(mul(mul(div(i,16777216),power2(8)) + mod(div(i,65536),256),power2(8)) + mod(div(i,256),256),power2(8)) + mod(i, 256);
            mul(mul(mul(i/16777216,power2(8)) + mod(i/65536,256),power2(8)) + mod(i/256,256),power2(8)) + mod(i, 256);
            mul(mul(mul(i/16777216,power2(8)) + (i/65536)%256,power2(8)) + (i/256)%256,power2(8)) + i%256;
        }

        calc {
            BEByteSeqToInt(bs);
                { lemma_BEByteSeqToInt_unpack_four(bs, []); }
            BEByteSeqToInt([])*power2(32)
                + (((bs[|bs|-4])*power2(8) + bs[|bs|-3])*power2(8) + bs[|bs|-2])*power2(8) + bs[|bs|-1];
            (((bs[0])*power2(8) + bs[1])*power2(8) + bs[2])*power2(8) + bs[3];
            mul(mul(mul(bs[0],power2(8)) + bs[1],power2(8)) + bs[2],power2(8)) + bs[3];
            mul(mul(mul(i/16777216,power2(8)) + (i/65536)%256,power2(8)) + (i/256)%256,power2(8)) + i%256;
            i;
            BEDigitSeqToInt(power2(32), ws[0..0])*power2(32) + ws[0];
            BEWordSeqToInt(ws);
        }
    } else {
        var prefix_words := ws[0..|ws|-1];
        var suffix_words := ws[|ws|-1..];
        var prefix_bytes := BEWordSeqToByteSeq_impl(prefix_words);
        var suffix_bytes := BEWordSeqToByteSeq_impl(suffix_words);
        bs := prefix_bytes + suffix_bytes;

        calc {
            BEByteSeqToInt(bs);
                { lemma_BEByteSeqToInt_strip_four(bs, prefix_bytes, suffix_bytes); }
            BEByteSeqToInt(prefix_bytes) * power2(32) + BEByteSeqToInt(suffix_bytes);
            BEWordSeqToInt(prefix_words) * power2(32) + BEWordSeqToInt(suffix_words);
            BEWordSeqToInt(prefix_words) * power2(32) + (BEDigitSeqToInt(power2(32), suffix_words[0..0])*power2(32) + suffix_words[0]);
            BEDigitSeqToInt(power2(32), ws[0..|ws|-1])*power2(32) + ws[|ws|-1];
            BEWordSeqToInt(ws);
        }
    }
    lemma_BEIntToByteSeq_BEWordSeqToInt(bs, ws);
}

static predicate BEWordSeqToByteSeq_iterative_loop_invariant(ws:seq<int>, bs:seq<int>, ptr:int)
    requires IsWordSeq(ws);
{
    0 <= ptr <= |ws|
    && IsByteSeq(bs)
    && |bs| == mul(|ws[ptr..]|,4)
    && BEByteSeqToInt(bs) == BEWordSeqToInt(ws[ptr..])
}

static function method SplitOneWord(i:int) : seq<int>
    requires Word32(i);
{
    [ i / 16777216, (i / 65536) % 256, (i / 256) % 256, i % 256 ]
}

static lemma lemma_BEWordSeqToByteSeq_iterative_loop(ws:seq<int>, bs:seq<int>, ptr:int, bs':seq<int>, ptr':int)
    requires IsWordSeq(ws);
    requires BEWordSeqToByteSeq_iterative_loop_invariant(ws, bs, ptr);
    requires ptr > 0;
    requires ptr' == ptr - 1;
    requires bs' == SplitOneWord(ws[ptr']) + bs;
    ensures BEWordSeqToByteSeq_iterative_loop_invariant(ws, bs', ptr');
{
    lemma_2toX();
    reveal_BEDigitSeqToInt_private();
    lemma_mul_basics_forall();

    var i := ws[ptr'];
    var newbytes := SplitOneWord(ws[ptr']);


    calc {
        i;
            { lemma_fundamental_div_mod(i, 256); lemma_mul_is_commutative_forall(); }
        mul(div(i,256),256) + mod(i, 256);
            { lemma_fundamental_div_mod(div(i,256), 256); lemma_mul_is_commutative_forall(); }
        mul(mul(div(div(i,256),256),256) + mod(div(i,256),256),256) + mod(i, 256);
            { lemma_div_denominator_forall(); }
        mul(mul(div(i,mul(256,256)),256) + mod(div(i,256),256),256) + mod(i, 256);
            { lemma_mul_is_mul_boogie(256, 256); }
        mul(mul(div(i,65536),256) + mod(div(i,256),256),256) + mod(i, 256);
            { lemma_fundamental_div_mod(div(i,65536), 256); lemma_mul_is_commutative_forall(); }
        mul(mul(mul(div(div(i,65536),256),256) + mod(div(i,65536),256),256) + mod(div(i,256),256),256) + mod(i, 256);
            { lemma_div_denominator_forall(); }
        mul(mul(mul(div(i,mul(65536,256)),256) + mod(div(i,65536),256),256) + mod(div(i,256),256),256) + mod(i, 256);
            { lemma_mul_is_mul_boogie(65536, 256); }
        mul(mul(mul(div(i,16777216),256) + mod(div(i,65536),256),256) + mod(div(i,256),256),256) + mod(i, 256);
        mul(mul(mul(div(i,16777216),power2(8)) + mod(div(i,65536),256),power2(8)) + mod(div(i,256),256),power2(8)) + mod(i, 256);
        mul(mul(mul(i/16777216,power2(8)) + mod(i/65536,256),power2(8)) + mod(i/256,256),power2(8)) + mod(i, 256);
        mul(mul(mul(i/16777216,power2(8)) + (i/65536)%256,power2(8)) + (i/256)%256,power2(8)) + i%256;
    }

    var nbs := newbytes;
    var ows := ws[ptr..];
    var nws := [ws[ptr']];
    calc {
        BEByteSeqToInt(nbs);
            { lemma_BEByteSeqToInt_unpack_four(nbs, []); }
        BEByteSeqToInt([])*power2(32)
            + (((nbs[|nbs|-4])*power2(8) + nbs[|nbs|-3])*power2(8) + nbs[|nbs|-2])*power2(8) + nbs[|nbs|-1];
        (((nbs[0])*power2(8) + nbs[1])*power2(8) + nbs[2])*power2(8) + nbs[3];
        mul(mul(mul(nbs[0],power2(8)) + nbs[1],power2(8)) + nbs[2],power2(8)) + nbs[3];
        mul(mul(mul(i/16777216,power2(8)) + (i/65536)%256,power2(8)) + (i/256)%256,power2(8)) + i%256;
        i;
        BEDigitSeqToInt(power2(32), nws[0..0])*power2(32) + nws[0];
        BEWordSeqToInt(nws);
    }

    calc {
        |bs'|;
        |bs| + 4;
        mul(|ws[ptr..]|,4) + 4;
        mul(|ws[ptr'..]|-1,4) + 4;
            { lemma_mul_is_distributive_forall(); }
        mul(|ws[ptr'..]|,4)+ mul(-1,4) + 4;
            { lemma_mul_is_mul_boogie(-1,4); }
        mul(|ws[ptr'..]|,4);
    }
    calc {
        BEByteSeqToInt(bs');
        BEByteSeqToInt(newbytes+bs);
        {
            lemma_mul_is_mul_boogie(|ows|,4);
            lemma_BEByteSeqToInt_BEWordSeqToInt_concatenation(
                newbytes, bs, nws, ows);
        }
        BEWordSeqToInt(nws+ows);
        BEWordSeqToInt([ws[ptr']] + ws[ptr..]);
            { assert [ws[ptr']] + ws[ptr..] == ws[ptr'..]; }
        BEWordSeqToInt(ws[ptr'..]);
    }
}

static method BEWordSeqToByteSeq_impl(ws:seq<int>) returns (bs:seq<int>)
    requires IsWordSeq(ws);
    decreases |ws|;
    ensures IsByteSeq(bs);
    ensures |bs| == |ws|*4;
    ensures BEByteSeqToInt(bs) == BEWordSeqToInt(ws);
    ensures BEWordSeqToByteSeq(ws) == bs;
    ensures BEByteSeqToWordSeq(bs) == ws;
{
    reveal_BEDigitSeqToInt_private();
    lemma_mul_basics_forall();
    lemma_power2_increases(8,32);
    lemma_2toX();

    if (|ws|==0)
    {
        bs := [];
        assert BEByteSeqToInt(bs) == BEWordSeqToInt(ws);
        assert |bs| == |ws|*4;
    }
    else
    {
        bs := [];
        ghost var old_bs;
        ghost var old_ptr;
        var ptr := |ws|;
        calc {
            |bs|;
            0;
                { lemma_mul_basics_forall(); }
            |ws[ptr..]|*4;
        }
        while (ptr > 0)
            invariant BEWordSeqToByteSeq_iterative_loop_invariant(ws, bs, ptr);
        {
            old_bs := bs;
            old_ptr := ptr;

            ptr := ptr - 1;
            var i := ws[ptr];
            bs := SplitOneWord(ws[ptr]) + bs;

            lemma_BEWordSeqToByteSeq_iterative_loop(ws, old_bs, old_ptr, bs, ptr);
        }
        assert ptr==0;
        assert ws == ws[0..];
        assert ws == ws[0..];
        assert BEByteSeqToInt(bs) == BEWordSeqToInt(ws);
    }
    lemma_mul_is_mul_boogie(|ws|,4);
    assert |bs| == |ws|*4;
    lemma_BEIntToByteSeq_BEWordSeqToInt(bs, ws);
    lemma_WordsBytesEquivalence(bs, ws);
}

//-lemma lemma_NSeqIntConcatMultiplePreservesIsDigitSeq(place_value:int, seqs:seq<seq<int>>)
//-    requires forall i :: 0 <= i < |seqs| ==> IsDigitSeq(place_value, seqs[i]);
//-    ensures IsDigitSeq(place_value, NSeqIntConcatMultiple(seqs));
//-    decreases |seqs|;
//-{
//-    reveal_NSeqIntConcatMultiple();
//-    if |seqs| > 0 {
//-        lemma_NSeqIntConcatMultiplePreservesIsDigitSeq(place_value, seqs[1..]);
//-        lemma_concat_preserves_IsDigitSeq(place_value, seqs[0], NSeqIntConcatMultiple(seqs[1..]));
//-    }
//-}

static lemma lemma_concat_preserves_IsDigitSeq(place_value:int, x:seq<int>, y:seq<int>)
    requires IsDigitSeq(place_value, x);
    requires IsDigitSeq(place_value, y);
    ensures IsDigitSeq(place_value, x + y);
{
}

static lemma lemma_BEByteSeqToBitSeq_selection(bs:seq<int>, len:int)
    requires IsByteSeq(bs);
    requires 0 <= len <= |bs|;
    ensures |BEByteSeqToBitSeq(bs)| >= len*8;
    ensures BEByteSeqToBitSeq(bs)[..len*8] == BEByteSeqToBitSeq(bs[..len]);
{
    lemma_BEByteSeqToBitSeq_ensures(bs);
    calc {
        |BEByteSeqToBitSeq(bs)[..len*8]|;
        len*8;
            { lemma_BEByteSeqToBitSeq_ensures(bs[..len]); }
        |BEByteSeqToBitSeq(bs[..len])|;
    }
    forall (i | 0<=i<|BEByteSeqToBitSeq(bs)[..len*8]|)
        ensures BEByteSeqToBitSeq(bs)[..len*8][i] == BEByteSeqToBitSeq(bs[..len])[i];
    {
        lemma_mul_is_mul_boogie(1,8);
        var headbs := bs[..len];
        var tailbs := bs[len..];

        calc {
            BEByteSeqToBitSeq(headbs) + BEByteSeqToBitSeq(tailbs);
            BEIntToDigitSeq(power2(1), |headbs|*8, BEDigitSeqToInt(power2(8), headbs))
                + BEIntToDigitSeq(power2(1), |tailbs|*8, BEDigitSeqToInt(power2(8), tailbs));
                {
                    lemma_SeqTransformChop(bs, headbs, tailbs, 1, 8, 8);
                    lemma_mul_is_mul_boogie(|headbs|,8);
                    lemma_mul_is_mul_boogie(|tailbs|,8);
                    lemma_mul_is_mul_boogie(|bs|,8);
                }
            BEIntToDigitSeq(power2(1), |bs|*8, BEDigitSeqToInt(power2(8), bs));
            BEByteSeqToBitSeq(bs);
        }
        calc {
            BEByteSeqToBitSeq(bs)[..len*8][i];
            BEByteSeqToBitSeq(bs)[i];
            BEByteSeqToBitSeq(headbs)[i];
            BEByteSeqToBitSeq(bs[..len])[i];
        }
    }
}

static method BEWordToFourBytes_impl(x:int) returns (bytes:seq<int>)
    requires Word32(x);
    ensures  bytes == BEWordToFourBytes(x);
    ensures  IsByteSeq(bytes);
    ensures  |bytes| == 4;
    ensures  BEByteSeqToInt(bytes) == x;
{
    bytes := BEWordSeqToByteSeq_impl([x]);
    calc {
        x;
        { lemma_mul_basics_forall(); }
        mul(0,power2(32)) + [x][|[x]|-1];
        { reveal_BEDigitSeqToInt_private(); }
        BEDigitSeqToInt_private(power2(32), [])*power2(32)+ [x][|[x]|-1];
        { assert [] == [x][0..|[x]|-1]; }
        BEDigitSeqToInt_private(power2(32), [x][0..|[x]|-1])*power2(32)+ [x][|[x]|-1];
        { reveal_BEDigitSeqToInt_private(); }
        BEDigitSeqToInt_private(power2(32), [x]);
        BEDigitSeqToInt(power2(32), [x]);
        BEDigitSeqToInt(power2(8), bytes);
    }

    lemma_2toX();
    lemma_BEDigitSeqToInt_invertibility(power2(8), x, bytes);
}

static lemma lemma_BEWordToFourBytesUnique(a:int, b:int)
    requires Word32(a);
    requires Word32(b);
    requires BEWordToFourBytes(a) == BEWordToFourBytes(b);
    ensures  a == b;
{
    lemma_2toX();
    calc {
        power(power2(8), 4);
            { lemma_power2_is_power_2(8); }
        power(power(2, 8), 4);
            { lemma_power_multiplies(2,8,4); }
        power(2, mul(8, 4));
            { lemma_mul_is_mul_boogie(8,4); }
        power(2, 32);
            { lemma_power2_is_power_2(32); }
        power2(32);
    }
    assert power(power2(8), 4) == power2(32);
    lemma_BEIntToDigitSeq_private_properties(power2(8), 4, a);
    lemma_BEIntToDigitSeq_private_properties(power2(8), 4, b);
    lemma_BEIntToDigitSeq_invertibility(power2(8), a, BEWordToFourBytes(a));
    lemma_BEIntToDigitSeq_invertibility(power2(8), b, BEWordToFourBytes(b));
}

static lemma lemma_BEWordToFourBytes_literal(x:int)
    requires 0<=x<power2(8);
    ensures Word32(0);
    ensures Word32(x);
    ensures BEWordToFourBytes(x) == [0,0,0,x];
    ensures IsByteSeq(BEWordToFourBytes(x));
{
    lemma_2toX();
    reveal_BEIntToDigitSeq_private();
    calc {
        BEWordToFourBytes(x);
        BEIntToDigitSeq(power2(8), 4, x);
        BEIntToDigitSeq_private(power2(8), 4, x);
        BEIntToDigitSeq_private(power2(8), 3, x/power2(8)) + [ x % power2(8) ];
            { lemma_small_div(); lemma_small_mod(x, power2(8)); }
        BEIntToDigitSeq_private(power2(8), 3, 0) + [x];
        BEIntToDigitSeq_private(power2(8), 2, div(0,power2(8))) + [ mod(0, power2(8)) ] + [x];
            { lemma_small_div(); lemma_small_mod(0, power2(8)); }
        BEIntToDigitSeq_private(power2(8), 2, 0) + [0] + [x];
        BEIntToDigitSeq_private(power2(8), 1, div(0,power2(8))) + [ mod(0, power2(8)) ] + [0] + [x];
            { lemma_small_div(); lemma_small_mod(0, power2(8)); }
        BEIntToDigitSeq_private(power2(8), 1, 0) + [0] + [0] + [x];
        BEIntToDigitSeq_private(power2(8), 0, div(0,power2(8))) + [ mod(0, power2(8)) ] + [0] + [0] + [x];
            { lemma_small_div(); lemma_small_mod(0, power2(8)); }
        BEIntToDigitSeq_private(power2(8), 0, 0) + [0] + [0] + [0] + [x];
        [] + [0] + [0] + [0] + [x];
        [0,0,0,x];
    }
}

static lemma lemma_AllButLastOfPrefixIsPrefix(s:seq<int>, n:int)
    requires 0 < n <= |s|;
    ensures s[0..n][0..n-1] == s[0..n-1];
{
    assert |s[0..n][0..n-1]| == n-1;
    forall i | 0 <= i < n - 1
        ensures s[0..n][0..n-1][i] == s[0..n-1][i];
    {
        calc {
            s[0..n][0..n-1][i];
            s[0..n][i];
            s[0..n-1][i];
        }
    }
}

static lemma lemma_BEFourBytesToWordIsWord(bs:seq<int>)
    requires IsByteSeqOfLen(bs, 4);
    ensures Word32(BEByteSeqToInt(bs));
{
    lemma_BEByteSeqToInt_bound(bs);
    calc {
        BEByteSeqToInt(bs);
        < power2(8*|bs|);
        <= power2(8*4);
        == power2(32);
    }
}

static method BEFourBytesToWord_impl(bs:seq<int>) returns (ret:int)
    requires IsByteSeqOfLen(bs, 4);
    ensures ret == BEByteSeqToInt(bs);
    ensures Word32(ret);
{
    var ws, padbytes := BEByteSeqToWordSeq_impl(bs);
    ret := ws[0];
    reveal_BEDigitSeqToInt_private();
    calc {
        BEWordSeqToInt(ws);
        BEDigitSeqToInt_private(power2(32), ws[0..|ws|-1])*power2(32) + ws[0];
            { assert |ws|==1; assert ws[0..|ws|-1] == ws[0..0] == []; }
        BEDigitSeqToInt_private(power2(32), [])*power2(32) + ws[0];
        { lemma_mul_is_mul_boogie(0, power2(32)); }
        0*power2(32) + ws[0];
    }
    lemma_BEFourBytesToWordIsWord(bs);
}

static lemma lemma_ValueOfFourByteSeq(s:seq<int>)
    requires IsByteSeqOfLen(s, 4);
    ensures BEByteSeqToInt(s) == 0x1000000 * s[0] + 0x10000 * s[1] + 0x100 * s[2] + s[3];
{
    reveal_BEDigitSeqToInt_private();

    calc {
        BEByteSeqToInt(s);
        BEDigitSeqToInt_private(power2(8), s);
        BEDigitSeqToInt_private(power2(8), s[0..3])*power2(8) + s[3];
        { lemma_AllButLastOfPrefixIsPrefix(s, 3); }
        (BEDigitSeqToInt_private(power2(8), s[0..2])*power2(8) + s[2])*power2(8) + s[3];
        { lemma_AllButLastOfPrefixIsPrefix(s, 2); }
        ((BEDigitSeqToInt_private(power2(8), s[0..1])*power2(8) + s[1])*power2(8) + s[2])*power2(8) + s[3];
        { lemma_AllButLastOfPrefixIsPrefix(s, 1); }
        (((BEDigitSeqToInt_private(power2(8), s[0..0])*power2(8) + s[0])*power2(8) + s[1])*power2(8) + s[2])*power2(8) + s[3];
        (((BEDigitSeqToInt_private(power2(8), [])*power2(8) + s[0])*power2(8) + s[1])*power2(8) + s[2])*power2(8) + s[3];
        { lemma_mul_is_mul_boogie(0, power2(8)); }
        (((0*power2(8) + s[0])*power2(8) + s[1])*power2(8) + s[2])*power2(8) + s[3];
        ((s[0]*power2(8) + s[1])*power2(8) + s[2])*power2(8) + s[3];
        { lemma_mul_is_commutative_forall(); }
        power2(8)*(power2(8)*(power2(8)*s[0] + s[1]) + s[2]) + s[3];
        { lemma_mul_is_distributive_add(power2(8), power2(8)*s[0], s[1]); }
        power2(8)*(power2(8)*(power2(8)*s[0]) + power2(8)*s[1] + s[2]) + s[3];
        { lemma_mul_is_distributive_add(power2(8), power2(8)*(power2(8)*s[0]) + power2(8)*s[1], s[2]); }
        power2(8)*(power2(8)*(power2(8)*s[0]) + power2(8)*s[1]) + power2(8)*s[2] + s[3];
        { lemma_mul_is_distributive_add(power2(8), power2(8)*(power2(8)*s[0]), power2(8)*s[1]); }
        power2(8)*(power2(8)*(power2(8)*s[0])) + power2(8)*(power2(8)*s[1]) + power2(8)*s[2] + s[3];
        { lemma_mul_is_associative_forall(); }
        power2(8)*power2(8)*power2(8)*s[0] + power2(8)*power2(8)*s[1] + power2(8)*s[2] + s[3];
        { lemma_power2_adds(8, 8); }
        power2(16)*power2(8)*s[0] + power2(16)*s[1] + power2(8)*s[2] + s[3];
        { lemma_power2_adds(16, 8); }
        power2(24)*s[0] + power2(16)*s[1] + power2(8)*s[2] + s[3];
        { lemma_2to32();
          lemma_mul_is_mul_boogie(0x1000000, s[0]);
          lemma_mul_is_mul_boogie(0x10000, s[1]);
          lemma_mul_is_mul_boogie(0x100, s[2]); }
        0x1000000 * s[0] + 0x10000 * s[1] + 0x100 * s[2] + s[3];
    }
}

static lemma lemma_ValueOfFourByteSeqSpecific(s:seq<int>, n:int)
    requires IsByteSeqOfLen(s, 4);
    requires n == 0x1000000 * s[0] + 0x10000 * s[1] + 0x100 * s[2] + s[3];
    ensures BEByteSeqToInt(s) == n;
{
    lemma_ValueOfFourByteSeq(s);
}


static lemma lemma_BEIntToDigitSeqProducesRightSizedDigits(place_value:int, min_places:int, v:int)
    requires 1<place_value;
    requires 0<=min_places;
    requires 0<=v;
    requires v < power(place_value, min_places);
    ensures IsDigitSeq(place_value, BEIntToDigitSeq(place_value, min_places, v));
{
    lemma_BEIntToDigitSeq_private_properties(place_value, min_places, v);
}


static function BEByteSeqToWordSeq(bs:seq<int>) : seq<int>
    requires IsByteSeq(bs);
    requires |bs|%4==0;
//-    ensures IsWordSeq(BEByteSeqToWordSeq(bs));
//-    ensures BEWordSeqToByteSeq(BEByteSeqToWordSeq(bs)) == bs;
{
    BEIntToDigitSeq(power2(32), |bs|/4, BEDigitSeqToInt(power2(8), bs))
}

static function TailPad4(bs:seq<int>) : seq<int>
{
    bs+RepeatDigit(0, ((|bs|+3)/4)*4-|bs|)
}

static lemma lemma_BEByteSeqToWordSeqTailPadding_constructive_form(ws:seq<int>, bs:seq<int>, pad_len:nat)
    requires IsWordSeq(ws);
    requires IsByteSeq(bs);
    requires |ws| == (|bs| + 3) / 4;
    requires pad_len == ((|bs|+3)/4)*4-|bs|;
    requires BEWordSeqToByteSeq(ws) == bs + RepeatDigit(0, pad_len);
    ensures IsByteSeq(TailPad4(bs));
    ensures |TailPad4(bs)|%4 == 0;
    ensures ws == BEByteSeqToWordSeq(TailPad4(bs));
{
    lemma_2toX();

    assert TailPad4(bs) == bs+RepeatDigit_premium(0, ((|bs|+3)/4)*4-|bs|);  //- OBSERVE

    var padsize := |TailPad4(bs)| - |bs|;
    var wx := BEWordSeqToInt(ws);
    var bx := BEByteSeqToInt(TailPad4(bs));
    var L8 := 8;

    lemma_mul_nonnegative(L8, |TailPad4(bs)|);
    lemma_BEDigitSeqToInt_bound(power2(8), TailPad4(bs));
    assert 0 <= bx;
    calc {
        bx;
        BEDigitSeqToInt(power2(8), TailPad4(bs));
        <
        power(power2(8), |TailPad4(bs)|);
            { lemma_power2_is_power_2(8); }
        power(power(2,8), |TailPad4(bs)|);
            { lemma_power_multiplies(2,8,|TailPad4(bs)|); }
        power(2,L8*|TailPad4(bs)|);
            { lemma_power2_is_power_2(L8*|TailPad4(bs)|); }
        power2(L8*|TailPad4(bs)|);
    }
    assert bx < power2(L8*|TailPad4(bs)|);
    lemma_BEIntToDigitSeq_private_chop(8, |TailPad4(bs)|, padsize, bx);
    lemma_mul_nonnegative(L8, padsize);
    assert BEIntToDigitSeq_private(power2(8), |bs|, bx/power2(L8*padsize))
            + BEIntToDigitSeq_private(power2(8), padsize, bx%power2(L8*padsize))
            == BEIntToDigitSeq_private(power2(8), |TailPad4(bs)|, bx);

    calc {
        wx;
        BEWordSeqToInt(ws);
            { lemma_BEWordSeqToInt_BEIntToByteSeq(BEWordSeqToByteSeq(ws), ws); }
        BEByteSeqToInt(BEWordSeqToByteSeq(ws));
        BEByteSeqToInt(bs + RepeatDigit(0, pad_len));
        BEByteSeqToInt(TailPad4(bs));
        bx;
    }

    assert wx == bx;

    calc {
        ws;
            { lemma_BEDigitSeqToInt_invertibility(power2(32), wx, ws); }
        BEIntToDigitSeq(power2(32), |ws|, wx);
        BEIntToDigitSeq(power2(32), |ws|, bx);
            { assert |ws| == |TailPad4(bs)|/4; }
        BEIntToDigitSeq(power2(32), |TailPad4(bs)|/4, bx);
        BEIntToDigitSeq(power2(32), |TailPad4(bs)|/4, BEDigitSeqToInt(power2(8), TailPad4(bs)));
        BEByteSeqToWordSeq(TailPad4(bs));
    }
}














//


//









static lemma lemma_BEByteSeqToWordSeqTailPadding_bit_equivalence(bs:seq<int>, ws:seq<int>, padded_bs:seq<int>, padding:seq<int>, ghost_padding:seq<int>)
    requires IsByteSeq(bs);
    requires IsWordSeq(ws);
    requires IsByteSeq(padded_bs);
    requires IsByteSeq(padding);
    requires padded_bs == bs + padding;
    requires ghost_padding + padded_bs == BEWordSeqToByteSeq(ws);
    requires ghost_padding == [];
    ensures |bs|*8 <= |BEWordSeqToBitSeq(ws)|;
    ensures BEByteSeqToBitSeq(bs) == BEWordSeqToBitSeq(ws)[..|bs|*8];
{
    var padding_len := |padding|;
    calc {
        BEWordSeqToBitSeq(ws);
            { lemma_BEByteSeqToBitSeq_BEWordSeqToByteSeq(ws); }
        BEByteSeqToBitSeq(BEWordSeqToByteSeq(ws));
        BEByteSeqToBitSeq(ghost_padding + padded_bs);
            { assert ghost_padding + padded_bs == padded_bs; /* OBSERVE */ }
        BEByteSeqToBitSeq(padded_bs);
    }

    calc {
        |BEWordSeqToBitSeq(ws)|;
            { lemma_BEWordSeqToBitSeq_ensures(ws); }
        32*|ws|;
        8*(4*|ws|);
            { lemma_BEWordSeqToByteSeq_ensures(ws); }
        8*(|BEWordSeqToByteSeq(ws)|);
        8*(|ghost_padding|+|padded_bs|);
        8*|padded_bs|;
        >=
        8*|bs|;
    }

    var head := padded_bs[..|padded_bs|-padding_len];
    var tail := padded_bs[|padded_bs|-padding_len..];
    calc {
        BEByteSeqToBitSeq(bs);
        BEByteSeqToBitSeq(padded_bs[..|padded_bs|-padding_len]);
        BEByteSeqToBitSeq(head);
        BEByteSeqToBitSeq(head)[..|BEByteSeqToBitSeq(head)|];
        (BEByteSeqToBitSeq(head) + BEByteSeqToBitSeq(tail))[..|BEByteSeqToBitSeq(head)|];
        {
            assert padded_bs == head + tail;
            calc {
                BEByteSeqToBitSeq(head) + BEByteSeqToBitSeq(tail);
                    { lemma_mul_is_mul_boogie(|head|,8); }
                    { lemma_mul_is_mul_boogie(|tail|,8); }
                BEIntToDigitSeq(power2(1), mul(|head|,8), BEDigitSeqToInt(power2(8), head))
                    + BEIntToDigitSeq(power2(1), mul(|tail|,8), BEDigitSeqToInt(power2(8), tail));
                {
                    lemma_mul_basics_forall();
                    lemma_SeqTransformChop(padded_bs, head, tail, 1, 8, 8);
                }
                BEIntToDigitSeq(power2(1), mul(|padded_bs|,8), BEDigitSeqToInt(power2(8), padded_bs));
                    { lemma_mul_is_mul_boogie(|padded_bs|,8); }
                BEByteSeqToBitSeq(padded_bs);
            }
        }
        BEByteSeqToBitSeq(padded_bs)[..|BEByteSeqToBitSeq(head)|];
            { lemma_BEByteSeqToBitSeq_ensures(head); }
        BEByteSeqToBitSeq(padded_bs)[..|head|*8];
        BEByteSeqToBitSeq(padded_bs)[..|bs|*8];
        BEWordSeqToBitSeq(ws)[..|bs|*8];
    }
}

static lemma lemma_BEByteSeqToWordSeqTailPadding_more(
    bs:seq<int>, ws_len:int, padding_len:int, padding:seq<int>, padded_bs:seq<int>, ws:seq<int>, ghost_padding:seq<int>)
    requires IsByteSeq(bs);
    requires ws_len == (|bs|-1)/4+1;
    requires padding_len == ws_len*4 - |bs|;
    requires padding == RepeatDigit_premium(0, padding_len);
    requires IsWordSeq(bs);
    requires IsByteSeq(padded_bs);
    requires padded_bs == bs + padding;
    requires IsWordSeq(ws);
    requires |padded_bs|>0 ==> |ws|>0;
    requires |ws| == (|padded_bs|+3)/4;
    requires BEByteSeqToInt(padded_bs) == BEWordSeqToInt(ws);
    requires |BEWordSeqToByteSeq(ws)| >= |padded_bs|;
    requires ghost_padding == SequenceOfZeros(|ws|*4 - |padded_bs|);
    requires IsByteSeq(ghost_padding);
    requires BEWordSeqToByteSeq(ws) == ghost_padding + padded_bs;
    requires (|padded_bs|%4)==0 ==> BEWordSeqToByteSeq(ws) == padded_bs;

    ensures ghost_padding==[];
    ensures |padded_bs|%4 == 0;
    ensures BEWordSeqToByteSeq(ws) == padded_bs;
{
    calc {
        |ghost_padding|;
        |SequenceOfZeros(|ws|*4 - |padded_bs|)|;
        |ws|*4 - |padded_bs|;
        ((|padded_bs|+3)/4)*4 - |padded_bs|;
        0;
    }
    assert ghost_padding == [];

    calc {
        |padded_bs|%4;
        |bs + padding|%4;
        (|bs| + |padding|)%4;
        (|bs| + padding_len)%4;
        (|bs| + ws_len*4 - |bs|)%4;
        (ws_len*4)%4;
        0;
    }
    assert BEWordSeqToByteSeq(ws) == padded_bs;

    calc {
        BEWordSeqToByteSeq(ws);
        ghost_padding + padded_bs;
        padded_bs;
        bs + padding;
            { lemma_SequenceOfZeros_is_RepeatDigit(padding_len); }
        bs + RepeatDigit(0, padding_len);
    }
}

static method BEByteSeqToWordSeqTailPadding(bs:seq<int>) returns (ws:seq<int>)
    requires IsByteSeq(bs);
    ensures IsWordSeq(ws);
    ensures |bs| > 0 ==> |ws| > 0;
    ensures |ws| == (|bs| + 3) / 4;
    ensures |bs|*8 <= |BEWordSeqToBitSeq(ws)|;
    ensures BEByteSeqToBitSeq(bs) == BEWordSeqToBitSeq(ws)[..|bs|*8];
    ensures IsByteSeq(TailPad4(bs));
    ensures |TailPad4(bs)|%4==0;
    ensures ws == BEByteSeqToWordSeq(TailPad4(bs));
{
    lemma_2toX();
    var ws_len := (|bs|-1)/4+1;
    var padding_len := ws_len*4 - |bs|;
    var padding := SequenceOfZerosIterative(padding_len);
    var padded_bs := bs + padding;
    ghost var ghost_padding;
    ws,ghost_padding := BEByteSeqToWordSeq_impl(padded_bs);

    lemma_SequenceOfZeros_is_RepeatDigit(padding_len);
    lemma_BEByteSeqToWordSeqTailPadding_more(bs, ws_len, padding_len, padding, padded_bs, ws, ghost_padding);
    lemma_BEByteSeqToWordSeqTailPadding_bit_equivalence(bs, ws, padded_bs, padding, ghost_padding);
    lemma_BEByteSeqToWordSeqTailPadding_constructive_form(ws, bs, padding_len);
}

static method BEByteSeqToWordSeqTailPadding_arrays(ba:array<int>, ghost bs:seq<int>) returns (wa:array<int>, ghost ws:seq<int>)
    requires ba!=null;
    requires ba[..]==bs;
    requires IsByteSeq(bs);
    ensures wa!=null;
    ensures wa[..]==ws;
    ensures IsWordSeq(ws);
    ensures |bs| > 0 ==> |ws| > 0;
    ensures |ws| == (|bs| + 3) / 4;
    ensures |bs|*8 <= |BEWordSeqToBitSeq(ws)|;
    ensures BEByteSeqToBitSeq(bs) == BEWordSeqToBitSeq(ws)[..|bs|*8];
    ensures IsByteSeq(TailPad4(bs));
    ensures |TailPad4(bs)|%4==0;
    ensures ws == BEByteSeqToWordSeq(TailPad4(bs));
{
    lemma_2toX();
    var ws_len := (ba.Length-1)/4+1;
    var padding_len := ws_len*4 - ba.Length;

    ghost var padding := RepeatDigit_premium(0, padding_len);
    ghost var padded_bs := bs + padding;

    var padded_ba := new int[ba.Length + padding_len];
    ArrayCpy(padded_ba, 0, ba, 0, ba.Length);
    calc {
        padded_ba[..ba.Length];
        padded_ba[0..ba.Length];
        ba[0..ba.Length];
        ba[..];
        bs;
    }
    ghost var first_ba_seq := padded_ba[..];
    assert forall k :: 0<=k<ba.Length ==> first_ba_seq[k] == ba[k];
    ArraySet(padded_ba, ba.Length, padding_len, 0);
    assert forall i :: 0<=i<ba.Length ==> padded_ba[i]==first_ba_seq[i];

    Lemma_RepeatDigitProperties(0, padding_len);
    assert |padded_ba[ba.Length..]|==|RepeatDigit_premium(0, padding_len)|;
    assert padded_ba[ba.Length..]==RepeatDigit_premium(0, padding_len);
    
    ghost var ghost_padding;
    assert padded_ba.Length == |padded_ba[..]| == |padded_bs|;
    forall (k | 0<=k<padded_ba.Length)
        ensures padded_ba[..][k]==padded_bs[k];
    {
        if (k < ba.Length)
        {
            calc {
                padded_ba[..][k];
                first_ba_seq[k];
                ba[k];
                padded_bs[k];
            }
        }
        else
        {
            assert padded_ba[..][k]==padded_bs[k];
        }
    }
    assert padded_ba[..] == padded_bs;
    wa,ws,ghost_padding := BEByteSeqToWordSeq_impl_arrays(padded_ba, padded_bs);

    lemma_SequenceOfZeros_is_RepeatDigit(padding_len);
    lemma_BEByteSeqToWordSeqTailPadding_more(bs, ws_len, padding_len, padding, padded_bs, ws, ghost_padding);
    lemma_BEByteSeqToWordSeqTailPadding_bit_equivalence(bs, ws, padded_bs, padding, ghost_padding);
    lemma_BEByteSeqToWordSeqTailPadding_constructive_form(ws, bs, padding_len);
}

static lemma lemma_BEBitSeqToInt_BEWordSeqToBitSeq(ws:seq<int>)
    requires IsWordSeq(ws);
    ensures IsBitSeq(BEWordSeqToBitSeq(ws));
    ensures BEBitSeqToInt(BEWordSeqToBitSeq(ws)) == BEWordSeqToInt(ws);
{
    lemma_BEWordSeqToBitSeq_ensures(ws);
    calc {
        BEBitSeqToInt(BEWordSeqToBitSeq(ws));
        BEBitSeqToInt(BEIntToDigitSeq(power2(1), |ws|*32, BEDigitSeqToInt(power2(32), ws)));
        BEDigitSeqToInt(power2(1), BEIntToDigitSeq(power2(1), |ws|*32, BEDigitSeqToInt(power2(32), ws)));
        { reveal_power2();
          lemma_BEDigitSeqToInt_bound(power2(32), ws);
          lemma_BEIntToDigitSeq_invertibility(power2(1),
                                              BEDigitSeqToInt(power2(32), ws),
                                              BEIntToDigitSeq(power2(1), |ws|*32, BEDigitSeqToInt(power2(32), ws))); }
        BEDigitSeqToInt(power2(32), ws);
        BEWordSeqToInt(ws);
    }
}
