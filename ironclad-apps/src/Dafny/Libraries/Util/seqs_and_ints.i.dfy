include "integer_sequences.s.dfy"
include "seqs_simple.i.dfy"
include "repeat_digit.i.dfy"
include "../Math/div.i.dfy"
include "../Math/power.i.dfy"
include "../Math/power2.i.dfy"

//-////////////////////////////////////////////////////////////////////////////
//- This file establishes properties that relate BEDigitSeqs
//- to their Int interpretation. In particular, it culminates
//- in reasoning about invertibility properties: For example, there's
//- only one byte sequence to represent a given int, and vice versa.

//-////////////////////////////////////////////////////////////////////////////
//- properties about DigitSeqToInt

static lemma lemma_BEDigitSeqToInt_bound(pv:nat, inseq:seq<int>)
    requires 0 < pv;
    requires IsDigitSeq(pv, inseq);
    decreases |inseq|;
    ensures |inseq|>0 ==> inseq[0] * power(pv, |inseq|-1) <= BEDigitSeqToInt(pv, inseq);
    ensures BEDigitSeqToInt(pv, inseq) < power(pv, |inseq|);
    ensures 0 <= BEDigitSeqToInt(pv, inseq);
{
    var result := BEDigitSeqToInt(pv, inseq);
    reveal_BEDigitSeqToInt_private();

    if (inseq==[])
    {
        assert result == 0;
        lemma_power_positive(pv, |inseq|);
    }
    else
    {
        lemma_BEDigitSeqToInt_bound(pv, inseq[0..|inseq|-1]);

        if (|inseq|==1)
        {
            calc {
                inseq[0] * power(pv, |inseq|-1);
                    { lemma_power_0(pv); }
                mul(inseq[0], 1);
                    { lemma_mul_basics_forall(); }
                inseq[0];
                inseq[|inseq|-1];
                    { lemma_mul_basics_forall(); }
                0*pv + inseq[|inseq|-1];
                BEDigitSeqToInt_private(pv, [])*pv + inseq[|inseq|-1];
                BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1])*pv + inseq[|inseq|-1];
                BEDigitSeqToInt_private(pv, inseq);
                BEDigitSeqToInt(pv, inseq);
            }
        }
        else
        {
            calc {
                inseq[0] * power(pv, |inseq|-1);
                    { lemma_power_adds(pv, |inseq|-2, 1); }
                inseq[0] * (power(pv, |inseq|-2) * power(pv,1));
                    { lemma_power_1(pv); }
                inseq[0] * (power(pv, |inseq|-2) * pv);
                    { lemma_mul_is_associative_forall(); }
                (inseq[0] * power(pv, |inseq|-2)) * pv;
                (inseq[0] * power(pv, |inseq[0..|inseq|-1]|-1)) * pv;
                <=
                (inseq[0] * power(pv, |inseq[0..|inseq|-1]|-1)) * pv + inseq[|inseq|-1];
                (inseq[0..|inseq|-1][0] * power(pv, |inseq[0..|inseq|-1]|-1)) * pv + inseq[|inseq|-1];
                <=    {
                        lemma_mul_inequality(inseq[0..|inseq|-1][0] * power(pv, |inseq[0..|inseq|-1]|-1), BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1]), pv);
                    }
                BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1])*pv + inseq[|inseq|-1];
                BEDigitSeqToInt_private(pv, inseq);
                BEDigitSeqToInt(pv, inseq);
            }
        }

        assert 0 <= BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1]);
        calc {
            0;
            <=    { lemma_mul_nonnegative_forall(); }
            pv*BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1]);
                { lemma_mul_is_commutative_forall(); }
            BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1])*pv;
            <= BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1])*pv + inseq[|inseq|-1];
            result;
        }
        calc {
            BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1])+1;
            <=    { lemma_BEDigitSeqToInt_bound(pv, inseq[0..|inseq|-1]); }
            power(pv, |inseq[0..|inseq|-1]|);
            power(pv, |inseq|-1);
        }
        lemma_mul_inequality(
            BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1])+1,
            power(pv, |inseq|-1),
            pv);
        calc {
            result;
            BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1])*pv + inseq[|inseq|-1];
            < BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1])*pv + pv;
                { lemma_mul_basics_forall(); }
            BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1])*pv + mul(1,pv);
                { lemma_mul_is_distributive_forall(); }
            (BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1])+1)*pv;
            <= power(pv, |inseq|-1)*pv;
                { reveal_power(); lemma_mul_is_commutative_forall(); }
            power(pv, |inseq|-1+1);
            power(pv, |inseq|);
        }
    }
}

static lemma lemma_BEIntToDigitSeq_mp_min(pv:int, mp:int, x:int)
    requires 1<pv;
    requires 0<=x;
    decreases mp;
    ensures mp <= |BEIntToDigitSeq_private(pv, mp, x)|;
{
    reveal_BEIntToDigitSeq_private();
    if (mp<=0)
    {
    }
    else
    {
        lemma_div_pos_is_pos(x,pv);
        lemma_BEIntToDigitSeq_mp_min(pv, mp-1, x/pv);
        calc {
            mp;
            <=    { lemma_BEIntToDigitSeq_mp_min(pv, mp-1, x/pv); }
            |BEIntToDigitSeq_private(pv, mp-1, x/pv)|+1;
            |BEIntToDigitSeq_private(pv, mp-1, x/pv) + [x%pv]|;
            |BEIntToDigitSeq_private(pv, mp, x)|;
        }
    }
}

static lemma lemma_BEIntToDigitSeq_zero(pv:int, mp:int)
    requires 1<pv;
    requires 0<=mp;
    ensures |BEIntToDigitSeq_private(pv, mp, 0)| == mp;
    decreases mp;
{
    reveal_BEIntToDigitSeq_private();
    if (mp>0)
    {
        lemma_div_basics_forall();
        lemma_BEIntToDigitSeq_zero(pv, mp-1);
    }
}

static lemma lemma_BEIntToDigitSeq_properties_inner(pv:int, mp:int, x:int)
    requires 1<pv;
    requires 0<=x;
    decreases x;
    ensures mp <= |BEIntToDigitSeq_private(pv, mp, x)|;
    ensures x < power(pv, |BEIntToDigitSeq_private(pv, mp, x)|);
    ensures x>0 ==> 0 < |BEIntToDigitSeq_private(pv, mp, x)|;
    ensures (x>0 && (mp<=0 || power(pv,mp-1)<=x)) ==> power(pv, |BEIntToDigitSeq_private(pv, mp, x)|-1) <= x;
{
    lemma_BEIntToDigitSeq_mp_min(pv, mp, x);

    if (x==0)
    {
        lemma_power_positive(pv, |BEIntToDigitSeq_private(pv, mp, x)|);
    }
    else
    {
        lemma_div_pos_is_pos(x,pv);
        lemma_div_is_strictly_ordered_by_denominator(x,pv);
        calc ==> {
            true;
                { lemma_BEIntToDigitSeq_properties_inner(pv, mp-1, x/pv); }
            x/pv+1 <= power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|);
                { lemma_mul_inequality_forall(); }
            (x/pv+1)*pv <= power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|)*pv;
                { lemma_mul_is_distributive_forall(); }
            (x/pv)*pv+mul(1,pv) <= power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|)*pv;
                { lemma_mul_basics_forall(); }
            (x/pv)*pv + pv <= power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|)*pv;
                { lemma_fundamental_div_mod(x,pv); lemma_mul_is_commutative_forall(); }
            x - x%pv + pv <= power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|)*pv;
        }
        calc {
            x;
            <    { lemma_mod_properties(); }
            x - x%pv + pv;
            <= power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|)*pv;
                { lemma_power_1(pv); }
            power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|)*power(pv, 1);
                { lemma_power_adds(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|, 1); }
            power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|+1);
            power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv) + [x%pv]|);
                { reveal_BEIntToDigitSeq_private(); }
            power(pv, |BEIntToDigitSeq_private(pv, mp, x)|);
        }

        reveal_BEIntToDigitSeq_private();
        assert 0 < |BEIntToDigitSeq_private(pv, mp, x)|;

        if (x>0 && (mp<=0 || power(pv,mp-1)<=x))    //- one more obligation.
        {
            if (x/pv <= 0)    //- can't recurse, case I
            {
                calc ==> {
                    true;
                        { lemma_small_div_converse(); }
                    0<x<pv;
                        {
                            if (mp>1)
                            {
                                calc {
                                    power(pv,mp-1);
                                        { lemma_power_adds(pv,mp-2,1); }
                                    power(pv,mp-2)*power(pv,1);
                                    >= {
                                        lemma_power_positive(pv,1);
                                        lemma_power_positive(pv,mp-2);
                                        lemma_mul_increases(power(pv,mp-2), power(pv,1));
                                    }
                                    power(pv,1);
                                        { lemma_power_1(pv); }
                                    pv;
                                }
                                assert false;
                            }
                        }
                    mp<=1;
                    |BEIntToDigitSeq_private(pv, mp, x)| <= 1;
                    |BEIntToDigitSeq_private(pv, mp, x)|-1 <= 0;
                    |BEIntToDigitSeq_private(pv, mp, x)|-1 == 0;
                        { lemma_power_0(pv); }
                    power(pv, |BEIntToDigitSeq_private(pv, mp, x)|-1) == 1;
                    power(pv, |BEIntToDigitSeq_private(pv, mp, x)|-1) <= x;
                }
            }
            else if (mp-1>0 && power(pv,mp-1-1)>x/pv)    //- can't recurse, case II
            {
                assert power(pv,mp-1)<=x;
                calc ==> {
                    mp>1;
                    power(pv,mp-2) > x/pv;
                        { lemma_div_by_multiple(power(pv,mp-2), pv); }
                    (power(pv,mp-2)*pv)/pv > x/pv;
                        { lemma_power_1(pv); }
                    (power(pv,mp-2)*power(pv,1))/pv > x/pv;
                        { lemma_power_adds(pv,mp-2,1); }
                    power(pv,mp-1)/pv > x/pv;
                        {
                            if (power(pv,mp-1) <= x)
                            {
                                lemma_power_positive(pv,mp-1);
                                lemma_div_is_ordered(power(pv,mp-1), x, pv);
                                assert false;
                            }
                        }
                    power(pv,mp-1) > x;
                    false;
                }
            }
            else    //- can recurse
            {
                assert x/pv > 0 && (mp-1<=0 || power(pv,mp-1-1)<=x/pv);
                assert |BEIntToDigitSeq_private(pv, mp-1, x/pv)|-1 >= 0;

                calc ==> {
                    true;
                        { lemma_BEIntToDigitSeq_properties_inner(pv, mp-1, x/pv); }
                    power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|-1) <= x/pv;

                    power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|-1) <= x/pv;
                        { lemma_mul_inequality_forall(); }
                    power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|-1)*pv <= (x/pv)*pv;
                        { lemma_fundamental_div_mod(x,pv); lemma_mul_is_commutative_forall(); }
                    power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|-1)*pv <= x - x%pv;
                }

                calc {
                    power(pv, |BEIntToDigitSeq_private(pv, mp, x)|-1);
                    power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv) + [x%pv]|-1);
                    power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|);
                    power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|-1+1);
                        { lemma_power_adds(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|-1, 1); }
                    power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|-1)*power(pv,1);
                        { lemma_power_1(pv); }
                    power(pv, |BEIntToDigitSeq_private(pv, mp-1, x/pv)|-1)*pv;
                    <= x - x%pv;
                    <=    { lemma_mod_properties(); }
                    x;
                }
            }
        }
    }
}

static lemma lemma_BEIntToDigitSeq_when_mp_dominates_x(pv:int, mp:int, x:int)
    requires 1<pv;
    requires 0<=mp;
    requires 0<=x<power(pv,mp);
    ensures mp == |BEIntToDigitSeq_private(pv, mp, x)|;
    decreases mp;
{
    reveal_BEIntToDigitSeq_private();
    if (mp==0)
    {
        lemma_power_0(pv);
    }
    else
    {
        calc {
            |BEIntToDigitSeq_private(pv, mp, x)|;
            |BEIntToDigitSeq_private(pv, mp-1, x/pv) + [ x % pv ]|;
            |BEIntToDigitSeq_private(pv, mp-1, x/pv)|+1;
            {
                lemma_div_pos_is_pos(x,pv);
                if (x/pv >= power(pv,mp-1))
                {
                    calc {
                        x;
                        >= { lemma_fundamental_div_mod(x,pv); lemma_mod_properties(); }
                        pv*(x/pv);
                        >=  { lemma_mul_inequality_forall(); lemma_mul_is_commutative_forall(); }   //- and contradiction hypothesis
                        pv*power(pv,mp-1);
                        { reveal_power(); }
                        power(pv,mp);
                    }
                }
                lemma_BEIntToDigitSeq_when_mp_dominates_x(pv, mp-1, x/pv);
            }
            mp-1+1;
            mp;
        }
    }
}

static lemma lemma_BEIntToDigitSeq_properties(pv:int, mp:int, x:int)
    requires 1<pv;
    requires 0<=x;
    decreases x;
    ensures mp <= |BEIntToDigitSeq_private(pv, mp, x)|;
    ensures x < power(pv, |BEIntToDigitSeq_private(pv, mp, x)|);
    ensures x>0 ==> 0 < |BEIntToDigitSeq_private(pv, mp, x)|;
    ensures (x>0 && (mp<=0 || power(pv,mp-1)<=x)) ==> power(pv, |BEIntToDigitSeq_private(pv, mp, x)|-1) <= x;
    ensures (0<=mp && x<power(pv,mp)) ==> mp == |BEIntToDigitSeq_private(pv, mp, x)|;
{
    lemma_BEIntToDigitSeq_properties_inner(pv, mp, x);
    if (0<=mp && x<power(pv,mp))
    {
        lemma_BEIntToDigitSeq_when_mp_dominates_x(pv, mp, x);
    }
}

static lemma lemma_BEIntToDigitSeq_length(pv:int, x:int)
    requires 1<pv;
    requires 1<=x;
    ensures |BEIntToDigitSeq_private(pv, 0, x/pv)|+1 == |BEIntToDigitSeq_private(pv, 0, x)|;
{
    lemma_BEIntToDigitSeq_properties_inner(pv, 0, x);

    assert x < power(pv, |BEIntToDigitSeq_private(pv, 0, x)|);
    assert 0 < |BEIntToDigitSeq_private(pv, 0, x)|;
    assert power(pv, |BEIntToDigitSeq_private(pv, 0, x)|-1) <= x;

    lemma_div_pos_is_pos(x,pv);
    lemma_BEIntToDigitSeq_properties_inner(pv, 0, x/pv);

    assert x/pv < power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|);
    assert x/pv>0 ==> 0 < |BEIntToDigitSeq_private(pv, 0, x/pv)|;
    assert x/pv>0 ==> power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|-1) <= x/pv;

    if (|BEIntToDigitSeq_private(pv, 0, x/pv)|+1 < |BEIntToDigitSeq_private(pv, 0, x)|)
    {
        //- should be able to place a too-low upper bound on x.
        calc ==> {
            true;
                { lemma_BEIntToDigitSeq_properties_inner(pv, 0, x/pv); }
            x/pv < power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|);
            x/pv + 1 <= power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|);
                { lemma_mul_inequality_forall(); lemma_mul_is_commutative_forall(); }
            pv*(x/pv + 1) <= pv*power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|);
                { lemma_mul_is_distributive_forall(); }
            pv*(x/pv) + mul(pv,1) <= pv*power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|);
                { lemma_mul_basics_forall(); }
            pv*(x/pv) + pv <= pv*power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|);
                { lemma_power_1(pv); lemma_power_adds(pv, 1, |BEIntToDigitSeq_private(pv, 0, x/pv)|); }
            pv*(x/pv) + pv <= power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|+1);
                { lemma_mod_properties(); }
            pv*(x/pv) + x%pv < power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|+1);
                { lemma_fundamental_div_mod(x,pv); }
            x < power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|+1);
        }

        calc ==> {
            true;
            |BEIntToDigitSeq_private(pv, 0, x/pv)|+2 <= |BEIntToDigitSeq_private(pv, 0, x)|;
                { lemma_power_increases(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|+1, |BEIntToDigitSeq_private(pv, 0, x)|-1); }
            power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|+1) <= power(pv, |BEIntToDigitSeq_private(pv, 0, x)|-1);
        }

        calc {
            x;
            <
            power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|+1);
            <=
            power(pv, |BEIntToDigitSeq_private(pv, 0, x)|-1);
            <=    { lemma_BEIntToDigitSeq_properties_inner(pv, 0, x); }
            x;
        }
        assert false;
    }
    else if (|BEIntToDigitSeq_private(pv, 0, x/pv)|+1 > |BEIntToDigitSeq_private(pv, 0, x)|)
    {
        //- should be able to place a too-high lower bound on x.
        if (x/pv==0)
        {
            calc {
                1;
                0+1;
                    { reveal_BEIntToDigitSeq_private(); }
                |BEIntToDigitSeq_private(pv, 0, x/pv)|+1;
                >    //- contradiction hypothesis
                |BEIntToDigitSeq_private(pv, 0, x)|;
            }
            assert |BEIntToDigitSeq_private(pv, 0, x)| == 0;
            assert x == 0;
        }
        else
        {
            calc ==> {
                true;
                    { lemma_BEIntToDigitSeq_properties_inner(pv, 0, x/pv); }
                power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|-1) <= x/pv;
                    { lemma_mul_inequality_forall(); lemma_mul_is_commutative_forall(); }
                pv*power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|-1) <= pv*(x/pv);
                    { lemma_mod_properties(); }
                pv*power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|-1) <= pv*(x/pv) + x%pv;
                    { lemma_fundamental_div_mod(x,pv); }
                pv*power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|-1) <= x;
                    { lemma_power_1(pv); lemma_power_adds(pv, 1, |BEIntToDigitSeq_private(pv, 0, x/pv)|-1); }
                power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|) <= x;
            }

            calc ==> {
                true;
                |BEIntToDigitSeq_private(pv, 0, x/pv)| >= |BEIntToDigitSeq_private(pv, 0, x)|;
                    { lemma_power_increases(pv, |BEIntToDigitSeq_private(pv, 0, x)|, |BEIntToDigitSeq_private(pv, 0, x/pv)|); }
                power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|) >= power(pv, |BEIntToDigitSeq_private(pv, 0, x)|);
            }

            calc {
                x;
                <    { lemma_BEIntToDigitSeq_properties_inner(pv, 0, x); }
                pv*power(pv, |BEIntToDigitSeq_private(pv, 0, x)|);
                <=
                pv*power(pv, |BEIntToDigitSeq_private(pv, 0, x/pv)|);
                <= x;
            }
        }
    }
}

static lemma lemma_BEIntToDigitSeq_mp_irrelevant(pv:int, mp:int, x:int)
    requires 1<pv;
    requires 0<=x;
    requires mp <= |BEIntToDigitSeq(pv, 0, x)|;
    decreases x;
    ensures BEIntToDigitSeq(pv, 0, x) == BEIntToDigitSeq(pv, mp, x);
{
    reveal_BEIntToDigitSeq_private();
    if (x==0)
    {
    }
    else
    {
        lemma_div_pos_is_pos(x,pv);
        calc {
            BEIntToDigitSeq(pv, mp, x);
            BEIntToDigitSeq_private(pv, mp, x);
            BEIntToDigitSeq_private(pv, mp-1, x/pv) + [x%pv];
                {
                    lemma_div_is_strictly_ordered_by_denominator(x,pv);
                    if (mp-1 > |BEIntToDigitSeq(pv, 0, x/pv)|)
                    {
                        lemma_BEIntToDigitSeq_length(pv, x);
                        assert false;
                    }
                    lemma_BEIntToDigitSeq_mp_irrelevant(pv, mp-1, x/pv);
                }
            BEIntToDigitSeq_private(pv, 0, x/pv) + [x%pv];
                { lemma_BEIntToDigitSeq_private_unbounded_mp_irrelevant(pv, x/pv, 0, -1); }
            BEIntToDigitSeq_private(pv, -1, x/pv) + [x%pv];
            BEIntToDigitSeq_private(pv, 0, x);
            BEIntToDigitSeq(pv, 0, x);
        }
    }
}

static lemma lemma_BEIntToDigitSeq_shortest_form(pv:int, digitseq:seq<int>, mp:int)
    requires 1<pv;
    requires IsDigitSeq(pv, digitseq);
//-    requires |BEIntToDigitSeq_private(pv, 0, mp)|==0 || BEIntToDigitSeq_private(pv, 0, mp)[0]!=0;
    requires |digitseq|==0 || digitseq[0]!=0;
    requires 0<=mp<=|digitseq|;
    decreases |digitseq|-mp;
    ensures BEIntToDigitSeq(pv, mp, BEDigitSeqToInt(pv, digitseq)) == digitseq;
{
    

    var x := BEDigitSeqToInt(pv, digitseq);
    lemma_BEDigitSeqToInt_bound(pv, digitseq);

    if (mp==|digitseq|)
    {
        lemma_BEDigitSeqToInt_invertibility(pv, x, digitseq);
    }
    else
    {
        assert digitseq[0] != 0;

        if (|BEIntToDigitSeq(pv,0,x)| < |digitseq|)
        {
            assert 0<|digitseq|;
            calc {
                x;
                <    { lemma_BEIntToDigitSeq_properties_inner(pv, 0, x); }
                power(pv, |BEIntToDigitSeq(pv,0,x)|);
                <=    { lemma_power_increases(pv, |BEIntToDigitSeq(pv,0,x)|, |digitseq|-1); }
                power(pv, |digitseq|-1);
                    { lemma_mul_basics_forall(); }
                mul(1,power(pv, |digitseq|-1));
                    //- requires digitseq[0]!=0
                <=    {
                    lemma_power_positive(pv, |digitseq|-1);
                    lemma_mul_inequality(1, digitseq[0], power(pv, |digitseq|-1));
                    lemma_mul_is_commutative_forall();
                }
                digitseq[0] * power(pv, |digitseq|-1);
                <=    { lemma_BEDigitSeqToInt_bound(pv, digitseq); }
                x;
            }
            assert false;
        }

        calc {
            BEIntToDigitSeq(pv, mp, x);
                {
                    assert mp < |digitseq| <= |BEIntToDigitSeq(pv, 0, x)|;
                    lemma_BEIntToDigitSeq_mp_irrelevant(pv, mp, x);
                    lemma_BEIntToDigitSeq_mp_irrelevant(pv, mp+1, x);
                }
            BEIntToDigitSeq(pv, mp+1, x);
                {
                lemma_BEIntToDigitSeq_shortest_form(pv, digitseq, mp+1);
//-                assert x == BEDigitSeqToInt(pv, digitseq);
//-                assert BEIntToDigitSeq(pv, mp+1, x) == digitseq;
//-                assert BEIntToDigitSeq(pv, mp, BEDigitSeqToInt(pv, digitseq)) == digitseq;
                }
            digitseq;
        }
    }
}

//- The converse of this lemma is lemma_BEInt_decoding_general
static lemma lemma_BEDigitSeqToInt_invertibility(pv:int, x:int, digitseq:seq<int>)
    requires 1<pv;
    requires 0<=x;
    requires IsDigitSeq(pv, digitseq);
    requires x == BEDigitSeqToInt(pv, digitseq);
    decreases |digitseq|;
    ensures digitseq == BEIntToDigitSeq(pv, |digitseq|, x);
{
    //- have: xy==DI(0 0 x y) ==> 0 0 x y == ID(4, xy)
    //- have: xyz==DI(0 0 x y z)
    //- have: DI(0 0 x y z) == DI(0 0 x y)*pv + z
    //- have: xyz == xy*pv + z

    //- want: 0 0 x y z == ID(5, xyz)
    //- ID(5, xyz) == ID(4, xyz/pv) + [xyz%pv]
    //- fundamental_div_mod, with: ...?
    //- == ID(4, xy) + [z]
    //- == 0 0 x y + [z]
    //- digitseq

    if (|digitseq|==0)
    {
        reveal_BEDigitSeqToInt_private();
        assert x==0;
        reveal_BEIntToDigitSeq_private();
    }
    else
    {
        calc ==> {
            true;
                { reveal_BEDigitSeqToInt_private(); }
            x == BEDigitSeqToInt_private(pv, digitseq)
                == BEDigitSeqToInt_private(pv, digitseq[0..|digitseq|-1])*pv + digitseq[|digitseq|-1];
                {
                    lemma_BEDigitSeqToInt_bound(pv, digitseq[0..|digitseq|-1]);
                    lemma_fundamental_div_mod_converse(
                        x,
                        pv,
                        BEDigitSeqToInt_private(pv, digitseq[0..|digitseq|-1]),
                        digitseq[|digitseq|-1]); }
            x/pv == BEDigitSeqToInt_private(pv, digitseq[0..|digitseq|-1])
                && x%pv == digitseq[|digitseq|-1];
                {
                    lemma_div_pos_is_pos(x, pv);
//-                    lemma_div_is_strictly_ordered_by_denominator(x, pv);
                    lemma_BEDigitSeqToInt_invertibility(pv, x/pv, digitseq[0..|digitseq|-1]);
                }
            BEIntToDigitSeq(pv, |digitseq|-1, x/pv) == digitseq[0..|digitseq|-1]
                && x%pv == digitseq[|digitseq|-1];
        }

        calc {
            //- ID(5, xyz)
            BEIntToDigitSeq(pv, |digitseq|, x);
                { reveal_BEIntToDigitSeq_private(); }
            //- ID( 4, xyz/pv) + [xyz%pv]
            digitseq[0..|digitseq|-1] + [ digitseq[|digitseq|-1] ];
            digitseq;
        }
    }
}

static lemma lemma_BEDigitSeqToInt_invertibility_tight(pv:int, x:int, digitseq:seq<int>)
    requires 1<pv;
    requires 0<=x;
    requires IsDigitSeq(pv, digitseq);
    requires x == BEDigitSeqToInt(pv, digitseq);
    requires |digitseq|==0 || digitseq[0]>0;
    ensures digitseq == BEIntToDigitSeq(pv, |digitseq|, x);
    ensures digitseq == BEIntToDigitSeq(pv, 0, x);
{
    lemma_BEDigitSeqToInt_invertibility(pv, x, digitseq);
    lemma_BEIntToDigitSeq_shortest_form(pv, digitseq, 0);
}

//-////////////////////////////////////////////////////////////////////////////
//- properties about IntToDigitSeq




static predicate IsZero(sx:seq<int>, xi:int)
    requires 0<=xi<|sx|;
{
    sx[xi]==0
}

static predicate AreEqual(sx:seq<int>, xi:int, sy:seq<int>, yi:int)
    requires 0<=xi<|sx|;
    requires 0<=yi<|sy|;
{
    sx[xi]==sy[yi]
}

static lemma lemma_LeadingZeros(pv:int, short:seq<int>, long:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, short);
    requires IsDigitSeq(pv, long);
    requires |short| <= |long|;
    requires forall i :: 0<=i<|long|-|short| ==> IsZero(long,i);
    requires forall i :: |long|-|short|<=i<|long| ==> AreEqual(long, i, short, i - (|long|-|short|));
    decreases |short|;
    ensures BEDigitSeqToInt(pv, short) == BEDigitSeqToInt(pv, long);
{
    if (|short|==0)
    {
        lemma_BEIntToDigitSeq_private_zero(pv, |short|);
        lemma_BEIntToDigitSeq_invertibility_zero(pv, short);
        lemma_BEIntToDigitSeq_private_zero(pv, |long|);
        
        
        forall (i | 0<=i<|long|)
            ensures long[i]==0;
        {
            assert IsZero(long, i); //- OBSERVE trigger
        }
        assert long == BEIntToDigitSeq_private(pv, |long|, 0);
        lemma_BEIntToDigitSeq_invertibility_zero(pv, long);
    }
    else
    {
        var shortp := short[..|short|-1];
        var longp := long[..|long|-1];
        calc {
            BEDigitSeqToInt(pv, short);
                { reveal_BEDigitSeqToInt_private(); }
            BEDigitSeqToInt_private(pv, short[0..|short|-1])*pv + short[|short|-1];
                { lemma_vacuous_statement_about_a_sequence(short, |short|-1); }
            BEDigitSeqToInt_private(pv, shortp)*pv + short[|short|-1];
            {
                //- Unwrap triggers
                forall (i | 0<=i<|longp|-|shortp|)
                    ensures longp[i]==0;
                {
                    assert IsZero(long, i); //- OBSERVE trigger
                }
                forall (i | |longp|-|shortp|<=i<|longp|)
                    ensures AreEqual(longp, i, shortp, i - (|longp|-|shortp|));
                {
                    assert AreEqual(long, i, short, i - (|long|-|short|)); //- OBSERVE trigger
                }

                lemma_LeadingZeros(pv, shortp, longp);
                assert BEDigitSeqToInt(pv, shortp) == BEDigitSeqToInt(pv, longp);
                assert BEDigitSeqToInt_private(pv, shortp) == BEDigitSeqToInt_private(pv, longp);
//-                calc {
//-                    long[|long|-1];
//-                    long[|long|-1-(|long|-|short|)];
//-                    short[|short|-1];
//-                }
                assert AreEqual(long, |long|-1, short, |long|-1-(|long|-|short|));
                assert short[|short|-1] == long[|long|-1];
            }
            BEDigitSeqToInt_private(pv, longp)*pv + long[|long|-1];
                { lemma_vacuous_statement_about_a_sequence(long, |long|-1); }
            BEDigitSeqToInt_private(pv, long[0..|long|-1])*pv + long[|long|-1];
                { reveal_BEDigitSeqToInt_private(); }
            BEDigitSeqToInt(pv, long);
        }
    }
}

//- the "opposite" of lemma_LeadingZeros; lets us prove properties
//- of the sequence structure when generating extra bits (e.g. converting
//- a Word32 to a 32-bit sequence).
static lemma lemma_zero_extension(pv:int, mp:nat, x:nat, tight:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, tight);
    requires BEIntToDigitSeq(pv, 0, x) == tight;
    requires |tight|<=mp;
    ensures BEIntToDigitSeq(pv, mp, x) == RepeatDigit_premium(0, mp-|tight|) + tight;
    decreases mp;
{
    reveal_BEIntToDigitSeq_private();

    if (x==0)
    {
        assert tight==[];
        if (mp==0)
        {
            calc {
                BEIntToDigitSeq(pv, mp, x);
                [];
                RepeatDigit_premium(0, 0) + [];
                RepeatDigit_premium(0, mp-|tight|) + tight;
            }
        }
        else
        {
            calc {
                BEIntToDigitSeq(pv, mp, x);
                BEIntToDigitSeq(pv, mp, 0);
                BEIntToDigitSeq_private(pv, mp-1, div(0,pv)) + [mod(0,pv)];
                    { lemma_div_basics(pv); lemma_small_mod(0,pv); }
                BEIntToDigitSeq_private(pv, mp-1, 0) + [0];
                    { lemma_zero_extension(pv, mp-1, 0, []); }
                RepeatDigit_premium(0, mp-1) + [] + [0];
                RepeatDigit_premium(0, mp);
                RepeatDigit_premium(0, mp) + [];
            }
        }
    }
    else
    {
        var tight' := BEIntToDigitSeq(pv, 0, x/pv);
        lemma_div_pos_is_pos(x,pv);
        lemma_BEIntToDigitSeq_private_unbounded_mp_irrelevant(pv, x/pv, -1, 0);
        lemma_zero_extension(pv, mp-1, x/pv, tight');
    }
}

static method TrimLeadingZeros(ghost pv:int, M:seq<int>) returns (TM:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, M);
    ensures IsDigitSeq(pv, TM);
    ensures BEDigitSeqToInt(pv, TM) == BEDigitSeqToInt(pv, M);
    ensures |TM|==0 || TM[0]>0;
{
    var ptr:=0;
    assert M[ptr..] == M;
    while (ptr<|M| && M[ptr]==0)
        invariant 0<=ptr<=|M|;
        invariant forall j :: 0<=j<ptr ==> M[j]==0;
        invariant BEDigitSeqToInt(pv, M[ptr..]) == BEDigitSeqToInt(pv, M);
    {
        ptr := ptr + 1;
        lemma_LeadingZeros(pv, M[ptr..], M);
    }
    TM := M[ptr..];
}

static lemma lemma_BEIntToDigitSeq_invertibility(pv:int, x:int, digitseq:seq<int>)
    requires 1<pv;
    requires 0<=x;
    requires IsDigitSeq(pv, digitseq);
    requires digitseq == BEIntToDigitSeq(pv, |digitseq|, x);
    requires IsDigitSeq(pv, digitseq);
//-    requires |digitseq| == |digitseq|;
    decreases x;
    ensures BEDigitSeqToInt(pv, digitseq) == x;
{
    reveal_BEDigitSeqToInt_private();
    reveal_BEIntToDigitSeq_private();

    if (x==0)
    {
        lemma_BEIntToDigitSeq_private_zero(pv, |digitseq|);
        lemma_BEIntToDigitSeq_invertibility_zero(pv, digitseq);
    }
    else
    {
        assert |digitseq|>0;

        var prefix := BEIntToDigitSeq_private(pv, |digitseq|-1, x/pv);
        var tail := [ x % pv ];
        var digits := prefix + tail;
        assert 0<|digits|;

        lemma_div_pos_is_pos(x,pv);
        if (x/pv == 0)
        {
            if (x >= pv)
            {
                lemma_div_basics(pv);
                lemma_div_is_ordered(pv,x,pv);
                assert false;
            }
            assert x < pv;

            var prefix2 := BEIntToDigitSeq(pv, |digitseq|-1, x/pv);
            assert prefix2 == BEIntToDigitSeq(pv, |digitseq|-1, 0);
            lemma_BEIntToDigitSeq_private_zero(pv, |digitseq|-1);
            lemma_BEIntToDigitSeq_invertibility_zero(pv, prefix2);
            assert BEDigitSeqToInt(pv, prefix2) == 0;

            lemma_small_mod(x, pv);
            assert digitseq == prefix2 + [ x ];

            calc {
                BEDigitSeqToInt_private(pv, digitseq);
                BEDigitSeqToInt_private(pv, digitseq[0..|digitseq|-1])*pv + digitseq[|digitseq|-1];
                    { lemma_vacuous_statement_about_a_sequence(digitseq, |digitseq|-1); }
                BEDigitSeqToInt_private(pv, prefix2)*pv + digitseq[|digitseq|-1];
                mul(0,pv) + digitseq[|digitseq|-1];
                    { lemma_mul_basics_forall(); }
                0 + digitseq[|digitseq|-1];
                x;
            }
        }
        else
        {
            assert 0<x/pv;
            calc {
                BEDigitSeqToInt_private(pv, BEIntToDigitSeq_private(pv, |digitseq|-1, x/pv));
                {
                    assert x>0;
                    lemma_div_is_strictly_ordered_by_denominator(x,pv);
                    assert x/pv < x;
                    lemma_BEIntToDigitSeq_invertibility(pv, x/pv, prefix);
                }
                x/pv;
            }
        }

        calc {
            BEDigitSeqToInt(pv, BEIntToDigitSeq(pv, |digitseq|, x));
            BEDigitSeqToInt(pv, BEIntToDigitSeq_private(pv, |digitseq|, x));
    //-            { reveal_BEIntToDigitSeq_private(); }
            BEDigitSeqToInt(pv, BEIntToDigitSeq_private(pv, |digitseq|-1, x/pv) + [ x % pv ]);
            BEDigitSeqToInt(pv, prefix + tail);
            BEDigitSeqToInt(pv, digits);
            BEDigitSeqToInt_private(pv, digits[0..|digits|-1])*pv + digits[|digits|-1];
            {
                calc {
                    digits[0..|digits|-1];
                    BEIntToDigitSeq_private(pv, |digitseq|-1, x/pv);
                }
            }
            BEDigitSeqToInt_private(pv, BEIntToDigitSeq_private(pv, |digitseq|-1, x/pv))*pv + digits[|digits|-1];
            BEDigitSeqToInt_private(pv, BEIntToDigitSeq_private(pv, |digitseq|-1, x/pv))
                *pv
                + (x % pv);
                //- apply calcs proven in previous case analysis
            (x/pv)*pv + (x%pv);
                { lemma_mul_is_commutative_forall(); }
            pv*(x/pv) + (x%pv);
                { lemma_fundamental_div_mod(x,pv); }
            x;
            x;
        }
    }
}

//-////////////////////////////////////////////////////////////////////////////
//- more properties about IntToDigitSeq

static lemma lemma_BEIntToDigitSeq_private_unbounded_mp_irrelevant(pv:int, x:int, mp1:int, mp2:int)
    requires 1<pv;
    requires 0<=x;
    requires mp1<=0;
    requires mp2<=0;
    decreases x;
    ensures BEIntToDigitSeq_private(pv,mp1,x) == BEIntToDigitSeq_private(pv,mp2,x);
{
    forall (mp1,mp2 | mp1<=0 && mp2<=0)
        ensures BEIntToDigitSeq_private(pv,mp1,x) == BEIntToDigitSeq_private(pv,mp2,x);
    {
        reveal_BEIntToDigitSeq_private();
        if (0<x) {
            lemma_div_pos_is_pos(x,pv);
            lemma_div_is_strictly_ordered_by_denominator(x,pv);
            assert 0 <= x/pv < x;
//-            lemma_BEIntToDigitSeq_private_unbounded_mp_irrelevant(pv, x/pv);
            calc {
                BEIntToDigitSeq_private(pv,mp1,x);
                BEIntToDigitSeq_private(pv, mp1-1, x/pv) + [ x % pv ];
                    { lemma_BEIntToDigitSeq_private_unbounded_mp_irrelevant(pv, x/pv, mp1-1, mp2-1); }
                BEIntToDigitSeq_private(pv, mp2-1, x/pv) + [ x % pv ];
                BEIntToDigitSeq_private(pv,mp2,x);
            }
        } else {
        }
    }
}


static lemma lemma_BEIntToDigitSeq_private_unbounded_properties(pv:int, mp:int, x:int)
    decreases x;
    requires 1<pv;
    requires 0<=x;
    requires mp<=0;
    ensures forall i :: 0<=i<|BEIntToDigitSeq_private(pv,mp,x)|
        ==> 0 <= BEIntToDigitSeq_private(pv,mp,x)[i] < pv;
    ensures IsDigitSeq(pv, BEIntToDigitSeq_private(pv,mp,x));
{
    forall (i | 0<=i<|BEIntToDigitSeq_private(pv,mp,x)|)
        ensures 0 <= BEIntToDigitSeq_private(pv,mp,x)[i] < pv;
    {
        reveal_BEIntToDigitSeq_private();
        if (0<x)
        {
            lemma_div_pos_is_pos(x,pv);
            lemma_div_is_strictly_ordered_by_denominator(x,pv);
            assert 0 <= x/pv < x;
            assert |BEIntToDigitSeq_private(pv, mp-1, x/pv)| + 1 == |BEIntToDigitSeq_private(pv,mp,x)|;
            if (i < |BEIntToDigitSeq_private(pv, mp-1, x/pv)|) {
                calc {
                    BEIntToDigitSeq_private(pv,mp,x)[i];
                    (BEIntToDigitSeq_private(pv, mp-1, x/pv) + [ x % pv ])[i];
                    BEIntToDigitSeq_private(pv, mp-1, x/pv)[i];
                }
                lemma_BEIntToDigitSeq_private_unbounded_properties(pv, mp-1, x/pv);
                assert 0 <= BEIntToDigitSeq_private(pv,mp,x)[i] < pv;
            } else {
                calc {
                    BEIntToDigitSeq_private(pv,mp,x)[i];
                    (BEIntToDigitSeq_private(pv, mp-1, x/pv) + [ x % pv ])[i];
                    x % pv;
                }
                lemma_mod_properties();
                assert 0 <= BEIntToDigitSeq_private(pv,mp,x)[i] < pv;
            }
        }
        else
        {
            assert 0 <= BEIntToDigitSeq_private(pv,mp,x)[i] < pv;
        }
    }
}

static lemma lemma_IsDigitSeq_BEIntToDigitSeq(pv:int, mp:int, x:int)
    requires 1<pv;
    requires 0<=x;
    decreases if mp > x then mp else x;
    ensures IsDigitSeq(pv, BEIntToDigitSeq(pv, mp, x));
{
    if (x==0 && mp<=0)
    {
        reveal_BEIntToDigitSeq_private();
        assert BEIntToDigitSeq(pv, mp, x) == [];
        assert IsDigitSeq(pv, BEIntToDigitSeq(pv, mp, x));
    }
    else
    {
        reveal_BEIntToDigitSeq_private();
        lemma_div_pos_is_pos(x,pv);
        if (x>0)
        {
            lemma_div_decreases(x,pv);
            lemma_IsDigitSeq_BEIntToDigitSeq(pv, mp-1, x/pv);
            calc {
                BEIntToDigitSeq(pv, mp, x);
                BEIntToDigitSeq_private(pv, mp-1, x/pv) + [ x % pv ];
            }
            lemma_mod_properties();
        }
        else
        {
            lemma_BEIntToDigitSeq_private_zero(pv, mp);
        }
    }
}

//- The converse of this lemma is lemma_BEDigitSeqToInt_invertibility
static lemma lemma_BEInt_decoding_general(pv:int, mp:int, x:int)
    requires 1<pv;
    requires 0<=x;
    decreases if mp > x then mp else x;
    ensures IsDigitSeq(pv, BEIntToDigitSeq(pv, mp, x));
    ensures BEDigitSeqToInt(pv, BEIntToDigitSeq(pv, mp, x)) == x;
{
    lemma_IsDigitSeq_BEIntToDigitSeq(pv, mp, x);

    if (x==0)
    {
        if (mp<=0)
        {
            calc {
                BEDigitSeqToInt(pv, BEIntToDigitSeq(pv, mp, x));
                    { reveal_BEIntToDigitSeq_private(); }
                BEDigitSeqToInt(pv, []);
                    { reveal_BEDigitSeqToInt_private(); }
                0;
                x;
            }
            assert BEDigitSeqToInt(pv, BEIntToDigitSeq(pv, mp, x)) == x;
        }
        else
        {
            lemma_BEIntToDigitSeq_private_zero(pv, mp);
            lemma_BEIntToDigitSeq_private_zero(pv, mp-1);
            lemma_BEIntToDigitSeq_invertibility_zero(pv, BEIntToDigitSeq(pv, mp, 0));
            lemma_BEIntToDigitSeq_invertibility_zero(pv, BEIntToDigitSeq(pv, mp-1, 0));
        }
    }
    else
    {
        var digits := BEIntToDigitSeq_private(pv, mp-1, x/pv) + [ x % pv ];
        lemma_div_decreases(x,pv);
        lemma_div_pos_is_pos(x,pv);
        lemma_IsDigitSeq_BEIntToDigitSeq(pv, mp-1, x/pv);
        calc {
            BEDigitSeqToInt(pv, BEIntToDigitSeq(pv, mp, x));
                { reveal_BEIntToDigitSeq_private(); }
            BEDigitSeqToInt(pv, digits);
                { reveal_BEDigitSeqToInt_private(); }
            BEDigitSeqToInt_private(pv, digits[0..|digits|-1])*pv + digits[|digits|-1];
                { assert digits[|digits|-1] == x%pv; }
            BEDigitSeqToInt_private(pv, digits[0..|digits|-1])*pv + x%pv;
                { assert digits[0..|digits|-1] == digits[..|digits|-1]; }
            BEDigitSeqToInt_private(pv, digits[..|digits|-1])*pv + x%pv;
            {
                calc {
                    BEDigitSeqToInt_private(pv, digits[..|digits|-1]);
                        { assert BEIntToDigitSeq(pv, mp-1, x/pv) == digits[..|digits|-1]; }
                    BEDigitSeqToInt_private(pv, BEIntToDigitSeq(pv, mp-1, x/pv));
                    BEDigitSeqToInt(pv, BEIntToDigitSeq(pv, mp-1, x/pv));
                        { lemma_BEInt_decoding_general(pv, mp-1, x/pv); }
                    x/pv;
                }
            }
            (x/pv)*pv + x%pv;
                { lemma_mul_is_commutative_forall(); lemma_fundamental_div_mod(x,pv); }
            x;
        }
    }
}


static lemma lemma_BEIntToByteSeq_decoding(x:int)
    requires 0<=x;
    decreases x;
    ensures IsDigitSeq(power2(8), BEIntToByteSeq(x));
    ensures x == BEByteSeqToInt(BEIntToByteSeq(x));
{
    lemma_2toX();
    lemma_BEInt_decoding_general(power2(8), 0, x);
}

static lemma lemma_BEIntToBitSeq_decoding(x:int)
    requires 0<=x;
    decreases x;
    ensures IsDigitSeq(power2(1), BEWordToBitSeq(x));
    ensures x == BEBitSeqToInt(BEWordToBitSeq(x));
{
    reveal_power2();
    lemma_2toX();
    lemma_BEInt_decoding_general(power2(1), 32, x);
}

static lemma lemma_BEIntToDigitSeq_private_form(pv:int, i:int)
    requires 1<pv;
    requires 0<=i;
    decreases i;
    ensures |BEIntToDigitSeq_private(pv, 0, i)|==0 || BEIntToDigitSeq_private(pv, 0, i)[0]!=0;
{
    reveal_BEIntToDigitSeq_private();
    if (0==i)
    {
    }
    else
    {
        lemma_div_pos_is_pos(i,pv);
        lemma_div_is_strictly_ordered_by_denominator(i,pv);
        assert 0 <= i/pv < i;
        calc {
            BEIntToDigitSeq_private(pv, 0, i);
            BEIntToDigitSeq_private(pv, -1, i/pv) + [ i % pv ];
                { lemma_BEIntToDigitSeq_private_unbounded_mp_irrelevant(pv, i/pv, 0, -1); }
            BEIntToDigitSeq_private(pv, 0, i/pv) + [ i % pv ];
        }
        lemma_BEIntToDigitSeq_private_form(pv, i/pv);
        if (i<pv)
        {
            lemma_small_div();
            assert |BEIntToDigitSeq_private(pv, 0, i/pv)|==0;
            assert BEIntToDigitSeq_private(pv, 0, i)[0] == i%pv;
            lemma_mod_is_mod_recursive_forall();
            assert 0 < i%pv;
        }
        else
        {
            lemma_div_is_ordered(pv, i, pv);
            lemma_div_basics(pv);
            assert 0<i/pv;
        }
    }
}

static lemma lemma_BEIntToByteSeq_form(i:int)
    requires 0<=i;
    //-ensures BEIntToByteSeq(i)!=NSeqInt_n();
    ensures |BEIntToByteSeq(i)|==0 || BEIntToByteSeq(i)[0]!=0;
{
    lemma_2toX();
    reveal_BEIntToDigitSeq_private();
    lemma_BEIntToDigitSeq_private_form(256, i);
}

static lemma lemma_BEWordSeqToInt_bound(inseq:seq<int>)
    requires IsWordSeq(inseq);
    ensures 0 <= BEWordSeqToInt(inseq);
    ensures BEWordSeqToInt(inseq) < power2(32*|inseq|);
{
    lemma_BEDigitSeqToInt_bound(power2(32), inseq);
    calc {
        BEWordSeqToInt(inseq);
        <
        power(power2(32), |inseq|);
            { lemma_power2_is_power_2(32); }
        power(power(2,32), |inseq|);
            { lemma_power_multiplies(2,32,|inseq|); }
        //-[dafnycc] power(2,mul(32, |inseq|));
            { lemma_power2_is_power_2(mul(32, |inseq|)); }
        power2(mul(32, |inseq|));
            { lemma_mul_is_mul_boogie(32, |inseq|); }
        power2(32*|inseq|);
    }
}

static lemma lemma_BEByteSeqToInt_bound(inseq:seq<int>)
    requires IsByteSeq(inseq);
    ensures 0 <= BEByteSeqToInt(inseq);
    ensures BEByteSeqToInt(inseq) < power2(8*|inseq|);
{
    lemma_BEDigitSeqToInt_bound(power2(8), inseq);
    calc {
        BEByteSeqToInt(inseq);
        <
        power(power2(8), |inseq|);
            { lemma_power2_is_power_2(8); }
        power(power(2,8), |inseq|);
            { lemma_power_multiplies(2,8,|inseq|); }
        //-[dafnycc] power(2,mul(8, |inseq|));
            { lemma_power2_is_power_2(mul(8, |inseq|)); }
        power2(mul(8, |inseq|));
            { lemma_mul_is_mul_boogie(8, |inseq|); }
        power2(8*|inseq|);
    }
}

static lemma lemma_BEDigitSeq_extract(pv:int, inseq:seq<int>, i:nat)
    requires 1<pv;
    requires IsDigitSeq(pv, inseq);
    requires i < |inseq|;
    ensures 0<power(pv,i);
    ensures inseq[|inseq|-1-i] == (BEDigitSeqToInt(pv, inseq) / power(pv,i)) % pv;
    decreases i;
{
    lemma_power_positive(pv,i);
    reveal_BEDigitSeqToInt_private();
    if (i==0)
    {
        lemma_power_0(pv);
        assert power(pv,i)==1;
        calc {
            (BEDigitSeqToInt(pv, inseq) / power(pv,i)) % pv;
                { lemma_div_is_div_boogie(BEDigitSeqToInt(pv, inseq), 1); }
            (BEDigitSeqToInt(pv, inseq) / 1) % pv;
            (BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1])*pv + inseq[|inseq|-1]) % pv;
                { lemma_mod_multiples_vanish(BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1]), inseq[|inseq|-1], pv);
                  lemma_mul_is_commutative_forall(); }
            (inseq[|inseq|-1]) % pv;
                { lemma_small_mod(inseq[|inseq|-1], pv); }
            inseq[|inseq|-1];
            }
    }
    else
    {
        lemma_power_positive(pv, i-1);
        
        
        
        
        lemma_BEDigitSeqToInt_bound(pv, inseq);

        calc {
            (BEDigitSeqToInt(pv, inseq) / power(pv,i)) % pv;
                { reveal_power(); }
            (BEDigitSeqToInt(pv, inseq) / (pv*power(pv,i-1))) % pv;
                { lemma_div_denominator(BEDigitSeqToInt(pv, inseq), pv, power(pv,i-1)); }
            ((BEDigitSeqToInt(pv, inseq)/pv)/power(pv,i-1)) % pv;
            (((BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1])*pv + inseq[|inseq|-1])/pv)/power(pv,i-1)) % pv;
            { 
                lemma_div_multiples_vanish_fancy(
                    BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1]),
                    inseq[|inseq|-1],
                    pv);
                lemma_mul_is_commutative_forall();
            }
            ((BEDigitSeqToInt_private(pv, inseq[0..|inseq|-1]))/power(pv,i-1)) % pv;
                { assert inseq[0..|inseq|-1] == inseq[..|inseq|-1]; }
            ((BEDigitSeqToInt_private(pv, inseq[..|inseq|-1]))/power(pv,i-1)) % pv;
            (BEDigitSeqToInt(pv, (inseq[..|inseq|-1])) / power(pv,(i-1))) % pv;
                { lemma_BEDigitSeq_extract(pv, inseq[..|inseq|-1], i-1); }
            (inseq[..|inseq|-1])[|(inseq[..|inseq|-1])|-1-(i-1)];

            inseq[|inseq|-1-i];
        }
    }
}

static lemma lemma_BEWordSeq_extract(inseq:seq<int>, i:nat)
    requires IsWordSeq(inseq);
    requires i < |inseq|;
    ensures inseq[|inseq|-1-i] == (BEWordSeqToInt(inseq) / power2(32*i)) % power2(32);
{
    lemma_2toX();
    lemma_BEDigitSeq_extract(power2(32), inseq, i);
    calc {
        power(power2(32),i);
            { lemma_power2_is_power_2(32); }
        power(power(2,32),i);
            { lemma_power_multiplies(2,32,i); }
        //-[dafnycc] power(2,mul(32,i));
            { lemma_power2_is_power_2(mul(32,i)); }
        power2(mul(32,i));
            { lemma_mul_is_mul_boogie(32,i); }
        power2(32*i);
    }
}


//-static lemma lemma_BEDigitSeqToInt_lower_bound(pv:nat, inseq:seq<int>, i:nat)
//-    requires 0 < pv;
//-    requires IsDigitSeq(pv, inseq);
//-    requires i<|inseq|;
//-    ensures inseq[|inseq|-1-i] * power(pv, i) <= BEDigitSeqToInt(pv, inseq);
//-    decreases |inseq|;
