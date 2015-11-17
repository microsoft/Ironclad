include "FatNatDivDefs.i.dfy"
include "FatNatDivEstTrivial.i.dfy"
include "Bitwise.i.dfy"
include "WordBoundHack.i.dfy"

method FNDivision_Estimate_Q_div32(n:array<int>, dv:array<int>) returns (q:array<int>)
    requires n!=null;
    requires IsWordSeq(n[..]);
    requires dv!=null;
    requires IsWordSeq(dv[..]);
    requires 1 < BEWordSeqToInt(dv[..]) <= BEWordSeqToInt(n[..]);
    ensures q!=null;
    ensures IsWordSeq(q[..]);
    ensures 0 < BEWordSeqToInt(q[..])*BEWordSeqToInt(dv[..]);
    ensures BEWordSeqToInt(q[..])*BEWordSeqToInt(dv[..]) <= BEWordSeqToInt(n[..]);
{
    lemma_2toX32();
    ghost var Ns := n[..];
    ghost var Nv := BEWordSeqToInt(Ns);
    ghost var Divs := dv[..];
    ghost var Divv := BEWordSeqToInt(Divs);

    var n_approx,n_approx_exp := TakeTopBits(n, 32);
    assert n_approx == Nv / power2(n_approx_exp);
    assert 0 < BEWordSeqToInt(dv[..]);
    var div_approx,div_approx_exp := TakeTopBits(dv, 16);
    assert div_approx == Divv / power2(div_approx_exp);
        //- this step is redundant, since dv never changes.
        
    
    var div_approx_conservative := div_approx + 1;

    var q_approx,r_discard :=
        Divide32(n_approx,div_approx_conservative);
    lemma_fundamental_div_mod_converse(n_approx,div_approx_conservative,q_approx,r_discard);
    assert q_approx == n_approx/div_approx_conservative;
    
    lemma_power_0(power2(32));
    lemma_mul_basics_forall();
    if (q_approx == 0)
    {
        //- this should only occur when n and d are very close
        //- (and hence n_approx_exp==d_approx_expr==0);
        //- otherwise, TakeBits(n) should be able to find more
        //- bits of n.
        
        
        
        
        
        
        
        q := FNDivision_Estimate_Q_trivial(n,dv);
        return;
    }

    calc {
        Divv;
            { lemma_fundamental_div_mod(Divv, power2(div_approx_exp)); }
        power2(div_approx_exp)*(Divv/power2(div_approx_exp))+Divv%power2(div_approx_exp);
        <=  { lemma_mod_properties(); }
        power2(div_approx_exp)*(Divv/power2(div_approx_exp))+power2(div_approx_exp);
            { lemma_mul_is_distributive_add(power2(div_approx_exp), Divv/power2(div_approx_exp), 1); }
        power2(div_approx_exp)*(Divv/power2(div_approx_exp)+1);
        power2(div_approx_exp)*(div_approx+1);
        power2(div_approx_exp)*(div_approx_conservative);
    }
    calc {
        n_approx*power2(n_approx_exp);
            { lemma_mul_is_commutative(n_approx, power2(n_approx_exp)); }
        power2(n_approx_exp)*n_approx;
        power2(n_approx_exp)*(Nv/power2(n_approx_exp));
        <=  { lemma_mod_properties(); }
        power2(n_approx_exp)*(Nv/power2(n_approx_exp))+Nv%power2(n_approx_exp);
            { lemma_fundamental_div_mod(Nv, power2(n_approx_exp)); }
        Nv;
    }

    if (n_approx_exp >= div_approx_exp) {
        //- common case: n much bigger than d
        var q_approx_exp := n_approx_exp - div_approx_exp;

        var q_approx_ary := new int[1];
        q_approx_ary[0] := q_approx;
        ghost var Qas := q_approx_ary[..];
        ghost var Qav := BEWordSeqToInt(Qas);
        reveal_BEDigitSeqToInt_private();
        calc {
            Qav;
            BEWordSeqToInt(Qas[0..|Qas|-1])*power(power2(32),0)+Qas[|Qas|-1];
            BEWordSeqToInt([])*power(power2(32),0)+Qas[|Qas|-1];
            mul(0,power(power2(32),0))+Qas[|Qas|-1];
            Qas[|Qas|-1];
            q_approx;
        }

        constrain_word_from_overflowing(q_approx_exp);
//-        if (power2(32)<=q_approx_exp)
//-        {
//-            calc {
//-                power2(power2(32));
//-                <= { lemma_power2_increases(power2(32), n_approx_exp); }
//-                power2(n_approx_exp);
//-                <= { lemma_mul_increases(n_approx, power2(n_approx_exp)); }
//-                n_approx*power2(n_approx_exp);
//-                <=
//-                BEDigitSeqToInt(power2(32), Ns);
//-                <  { lemma_BEDigitSeqToInt_bound(power2(32), Ns); }
//-                power(power2(32),|Ns|);
//-                    { lemma_power2_unfolding(32, |Ns|);
//-                      lemma_mul_is_mul_boogie(32, |Ns|); }
//-                power2(32*|Ns|);
//-                <=  { lemma_power2_increases(32*|Ns|, 32*power2(27)); }
//-                power2(32*power2(27));
//-                    { lemma_2toX32(); lemma_mul_is_mul_boogie(32, power2(27)); }
//-                power2(power2(5)*power2(27));
//-                    { lemma_power2_adds(5, 27); }
//-                power2(power2(32));
//-            }
//-            assert false;
//-        }

        assert IsWord(q_approx_exp);
        q := BitShiftLeft_Array(q_approx_ary, q_approx_exp);
        ghost var Qs := q[..];
        ghost var Qv := BEWordSeqToInt(Qs);
        assert Qv == Qav * power2(q_approx_exp);

        assert 0 < q_approx;
        lemma_BEDigitSeqToInt_bound(power2(32), Qas);
        lemma_power2_positive();
        lemma_mul_strictly_positive(BEWordSeqToInt(Qas), power2(q_approx_exp));

        assert 0 < Qv;
        assert 0 < Divv;
        lemma_mul_strictly_positive(Qv,Divv);
        assert 0 < Qv*Divv;

        assert 0 < div_approx_conservative;
        assert 0 < power2(div_approx_exp);
        lemma_mul_strictly_positive(div_approx_conservative, power2(div_approx_exp));
        calc {
            Qv;
            Qav * power2(q_approx_exp);
            q_approx * power2(q_approx_exp);
            (n_approx/div_approx_conservative)*power2(q_approx_exp);
            <= { lemma_mul_is_commutative(power2(q_approx_exp), n_approx/div_approx_conservative);
                 lemma_mul_hoist_inequality(power2(q_approx_exp), n_approx, div_approx_conservative);
                 lemma_mul_is_commutative(n_approx, power2(q_approx_exp)); }
            (n_approx*power2(q_approx_exp))/div_approx_conservative;
                { lemma_mul_nonnegative(n_approx, power2(q_approx_exp));
                  lemma_div_multiples_vanish_quotient(power2(div_approx_exp), n_approx*power2(q_approx_exp), div_approx_conservative); }
            (power2(div_approx_exp)*(n_approx*power2(q_approx_exp)))
                /(power2(div_approx_exp)*div_approx_conservative);    // Commute
            (n_approx*power2(q_approx_exp)*power2(div_approx_exp))
                /(power2(div_approx_exp)*div_approx_conservative);    // Commute 
            (n_approx*power2(q_approx_exp)*power2(div_approx_exp))
                /(div_approx_conservative*power2(div_approx_exp));
                { lemma_mul_is_associative(n_approx, power2(q_approx_exp), power2(div_approx_exp));
                  lemma_power2_adds(q_approx_exp,div_approx_exp); }
            (n_approx*power2(n_approx_exp))
                /(div_approx_conservative*power2(div_approx_exp));
            <= { lemma_div_is_ordered(n_approx*power2(n_approx_exp), Nv, div_approx_conservative*power2(div_approx_exp)); }
            Nv / (div_approx_conservative*power2(div_approx_exp));
            <= {
                lemma_mul_is_commutative(div_approx_conservative, power2(div_approx_exp));
                lemma_div_is_ordered_by_denominator(Nv, Divv, div_approx_conservative*power2(div_approx_exp)); }
            Nv / Divv;
        }
        calc {
            BEWordSeqToInt(Qs)*BEWordSeqToInt(Divs);
            Qv * Divv;
            <=  { lemma_mul_inequality(Qv, Nv / Divv, Divv);
                  lemma_mul_is_commutative(Nv / Divv, Divv); }
            Divv * (Nv / Divv);
            <=  { lemma_mul_hoist_inequality(Divv, Nv, Divv); }
            (Divv * Nv) / Divv;
                { lemma_mul_is_commutative(Divv, Nv);
                  lemma_div_multiples_vanish(Nv, Divv); }
            Nv;
            BEWordSeqToInt(Ns);
        }
        return;
    }

    //- n very nearly d; negative exponent implies some bits
    //- of result are actually describing the remainder, not the quotient.
    lemma_word32(q_approx);
    var neg_exp := div_approx_exp - n_approx_exp;
    assert 0 <= neg_exp;

    
    
    if (neg_exp >= 32)  //- contradiction
    {
        calc {
            Nv;
                { lemma_fundamental_div_mod(Nv, power2(n_approx_exp)); }
            power2(n_approx_exp) * (Nv / power2(n_approx_exp))
                + Nv % power2(n_approx_exp);
            <=  { lemma_mod_properties(); }
            power2(n_approx_exp) * (Nv / power2(n_approx_exp))
                + power2(n_approx_exp);
            power2(n_approx_exp) * n_approx
                + mul(power2(n_approx_exp),1);
                { lemma_mul_is_distributive(power2(n_approx_exp), n_approx, 1); }
            power2(n_approx_exp) * (n_approx + 1);
            <=  { lemma_mul_inequality(n_approx + 1, power2(32), power2(n_approx_exp));
                  lemma_mul_is_commutative(power2(n_approx_exp), n_approx + 1);
                  lemma_mul_is_commutative(power2(n_approx_exp), power2(32)); }
            power2(n_approx_exp) * power2(32);
                { lemma_power2_adds(n_approx_exp, 32); }
            power2(n_approx_exp + 32);
            <=  { lemma_power2_increases(n_approx_exp+32, div_approx_exp); }
            power2(div_approx_exp);
            <   { lemma_mul_strictly_increases(
                    (Divv / power2(div_approx_exp)),
                    power2(div_approx_exp));
                  assert 1 < (Divv / power2(div_approx_exp));
                  assert 0 < power2(div_approx_exp);
                }
            (Divv / power2(div_approx_exp)) * power2(div_approx_exp);
                { lemma_mul_is_commutative(power2(div_approx_exp), Divv / power2(div_approx_exp)); }
            power2(div_approx_exp) * (Divv / power2(div_approx_exp));
            <=  { lemma_mul_hoist_inequality(power2(div_approx_exp), Divv, power2(div_approx_exp)); }
            (power2(div_approx_exp) * Divv) / power2(div_approx_exp);
                { lemma_div_multiples_vanish(Divv, power2(div_approx_exp)); }
            Divv;
        }
        assert false;
    }

    assert 0 < div_approx_exp;

    var q_approx_scaled := BitShiftRight_Word(q_approx, neg_exp);
    assert q_approx_scaled == q_approx / power2(neg_exp);

    if (q_approx_scaled == 0)
    {
        
        q := FNDivision_Estimate_Q_trivial(n,dv);
        return;
    }

    lemma_word32(q_approx_scaled);
    q := new int[1];
    q[0] := q_approx_scaled;
    ghost var Qs := q[..];
    ghost var Qv := BEWordSeqToInt(Qs);

    assert Qs == [q_approx_scaled]; //- OBSERVE
    lemma_BEDigitSeqToInt_singleton(power2(32), q_approx_scaled);
    assert Qv == q_approx_scaled;

    lemma_mul_strictly_positive(Qv, Divv);
    assert 0 < BEWordSeqToInt(Qs)*BEWordSeqToInt(Divs);

    calc {
        Qv * Divv;
        <=  { lemma_mul_is_commutative(Qv, Divv);
              lemma_mul_is_associative(Qv, power2(div_approx_exp), div_approx_conservative);
              lemma_mul_is_commutative(Qv, power2(div_approx_exp) * div_approx_conservative);
              lemma_mul_inequality(Divv, power2(div_approx_exp)*div_approx_conservative, Qv); }
        Qv * power2(div_approx_exp) * div_approx_conservative;
            { lemma_power2_adds(n_approx_exp, neg_exp);
              lemma_mul_is_associative(Qv, power2(n_approx_exp), power2(neg_exp)); }
        Qv * power2(n_approx_exp) * power2(neg_exp) * div_approx_conservative;
        (q_approx / power2(neg_exp)) * power2(n_approx_exp) * power2(neg_exp) * div_approx_conservative;
            { lemma_mul_is_associative(q_approx / power2(neg_exp), power2(n_approx_exp), power2(neg_exp)); }
        (q_approx / power2(neg_exp)) * (power2(n_approx_exp) * power2(neg_exp)) * div_approx_conservative;
            { lemma_mul_is_commutative(power2(n_approx_exp), power2(neg_exp)); }
        (q_approx / power2(neg_exp)) * (power2(neg_exp) * power2(n_approx_exp)) * div_approx_conservative;
            { lemma_mul_is_associative(q_approx / power2(neg_exp), power2(neg_exp), power2(n_approx_exp)); }
        (q_approx / power2(neg_exp)) * power2(neg_exp) * power2(n_approx_exp) * div_approx_conservative;
            { lemma_mul_is_commutative(q_approx / power2(neg_exp), power2(neg_exp)); }
        power2(neg_exp) * (q_approx / power2(neg_exp)) * power2(n_approx_exp) * div_approx_conservative;
        { lemma_mul_is_associative(power2(neg_exp) * (q_approx / power2(neg_exp)), power2(n_approx_exp), div_approx_conservative); }
        power2(neg_exp) * (q_approx / power2(neg_exp)) * (power2(n_approx_exp) * div_approx_conservative);
        <=  { lemma_fundamental_div_mod(q_approx, power2(neg_exp));
              lemma_mod_properties();
              lemma_mul_nonnegative(power2(n_approx_exp), div_approx_conservative);
              lemma_mul_inequality(
                power2(neg_exp) * (q_approx / power2(neg_exp)),
                q_approx,
                (power2(n_approx_exp) * div_approx_conservative)); }
        q_approx * (power2(n_approx_exp) * div_approx_conservative);
            { lemma_mul_is_commutative(power2(n_approx_exp), div_approx_conservative);
              lemma_mul_is_associative(q_approx, div_approx_conservative, power2(n_approx_exp)); }
        q_approx * div_approx_conservative * power2(n_approx_exp);
        <= {
          calc {
            q_approx * div_approx_conservative;
                { lemma_mul_is_commutative(q_approx, div_approx_conservative); }
            div_approx_conservative * (n_approx / div_approx_conservative);
            <=  { lemma_mul_hoist_inequality(div_approx_conservative, n_approx, div_approx_conservative); }
            (div_approx_conservative * n_approx) / div_approx_conservative;
                { lemma_div_multiples_vanish(n_approx, div_approx_conservative); }
            n_approx;
          }
          lemma_mul_inequality_forall();
        }
        n_approx * power2(n_approx_exp);
        <=
        Nv;
    }
    assert BEWordSeqToInt(Qs)*BEWordSeqToInt(Divs) <= BEWordSeqToInt(n[..]);
}

