include "FleetNatAdd.i.dfy"

//- mpi_mul_hlp uses 16/8/1 unrolling and muladdc and optionally a special MULADDC_HUIT instruction
//- then it propagates the carries out.
//- s is the source value, d is the dest value (shifted with pointer math), b is the single
//- limb being multiplied in.
//- mpi_mul_mpi counts up the zeros and preallocates i+j, since that's actually precise.
// Noice.
// The contents of X is always discarded, so all we could possibly save is an allocation.
// Let's ignore that option for now.

lemma lemma_FleetNatMul_one_element(pv:int, newcj:int, carry:int, aj:int, bv:int, lastcj:int, lastcarry:int,
        mlo:int, mhi:int, add1:int, carry1:int, carry2:int)
    requires pv==power2(32);
    requires Word32(newcj);
    requires Word32(carry);
    requires Word32(aj);
    requires Word32(bv);
    requires Word32(lastcj);
    requires Word32(lastcarry);
    requires mhi == (aj * bv) / 0x100000000;
    requires mlo == mod0x100000000(aj * bv);
    requires add1 == mod0x100000000(mlo + lastcarry);
    requires carry1 == if add1 < lastcarry then 1 else 0;
    requires newcj == mod0x100000000(mod0x100000000(mlo + lastcarry) + lastcj);
    requires carry2 == if mod0x100000000(mlo + lastcarry) + lastcj >= 0x100000000 then 1 else 0;
    requires carry == mod0x100000000(mhi + carry1 + carry2);

    ensures newcj + carry*pv == aj * bv + lastcj + lastcarry;
{   
    lemma_2toX();

    calc {
        0;
        <= { lemma_mul_nonnegative_forall(); }
        aj * bv;
    }
    
    // Strip off Boogie-level definitions
    lemma_mod0x100000000(aj * bv);
    assert mlo == (aj * bv) % 0x100000000;
    lemma_mod0x100000000(mlo + lastcarry);
    assert add1 == (mlo + lastcarry) % 0x100000000;
    lemma_mod0x100000000(((mlo + lastcarry) % 0x100000000) + lastcj);
    assert newcj == (((mlo + lastcarry) % 0x100000000) + lastcj) % 0x100000000;

    var product := aj * bv;
    calc {
        product;
        { lemma_fundamental_div_mod(product, pv); }
        pv * (product / pv) + (product % pv);
        pv * mhi + mlo;
    }
    assert product == pv * mhi + mlo;

    calc {
        mlo + lastcarry;
            { lemma_word32(mlo);
              lemma_word32(lastcarry);
              lemma_word32(add1);
              lemma_asm_Add_properties(mlo, lastcarry, add1, carry1); }
        carry1 * pv + add1;
    }

    calc {
        add1 + lastcj;
          { lemma_word32(add1);
            lemma_word32(lastcj);
            lemma_word32(newcj);
            lemma_asm_Add_properties(add1, lastcj, newcj, carry2); }
        carry2 * pv + newcj;
    }

    var untruncated_carry := mhi + carry1 + carry2;
    calc {
        untruncated_carry * pv;
        (mhi + carry1 + carry2) * pv;
        { lemma_mul_is_distributive_forall(); }
        mhi * pv + carry1 * pv + carry2 * pv;
        mhi * pv + (mlo + lastcarry - add1) + carry2*pv;
        mhi * pv + (mlo + lastcarry - add1) + (add1 + lastcj - newcj);
        mhi * pv + mlo + lastcarry + lastcj - newcj;
    }

    calc {
        newcj + untruncated_carry * pv;
        mhi * pv + mlo + lastcarry + lastcj;
        { lemma_mul_is_commutative_forall(); }
        product + lastcarry + lastcj;
    }

    if (untruncated_carry >= pv) {
        calc {
            newcj + untruncated_carry * pv;
            product + lastcarry + lastcj;
            <= calc {
                    product;
                    aj*bv;
                    <= { lemma_mul_upper_bound(aj, pv - 1, bv, pv - 1); }
                    (pv - 1)*(pv - 1);
                }
            (pv-1)*(pv-1) + pv - 1 + pv - 1;
            pv*pv - 2*pv + 1 + pv - 1 + pv - 1;
            pv*pv - 1;
            <
            pv * pv;
        }
        assert untruncated_carry * pv >= pv * pv;
    }
    assert untruncated_carry < pv;
    lemma_div_pos_is_pos(product, pv);
    assert 0 <= untruncated_carry;
    lemma_small_mod(untruncated_carry, pv);
    lemma_mod0x100000000(untruncated_carry);
    assert mod0x100000000(untruncated_carry) == untruncated_carry;
}


lemma lemma_FleetNatMul_one_partial_sum_induction(pv:int,
    oldcs:seq<int>, lastcs:seq<int>, cs:seq<int>, asq:seq<int>, adigits:int,
    bi:int, bv:int, j:int, lastj:int, carry:int, lastcarry:int,
    lastcj:int, newcj:int)
    requires pv==power2(32);
    requires IsWordSeq(cs);
    requires IsWordSeq(oldcs);
    requires IsWordSeq(lastcs);
    requires IsWordSeq(asq);
    requires |cs|==|lastcs|==|oldcs|;
    requires forall i :: 0<=i<|cs| && i!=|cs|-1-(lastj+bi) ==> lastcs[i]==cs[i];
    requires lastj+1 == j <= adigits <= |asq|;
    requires 0 <= lastj;
    requires 0 <= bi;
    requires lastj+bi < |cs|;
    //- element operation components
    requires lastcj == DigitAt(lastcs, lastj+bi);
    requires newcj == DigitAt(cs, lastj+bi);
    requires newcj + carry*pv == DigitAt(asq, lastj) * bv + lastcj + lastcarry;
    requires 0<=carry<pv;
    //- loop invariants
    requires BEWordSeqToInt(lastcs) + lastcarry*power(pv, lastj+bi)
        == BEWordSeqToInt(oldcs)
         + BEWordSeqToInt(SelectDigitRange(asq, lastj, 0)) * bv * power(pv, bi);
    ensures BEWordSeqToInt(cs) + carry*power(pv, j+bi)
        == BEWordSeqToInt(oldcs)
         + BEWordSeqToInt(SelectDigitRange(asq, j, 0)) * bv * power(pv, bi);
{
    assert SelectDigitRange(lastcs, |lastcs|, j+bi) == SelectDigitRange(cs, |cs|, j+bi);    //- OBSERVE SEQ
    assert SelectDigitRange(lastcs, lastj+bi, 0) == SelectDigitRange(cs, lastj+bi, 0);  //- OBSERVE SEQ
    calc {
        BEWordSeqToInt(lastcs);
            { lemma_PluckDigit(cs, lastj+bi);
              lemma_PluckDigit(lastcs, lastj+bi); }
        BEWordSeqToInt(cs)
         - DigitAt(cs, lastj+bi) * power(pv, lastj+bi)
         + DigitAt(lastcs, lastj+bi) * power(pv, lastj+bi);
    }
    
    var aj := DigitAt(asq, lastj);

    calc {
        BEWordSeqToInt(oldcs)
         + BEWordSeqToInt(SelectDigitRange(asq, j, 0)) * bv * power(pv, bi);
            { lemma_mul_is_associative_forall(); }
        BEWordSeqToInt(oldcs)
         + BEWordSeqToInt(SelectDigitRange(asq, j, 0)) * (bv * power(pv, bi));
            { lemma_PluckDigit_general(asq, j, lastj, 0); }
        BEWordSeqToInt(oldcs) + (
          BEWordSeqToInt(SelectDigitRange(asq, j, j)) * power(pv, j)
          + aj * power(pv, lastj)
          + BEWordSeqToInt(SelectDigitRange(asq, lastj, 0))
         )* (bv * power(pv, bi));
            { assert SelectDigitRange(asq, j, j)==[]; //- OBSERVE SEQ
              reveal_BEDigitSeqToInt_private(); }
        BEWordSeqToInt(oldcs) + (
          aj * power(pv, lastj)
          + BEWordSeqToInt(SelectDigitRange(asq, lastj, 0))
         )* (bv * power(pv, bi));
            { lemma_mul_is_distributive_forall(); }
        aj * power(pv, lastj)* (bv * power(pv, bi))
          + BEWordSeqToInt(oldcs)
          + BEWordSeqToInt(SelectDigitRange(asq, lastj, 0))* (bv * power(pv, bi));
            { lemma_mul_is_associative_forall(); } //- apply partial sum hypothesis
        aj * power(pv, lastj)* (bv * power(pv, bi))
            + BEWordSeqToInt(lastcs) + lastcarry*power(pv, lastj+bi);
            //- earlier calc
        aj * power(pv, lastj)* (bv * power(pv, bi))
            + BEWordSeqToInt(cs)
            - DigitAt(cs, lastj+bi) * power(pv, lastj+bi)
            + DigitAt(lastcs, lastj+bi) * power(pv, lastj+bi)
            + lastcarry*power(pv, lastj+bi);
            { lemma_mul_is_associative_forall(); lemma_power_adds(pv, lastj, bi); }
        aj * bv * power(pv, lastj + bi)
            + BEWordSeqToInt(cs)
            - DigitAt(cs, lastj+bi) * power(pv, lastj+bi)
            + DigitAt(lastcs, lastj+bi) * power(pv, lastj+bi)
            + lastcarry*power(pv, lastj+bi);
            { lemma_mul_is_distributive_forall(); }
        (aj * bv - DigitAt(cs, lastj+bi) + DigitAt(lastcs, lastj+bi) + lastcarry)
                * power(pv, lastj + bi)
            + BEWordSeqToInt(cs);
            { lemma_power_1(pv); }  //- and apply earlier calc
        BEWordSeqToInt(cs) + carry*power(pv,1) * power(pv, lastj+bi);
            { lemma_mul_is_associative_forall(); lemma_power_adds(pv,1,lastj+bi); }
        BEWordSeqToInt(cs) + carry*power(pv, j+bi);
    }
}
