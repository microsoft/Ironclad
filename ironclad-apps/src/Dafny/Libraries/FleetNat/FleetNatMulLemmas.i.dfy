include "FleetNatAdd.i.dfy"

lemma lemma_asm_Mul64(x:int, y:int, hi:int, lo:int)
    requires word32(x);
    requires word32(y);
    requires word32(hi);
    requires word32(lo);
    requires lo == mod0x100000000(x * y);
    requires hi == (x * y) / 0x100000000;
    ensures hi*power2(32)+lo == x*y;
    ensures 0 <= lo < power2(32);
    ensures 0 <= hi < power2(32)-1;
    ensures 0 <= x*y;
{
    lemma_2toX();
    var pv:=power2(32);
    lemma_word32(x);
    lemma_word32(y);
    lemma_word32(hi);
    lemma_word32(lo);
    calc {
        x*y;
        <=  { lemma_mul_inequality(x,pv-1,y); }
        (pv-1)*y;
        <=  { lemma_mul_inequality(y,pv-1,pv-1); }
        (pv-1)*(pv-1);
            { lemma_mul_is_distributive_forall(); }
        pv*pv-2*pv+1;
    }
    lemma_mod_properties();

    lemma_mod0x100000000(x*y);
    lemma_fundamental_div_mod(x*y, pv);

    if (pv<=hi)
    {
        calc {
            pv*pv;
            <=  { lemma_fundamental_div_mod(x*y,pv); }
                pv*((x*y)/pv);
            <= x*y;
            <   { lemma_mul_strict_inequality(x, pv, y); }
            pv*y;
            <   { lemma_mul_strict_inequality(y, pv, pv); }
            pv*pv;
        }   //- contradiction
    }
    if (hi == pv-1)
    {
        calc {
            pv*pv - pv;
            <
            (pv-1)*pv;
            <=
            (pv-1)*pv+lo;
            hi*pv+lo;
            x*y;
            <
            (pv-1)*(pv-1);
            pv*pv-2*pv-1;
            <
            pv*pv - pv;
        }   //- contradiction
    }
}

lemma lemma_FleetNatMul_one_element_properties(pv:int,
            aj:int, bv:int, mhi:int, mlo:int,
            lastcarry:int, add1:int, carry1:int,
            lastcj:int, newcj:int, carry2:int,
            add3:int, carry3:int,
            carry:int, carry4:int)
    requires pv==power2(32);
    requires 0<=aj<pv;
    requires 0<=bv<pv;
    requires 0<=mhi<pv;
    requires 0<=mlo<pv;
    requires 0<=lastcarry<pv;
    requires 0<=add1<pv;
    requires 0<=carry1<2;
    requires 0<=lastcj<pv;
    requires 0<=newcj<pv;
    requires 0<=carry2<2;
    requires 0<=add3<pv;
    requires 0<=carry3<pv;
    requires 0<=carry<pv;
    requires 0<=carry4<pv;

    //- Mul
    requires mhi*pv+mlo == aj*bv;
    //- add1
    requires mlo + lastcarry == add1 + carry1 * pv;
    //- add2
    requires add1 + lastcj == newcj + carry2 * pv;
    //- add3
    requires carry1 + carry2 == add3 + carry3 * pv;
    //- add4
    requires add3 + mhi == carry + carry4 * pv;
    ensures 0<=carry<pv;
    ensures newcj + carry*pv == aj * bv + lastcj + lastcarry;
{
    lemma_2toX();
//-    assert carry3==0;
    calc {
        aj*bv + lastcarry + lastcj;
        mhi*pv+mlo + lastcarry + lastcj;
        mhi*pv+add1+carry1*pv + lastcj;
        mhi*pv+carry1*pv+newcj+carry2*pv;

        mhi*pv+(carry1+carry2)*pv+newcj;
        mhi*pv+(add3+carry3*pv)*pv+newcj;
        mhi*pv+add3*pv+newcj;

        (mhi+add3)*pv+newcj;
        (carry + carry4*pv)*pv+newcj;

        carry*pv + carry4*pv*pv+newcj;
    }
    lemma_mul_inequality(aj,pv-1,bv);
    lemma_mul_inequality(bv,pv-1,pv-1);
//-    if (0<carry4)
//-    {
//-        assert carry*pv + carry4*pv*pv+newcj >= pv*pv;
//-        assert aj*bv + lastcarry + lastcj < pv*pv;
//-    }
//-    assert carry4==0;
}

