include "FleetNatMulLemmas.i.dfy"

method {:decl} FleetNatMulMathOpt(aj:int, bv:int, lastcj:int, lastcarry:int)
    returns (newcj:int, newcarry:int)
    requires 0<=aj<0x100000000;
    requires 0<=bv<0x100000000;
    requires 0<=lastcj<0x100000000;
    requires 0<=lastcarry<0x100000000;
    ensures 0<=newcj<0x100000000;
    ensures 0<=newcarry<0x100000000;

    ensures newcj + newcarry*0x100000000 == aj * bv + lastcj + lastcarry;
/*
{
    //- mul
    lemma_mod_properties();
    lemma_word32(aj);
    lemma_word32(bv);
    var mhi,mlo := asm_Mul64(aj, bv);
    lemma_asm_Mul64(aj, bv, mhi, mlo);

    //- add1
    lemma_word32(mlo);
    lemma_word32(lastcarry);
    var add1 := asm_Add(mlo, lastcarry);
    var carry1 := 0;
    if (add1 < lastcarry) { carry1 := 1; }
    lemma_asm_Add_properties(mlo, lastcarry, add1, carry1);

    //- add2
    lemma_word32(lastcj);
    newcj := asm_Add(add1, lastcj);
    var carry2 := 0;
    if (newcj < lastcj) { carry2 := 1; }
    lemma_asm_Add_properties(add1, lastcj, newcj, carry2);

    //- add3
    lemma_word32(carry1);
    lemma_word32(carry2);
    var add3 := asm_Add(carry1, carry2);
    ghost var carry3 := 0;
    if (add3 < carry2) { carry3 := 1; }
    lemma_asm_Add_properties(carry1, carry2, add3, carry3);

    //- add4
    newcarry := asm_Add(add3, mhi);
    ghost var carry4 := 0;
    if (newcarry < mhi) { carry4 := 1; }
    lemma_asm_Add_properties(add3, mhi, newcarry, carry4);

    lemma_2toX();
    lemma_FleetNatMul_one_element_properties(0x100000000,
        aj, bv, mhi, mlo,
        lastcarry, add1, carry1,
        lastcj, newcj, carry2,
        add3, carry3,
        newcarry, carry4);
}
*/
