


method FleetNatSub_local_math_core(lastcj:int, bj:int, lastborrow:int) returns (newcj:int, borrow:int)
    requires 0<=lastcj<0x100000000;
    requires 0<=bj<0x100000000;
    requires 0<=lastborrow<2;
    ensures 0<=newcj<0x100000000;
    ensures 0<=borrow<2;
    ensures lastcj - lastborrow - bj == newcj - 0x100000000*borrow;
{
    var lastcj := c[ci];
    var borrow1 := 0;
    if (lastcj < borrow) { borrow1 := 1; }
    lemma_word32(lastcj);
    lemma_word32(borrow);
    var midcj := asm_Sub(lastcj, borrow);

    lemma_asm_Sub_properties(lastcj, borrow, midcj, borrow1);

    lemma_word32(1);
    var borrow2 := 0;
    if (midcj < bj) {
        borrow2 := 1;
    }
    lemma_word32(bj);
    newcj := asm_Sub(midcj, bj);

    lemma_asm_Sub_properties(midcj, bj, newcj, borrow2);
    lemma_word32(borrow1);
    borrow := asm_Add(borrow1, borrow2);
    lemma_mod0x100000000(borrow1+borrow2);
}


