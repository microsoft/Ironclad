include "bit_vector_lemmas.i.dfy"
include "../../Drivers/CPU/assembly_premium.i.dfy"

static lemma lemma_and_with_ff_premium()
    ensures Word32(0xFF);
    ensures forall x :: Word32(x) ==> 0 <= Asm_BitwiseAnd(x, 0xFF) < 256 && IsByte(Asm_BitwiseAnd(x, 0xFF));
{
    lemma_2toX();
    forall x | Word32(x)
        ensures 0 <= Asm_BitwiseAnd(x, 0xFF) < 256;
        ensures Word16(Asm_BitwiseAnd(x, 0xFF));
    {
        lemma_word32_Word32();
        lemma_and_with_ff(x);
    }
}

static lemma lemma_and_with_ffff_premium()
    ensures Word32(0xFFFF);
    ensures forall x :: Word32(x) ==> 0 <= Asm_BitwiseAnd(x, 0xFFFF) < 0x10000 && Word16(Asm_BitwiseAnd(x, 0xFFFF));
{
    lemma_2toX();
    forall x | Word32(x)
        ensures 0 <= Asm_BitwiseAnd(x, 0xFFFF) < 0x10000;
        ensures Word16(Asm_BitwiseAnd(x, 0xFFFF));
    {
        lemma_word32_Word32();
        lemma_and_with_ffff(x);
    }
}


static lemma lemma_and_with_32_64_specific_premium(x:int)
    requires Word32(x);
    ensures Word32(32) && Word32(64);
    ensures Asm_BitwiseAnd(x, 32) > 0 ==> BEWordToBitSeq(x)[26] == 1;
    ensures Asm_BitwiseAnd(x, 64) > 0 ==> BEWordToBitSeq(x)[25] == 1;
{
    lemma_and_with_32_64_premium();
}

static lemma lemma_and_with_32_64_premium()
    ensures Word32(32) && Word32(64);
    ensures forall x :: Word32(x) ==> (Asm_BitwiseAnd(x, 32) > 0 ==> BEWordToBitSeq(x)[26] == 1);
    ensures forall x :: Word32(x) ==> (Asm_BitwiseAnd(x, 64) > 0 ==> BEWordToBitSeq(x)[25] == 1);
{
    lemma_2toX();
    forall x | Word32(x)
        ensures Asm_BitwiseAnd(x, 32) > 0 ==> BEWordToBitSeq(x)[26] == 1;
        ensures Asm_BitwiseAnd(x, 64) > 0 ==> BEWordToBitSeq(x)[25] == 1;
    {
        lemma_word32_Word32();
        lemma_and_with_32_64(x);
        lemma_IntBit_is_BEWordToBitSeq();
    }

}

static lemma lemma_xor_bytes_premium(x:int, y:int)
    requires 0 <= x < 256;
    requires 0 <= y < 256;

    ensures word32(x);
    ensures word32(y);
    ensures Word32(x);
    ensures Word32(y);
    ensures 0 <= asm_BitwiseXor(x, y) < 256;
    ensures 0 <= Asm_BitwiseXor(x, y) < 256;
    ensures 0 <= BitwiseXor(x, y) < 256;
{
    lemma_2toX();
    lemma_word32(x);
    lemma_word32(y);
    lemma_xor_bytes(x, y);
}

