include "../../Drivers/CPU/assembly.i.dfy"

//-///////////////////////////////////////////////////
//-  These connect to the underlying lemmas proven 
//-  in Boogie.  It is strongly suggested that you
//-  call the premium versions of these lemmas 
//-  (in bit_vector_lemmas_premium.i.dfy) instead of
//-  calling these directly.
//-///////////////////////////////////////////////////

static lemma {:decl} lemma_xor_bytes(x:int, y:int)
    requires 0 <= x < 256;
    requires 0 <= y < 256;
    requires word32(x);
    requires word32(y);
    ensures 0 <= asm_BitwiseXor(x, y) < 256;

static lemma {:decl} lemma_and_with_ff(x:int)
    requires word32(x);
    requires word32(0xFF);
    ensures  0 <= asm_BitwiseAnd(x, 0xFF) < 256;

static lemma {:decl} lemma_and_with_ffff(x:int)
    requires word32(x);
    requires word32(0xFFFF);
    ensures  0 <= asm_BitwiseAnd(x, 0xFFFF) < 0x10000;

static lemma {:decl} lemma_and_with_32_64(x:int)
    requires word32(x);
    requires word32(32);
    requires word32(64);
    ensures  asm_BitwiseAnd(x, 32) > 0 ==> IntBit(26, x);
    ensures  asm_BitwiseAnd(x, 64) > 0 ==> IntBit(25, x);
