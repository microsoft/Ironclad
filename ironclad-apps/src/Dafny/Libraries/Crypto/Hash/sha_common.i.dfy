include "../../base.s.dfy"
include "../../../Drivers/CPU/assembly.s.dfy"
include "../../../Drivers/CPU/assembly_premium.i.dfy"
include "../../Util/integer_sequences.s.dfy"
include "../../Util/seq_blocking.s.dfy"
include "sha_common.s.dfy"

static function method{:CompiledSpec} CompiledSpec_NumPaddingZeroes(message_len: int) : int
static function method{:CompiledSpec} CompiledSpec_OneOf8(i: int, n0: int, n1: int, n2: int, n3: int, n4: int, n5: int, n6: int, n7: int) : int

static function{:opaque} Mul16(i:int):int { i * 16 }
static function{:opaque} Mod16(i:int):int { i % 16 }

//-///////////////////////////////////////////////////
//- Ch, Maj, BSIG0, BSIG1, SSIG0, SSIG1
//-///////////////////////////////////////////////////

static function method Ch_impl(x: int, y: int, z: int) : int
    requires Word32(x);
    requires Word32(y);
    requires Word32(z);
    ensures Word32(Ch_impl(x, y, z));
    ensures Ch_impl(x, y, z) == Ch(x, y, z);
{
    reveal_Ch();
    Asm_BitwiseXor(Asm_BitwiseAnd(x, y), Asm_BitwiseAnd(Asm_BitwiseNot(x), z))
}

static function method Maj_impl(x: int, y: int, z: int) : int
    requires Word32(x);
    requires Word32(y);
    requires Word32(z);
    ensures Word32(Maj_impl(x, y, z));
    ensures Maj_impl(x, y, z) == Maj(x, y, z);
{
    reveal_Maj();
    Asm_BitwiseXor(Asm_BitwiseXor(Asm_BitwiseAnd(x, y), Asm_BitwiseAnd(x, z)), Asm_BitwiseAnd(y, z))
}

static function method Parity_impl(x: int, y: int, z: int) : int
    requires Word32(x);
    requires Word32(y);
    requires Word32(z);
    ensures Word32(Parity_impl(x, y, z));
    ensures Parity_impl(x, y, z) == Parity(x, y, z);
{
    reveal_Parity();
    Asm_BitwiseXor(Asm_BitwiseXor(x, y), z)
}

static function method ft_impl(t: int, x: int, y: int, z: int) : int
    requires 0 <= t <= 79;
    requires Word32(x);
    requires Word32(y);
    requires Word32(z);
    ensures Word32(ft_impl(t, x, y, z));
    ensures ft_impl(t, x, y, z) == ft(t, x, y, z);
{
    reveal_ft();

    if t >= 0 && t <= 19 then
        Ch_impl(x, y, z)

    else if t >= 40 && t <= 59 then
        Maj_impl(x, y, z)
    else
        Parity_impl(x, y, z)
}

static function method BSIG0_impl(x: int) : int
    requires Word32(x);
    ensures Word32(BSIG0_impl(x));
    ensures BSIG0_impl(x) == BSIG0(x);
{
    reveal_BSIG0();
    Asm_BitwiseXor(Asm_BitwiseXor(Asm_RotateRight(x, 2), Asm_RotateRight(x, 13)), Asm_RotateRight(x, 22))
}

static function method BSIG1_impl(x: int) : int
    requires Word32(x);
    ensures Word32(BSIG1_impl(x));
    ensures BSIG1_impl(x) == BSIG1(x);
{
    reveal_BSIG1();
    Asm_BitwiseXor(Asm_BitwiseXor(Asm_RotateRight(x, 6), Asm_RotateRight(x, 11)), Asm_RotateRight(x, 25))
}

static function method SSIG0_impl(x: int) : int
    requires Word32(x);
    ensures Word32(SSIG0_impl(x));
    ensures SSIG0_impl(x) == SSIG0(x);
{
    reveal_SSIG0();
    Asm_BitwiseXor(Asm_BitwiseXor(Asm_RotateRight(x, 7), Asm_RotateRight(x, 18)), Asm_RightShift(x, 3))
}

static function method SSIG1_impl(x: int) : int
    requires Word32(x);
    ensures Word32(SSIG1_impl(x));
    ensures SSIG1_impl(x) == SSIG1(x);
{
    reveal_SSIG1();
    Asm_BitwiseXor(Asm_BitwiseXor(Asm_RotateRight(x, 17), Asm_RotateRight(x, 19)), Asm_RightShift(x, 10))
}

static lemma lemma_SHA_impl_Bytes_arrays_bitmangle(messageBytes:array<int>,
    messageBytes_seq:seq<int>, messageBits:seq<int>, M_seq:seq<int>, bits:int)
    requires messageBytes!=null;
    requires IsWordSeq(M_seq);
    requires 0 <= bits <= |BEWordSeqToBitSeq_premium(M_seq)|;
    requires messageBits == BEWordSeqToBitSeq_premium(M_seq)[..bits];
    requires messageBytes_seq == messageBytes[..];
    requires IsByteSeq(messageBytes_seq);
    requires BEByteSeqToBitSeq_premium(messageBytes[..]) == BEWordSeqToBitSeq(M_seq)[..bits];
    ensures messageBits == BEByteSeqToBitSeq_premium(messageBytes_seq);
{
    calc {
        messageBits;
        BEWordSeqToBitSeq_premium(M_seq)[..bits];
        BEWordSeqToBitSeq(M_seq)[..bits];
        BEByteSeqToBitSeq_premium(messageBytes[..]);
        BEByteSeqToBitSeq_premium(messageBytes_seq);
    }
}

static lemma lemma_SHA_impl_Words_arrays_bitmangle(messageWords:array<int>,
    messageWords_seq:seq<int>, messageBits:seq<int>, M_seq:seq<int>, bits:int)
    requires messageWords!=null;
    requires IsWordSeq(M_seq);
    requires 0 <= bits <= |BEWordSeqToBitSeq_premium(M_seq)|;
    requires messageBits == BEWordSeqToBitSeq_premium(M_seq)[..bits];
    requires messageWords_seq == messageWords[..];
    requires IsWordSeq(messageWords_seq);
    requires BEWordSeqToBitSeq_premium(messageWords[..]) == BEWordSeqToBitSeq(M_seq)[..bits];
    ensures messageBits == BEWordSeqToBitSeq_premium(messageWords_seq);
{
    calc {
        messageBits;
        BEWordSeqToBitSeq_premium(M_seq)[..bits];
        BEWordSeqToBitSeq(M_seq)[..bits];
        BEWordSeqToBitSeq_premium(messageWords[..]);
        BEWordSeqToBitSeq_premium(messageWords_seq);
    }
}

