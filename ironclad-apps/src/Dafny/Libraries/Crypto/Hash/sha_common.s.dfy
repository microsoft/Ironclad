include "../../base.s.dfy"
include "../../../Drivers/CPU/assembly.s.dfy"
include "../../Util/integer_sequences.s.dfy"
include "../../Util/seq_blocking.s.dfy"

//-///////////////////////////////////////////////////
//- Ch, Maj, BSIG0, BSIG1, SSIG0, SSIG1
//-///////////////////////////////////////////////////

static function {:opaque} Ch(x: int, y: int, z: int) : int
    requires Word32(x);
    requires Word32(y);
    requires Word32(z);
    ensures Word32(Ch(x, y, z));
{
    BitwiseXor(BitwiseAnd(x, y), BitwiseAnd(BitwiseNot(x), z))
}

static function {:opaque} Maj(x: int, y: int, z: int) : int
    requires Word32(x);
    requires Word32(y);
    requires Word32(z);
    ensures Word32(Maj(x, y, z));
{
    BitwiseXor(BitwiseXor(BitwiseAnd(x, y), BitwiseAnd(x, z)), BitwiseAnd(y, z))
}

static function {:opaque} Parity(x: int, y: int, z: int) : int
    requires Word32(x);
    requires Word32(y);
    requires Word32(z);
    ensures Word32(Parity(x, y, z));
{
    BitwiseXor(BitwiseXor(x, y), z)
}

static function {:opaque} ft(t: int, x: int, y: int, z: int) : int
    requires 0 <= t <= 79;
    requires Word32(x);
    requires Word32(y);
    requires Word32(z);
    ensures Word32(ft(t, x, y, z));
{

    if t >= 0 && t <= 19 then
        Ch(x, y, z)

    else if t >= 40 && t <= 59 then
        Maj(x, y, z)
    else
        Parity(x, y, z)
}

static function {:opaque} BSIG0(x: int) : int
    requires Word32(x);
    ensures Word32(BSIG0(x));
{
    BitwiseXor(BitwiseXor(RotateRight(x, 2), RotateRight(x, 13)), RotateRight(x, 22))
}

static function {:opaque} BSIG1(x: int) : int
    requires Word32(x);
    ensures Word32(BSIG1(x));
{
    BitwiseXor(BitwiseXor(RotateRight(x, 6), RotateRight(x, 11)), RotateRight(x, 25))
}

static function {:opaque} SSIG0(x: int) : int
    requires Word32(x);
    ensures Word32(SSIG0(x));
{
    BitwiseXor(BitwiseXor(RotateRight(x, 7), RotateRight(x, 18)), RightShift(x, 3))
}

static function {:opaque} SSIG1(x: int) : int
    requires Word32(x);
    ensures Word32(SSIG1(x));
{
    BitwiseXor(BitwiseXor(RotateRight(x, 17), RotateRight(x, 19)), RightShift(x, 10))
}

static function method {:opaque} NumPaddingZeroes(message_len: int) : int
    //- According to the spec, this is the smallest non-negative k such that message_len + 1 + k = 448 (mod 512)
    //-    ensures (message_len + 1 + NumPaddingZeroes(message_len)) % 512 == 448;
    
    //-    ensures NumPaddingZeroes(message_len) <= (448 - message_len - 1) % 512;
    //-    ensures (message_len + NumPaddingZeroes(message_len) + 1) % 32 == 0;
    ensures 0 <= NumPaddingZeroes(message_len) < 512;
{
    (959 - (message_len % 512)) % 512
}

static function PadMessageForSHA(messageBits: seq<int>) : seq<int>
{
    messageBits + [1] + RepeatDigit(0, NumPaddingZeroes(|messageBits|)) + BEIntToDigitSeq(2, 64, |messageBits|)
}

static function {:opaque} BlockMessageForSHA(paddedMessageBits: seq<int>) : seq<seq<int>>
    requires IsBitSeq(paddedMessageBits);
    requires |paddedMessageBits| % 512 == 0;
{
    BreakIntoBlocks(BEIntToDigitSeq(power2(32), |paddedMessageBits|/32, BEBitSeqToInt(paddedMessageBits)), 16)
}

static function method OneOf8(i: int, n0: int, n1: int, n2: int, n3: int, n4: int, n5: int, n6: int, n7: int) : int
    requires 0 <= i < 8;
{
    if i == 0 then n0 else if i == 1 then n1 else if i == 2 then n2 else if i == 3 then n3
    else if i == 4 then n4 else if i == 5 then n5 else if i == 6 then n6 else n7
}

//- Used to avoid matching loops in some uses of forall
//- (avoid formulas of the form "forall i :: ...a[i]...a[i+1]...", which can loop
//- if the trigger is a[i] and the i+1 in the body is used to instantiate the i in the trigger)
static function TBlk(blk:int):bool { true }
static function TStep(t:int):bool { true }

