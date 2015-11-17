//-<NuBuild BasmEnableSymdiff true />
include "../../Libraries/Util/bytes_and_words.s.dfy"
include "../../Libraries/Util/be_sequences.s.dfy"
include "../../Libraries/Util/integer_sequences_premium.i.dfy"
include "assembly.i.dfy"

//-////////////////////////////////////////////////////////////
//-  Upscale wrappers around the basic assembly instructions
//-  that Boogie exposes via assembly.i.dfy
//-////////////////////////////////////////////////////////////

//-/////////////////  Helpers ////////////////////////////////

static lemma lemma_word32_Word32()
    ensures forall x:int {:trigger word32(x)} :: word32(x) == Word32(x);
{
    forall x:int
        ensures word32(x) == Word32(x);
    {
        lemma_word32(x);
        lemma_power2_32();
    }
}

static lemma lemma_IntBit_is_BEWordToBitSeq()
    ensures forall x, i :: Word32(x) && 0 <= i < 32 ==>  (IntBit(i, x) <==> (BEWordToBitSeq_premium(x)[i] == 1));
    ensures forall x, i :: Word32(x) && 0 <= i < 32 ==> (!IntBit(i, x) <==> (BEWordToBitSeq_premium(x)[i] == 0));
{
    forall x, i | Word32(x) && 0 <= i < 32 
        ensures  IntBit(i, x) <==> (BEWordToBitSeq_premium(x)[i] == 1);
        ensures !IntBit(i, x) <==> (BEWordToBitSeq_premium(x)[i] == 0);
    {
        lemma_IntBit(i, x);
        lemma_IntBit_is_BEWordToBitSeq_specific(i, x);
    }
}

static lemma lemma_IntBit_is_IntBit_spec()
    ensures forall x, i :: Word32(x) && 0 <= i < 32 ==> IntBit(i, x) == IntBit_spec(i, x);
{
        lemma_IntBit_is_BEWordToBitSeq();
}

static lemma lemma_IntBit_is_BEWordToBitSeq_specific(index:int, x:int)
    requires 0 <= index < 32;
    requires Word32(x);
    ensures  IntBit(index, x) <== (BEWordToBitSeq_premium(x)[index] == 1);
    ensures  IntBit(index, x) ==> (BEWordToBitSeq_premium(x)[index] == 1);
    decreases 32 - index;
{
    lemma_IntBit(index, x);
    lemma_word32(x);
    lemma_2toX();
    
    calc {
        BEWordToBitSeq_premium(x);
        BEIntToDigitSeq(power2(1), 32, x);
        { reveal_power2(); } 
        BEIntToDigitSeq(2, 32, x);
        BEIntToDigitSeq_private(2, 32, x);
        { reveal_BEIntToDigitSeq_private(); }
        BEIntToDigitSeq_private(2, 32-1, x/2) + [ x % 2];
    }

    if (index == 31) {
        lemma_2toX();
        calc {
            power(2, 31);
            { lemma_power2_is_power_2_general(); }
            power2(31);
            { lemma_power2_adds(24, 7); lemma_power2_adds(3, 4); reveal_power2(); }
            0x80000000;
        }

        lemma_BEIntToDigitSeq_private_properties(2, 31, x/2);
    } else {
        lemma_IntBit_is_BEWordToBitSeq_specific(index + 1, x/2);

        assert IntBit(index, x) == IntBit(index + 1, x/2);
        assert IntBit(index + 1, x/2) ==> BEWordToBitSeq_premium(x/2)[index+1] == 1;
        calc {
            BEWordToBitSeq_premium(x/2)[index+1];
            BEIntToDigitSeq_private(power2(1), 32, x/2)[index+1];
            { lemma_power2_1_is_2(); }
            BEIntToDigitSeq_private(2, 32, x/2)[index+1];
            { lemma_index_shift(index, x); }
            BEIntToDigitSeq_private(2, 32-1, x/2)[index];
            BEWordToBitSeq_premium(x)[index];
        }
    }
}

static lemma lemma_index_shift(index:int, x:int) 
    requires 0 <= index < 31;
    requires Word32(x);
    ensures |BEIntToDigitSeq_private(2, 32, x/2)| == 32;    //- To assuage function precondition below
    ensures |BEIntToDigitSeq_private(2, 32-1, x/2)| == 31;    //- To assuage function precondition below
    ensures BEIntToDigitSeq_private(2, 32, x/2)[index+1] ==
            BEIntToDigitSeq_private(2, 32-1, x/2)[index];
{
    reveal_power2();
    var y := x/2;
    assert y < power2(31);

    lemma_power2_is_power_2(31);
    lemma_power2_increases(31,32);
    lemma_power2_is_power_2(32);

    lemma_BEIntToDigitSeq_private_properties(2, 32, y);
    assert |BEIntToDigitSeq_private(2, 32, x/2)| == 32;

    lemma_BEIntToDigitSeq_private_properties(2, 31, y);
    assert |BEIntToDigitSeq_private(2, 32-1, x/2)| == 31;



    calc {
        BEIntToDigitSeq_private(2, 32, y);
        BEIntToDigitSeq_private(power2(1), 32, y);
        {
            lemma_mul_is_mul_boogie(1,31);
            lemma_mul_is_mul_boogie(1,32);
            lemma_BEIntToDigitSeq_private_chop(1, 32, 31, y);
        }
        BEIntToDigitSeq_private(power2(1), 32-31, y/power2(1*31)) + BEIntToDigitSeq_private(power2(1), 31, y%power2(1*31));
            { lemma_small_mod(y, power2(31)); }
        BEIntToDigitSeq_private(power2(1), 32-31, y/power2(1*31)) + BEIntToDigitSeq_private(2, 31, y);
            { lemma_small_div(); }
        BEIntToDigitSeq_private(2, 1, 0) + BEIntToDigitSeq_private(2, 31, y);
        {
            reveal_BEIntToDigitSeq_private();
            lemma_small_div();
            lemma_small_mod(0, 2);
        }
        [0] + BEIntToDigitSeq_private(2, 31, y);
    }
    assert BEIntToDigitSeq_private(2, 32, y)[index+1] == BEIntToDigitSeq_private(2, 31, y)[index];
}

static lemma lemma_bits_match_implies_ints_match_general()
    ensures forall x, y :: Word32(x) && Word32(y) && (forall i :: 0 <= i < 32 ==> IntBit(i, x) == IntBit(i, y))
            ==> x == y;
{
    forall x, y | Word32(x) && Word32(y) && (forall i :: 0 <= i < 32 ==> IntBit(i, x) == IntBit(i, y))
        ensures x == y;
    {
        lemma_bits_match_implies_ints_match(x, y);
    }
}


static lemma lemma_bits_match_implies_ints_match(x:int, y:int) 
    requires Word32(x) && Word32(y);
    requires forall i :: 0 <= i < 32 ==> IntBit(i, x) == IntBit(i, y);
    ensures x == y;
{
    var xb := BEWordToBitSeq_premium(x);
    var yb := BEWordToBitSeq_premium(y);

    assert |xb| == |yb| == 32;
    forall i | 0 <= i < 32 
        ensures xb[i] == yb[i];
    {
        calc {
            xb[i] == 1;
            { lemma_IntBit_is_BEWordToBitSeq(); }
            IntBit(i, x);
            IntBit(i, y);
            { lemma_IntBit_is_BEWordToBitSeq(); }
            yb[i] == 1;
        }
    }

    assert xb == yb;

    calc {
        x;
        BEBitSeqToInt(xb);
        BEBitSeqToInt(yb);
        y;
    }
}


//-static lemma lemma_bits_match_implies_ints_match_helper(x:int, y:int, index:int) 
//-    requires Word32(x) && Word32(y);
//-    requires forall i :: 0 <= i < 32 ==> IntBit(i, x) == IntBit(i, y);
    

//-/////////////////  Methods ////////////////////////////////

static method{:instruction "out@EDX", "inout@EAX", "in"}{:strict_operands} Method_Mul(x:int, y:int) returns(hi:int, r:int)
    ensures  r == x * y;
{
    lemma_mul_is_mul_boogie(x, y);
    hi, r := method_Mul(x, y);
}

static method{:instruction "inout@EDX", "inout@EAX", "in"}{:strict_operands} Method_DivMod(zero:int, x:int, y:int) returns(m:int, r:int)
    requires zero == 0;
    requires y != 0;
    ensures  r == x / y;
    ensures  y > 0 ==> m == x % y;
{
    lemma_div_is_div_boogie(x, y);
    if (y > 0) { lemma_mod_is_mod_boogie(x, y); }
    m, r := method_DivMod(zero, x, y);
}

static function method{:instruction "inout", "in"} Asm_Add(x:int, y:int):int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(Asm_Add(x, y));
    ensures Asm_Add(x, y) == mod0x100000000(x + y);
    ensures Asm_Add(x, y) == Add32(x, y);
{
    lemma_word32_Word32();
    lemma_mod0x100000000(x+y);
    asm_Add(x, y)
}

static function method{:instruction "inout", "in"} Asm_Sub(x:int, y:int):int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(Asm_Sub(x, y));
    ensures Asm_Sub(x, y) == mod0x100000000(x - y);
{
    lemma_word32_Word32();
    lemma_mod0x100000000(x-y);
    asm_Sub(x, y)
}

static function method Asm_Mul(x:int, y:int):int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(Asm_Mul(x, y));
    ensures Asm_Mul(x, y) == mod0x100000000(x*y);
{
    lemma_word32_Word32();
    lemma_mod0x100000000(x*y);
    asm_Mul(x, y)
}

static function method Asm_Div(x:int, y:int):int
    requires Word32(x);
    requires Word32(y);
    requires y > 0;
    ensures Word32(Asm_Div(x, y));
    ensures Asm_Div(x, y) == mod0x100000000(x/y);
{
    lemma_word32_Word32();
    lemma_mod0x100000000(x/y);
    asm_Div(x, y)
}

static function method Asm_Mod(x:int, y:int):int
    requires Word32(x);
    requires Word32(y);
    requires y > 0;
    ensures Word32(Asm_Mod(x, y));
    ensures Asm_Mod(x, y) == x % y;
{
    lemma_word32_Word32();
    lemma_mod0x100000000(x%y);
    asm_Mod(x, y)
}

static function method{:instruction "inout", "in@ECX"} Asm_LeftShift(x:int, amount:int):int
    requires Word32(x);
    requires 0 <= amount < 32;
    ensures Word32(Asm_LeftShift(x, amount));
    ensures |BEWordToBitSeq_premium(x)| == 32;
    ensures BEWordToBitSeq_premium(Asm_LeftShift(x, amount)) == BEWordToBitSeq_premium(x)[amount..] + RepeatDigit_premium(0, amount);
    ensures Asm_LeftShift(x, amount) == LeftShift(x, amount); //- Fulfills spec
{
    lemma_word32_Word32();
    lemma_IntBit_is_BEWordToBitSeq();
    lemma_bits_match_implies_ints_match_general();
    lemma_IntBit_is_IntBit_spec();
    asm_LeftShift(x, amount)
}

static function method{:instruction "inout", "in@ECX"} Asm_RightShift(x:int, amount:int):int
    requires Word32(x);
    requires 0 <= amount < 32;
    ensures Word32(Asm_RightShift(x, amount));
    ensures |BEWordToBitSeq(x)| == 32;
    ensures BEWordToBitSeq_premium(Asm_RightShift(x, amount)) == RepeatDigit_premium(0, amount) + BEWordToBitSeq_premium(x)[..32-amount];
    ensures Asm_RightShift(x, amount) == RightShift(x, amount); //- Fulfills spec
{
    lemma_word32_Word32();
    lemma_IntBit_is_BEWordToBitSeq();
    lemma_bits_match_implies_ints_match_general();
    lemma_IntBit_is_IntBit_spec();
    asm_RightShift(x, amount)
}

static function method{:instruction "inout", "in@ECX"} Asm_RotateLeft(x:int, amount:int):int
    requires Word32(x);
    requires 0 <= amount < 32;
    ensures Word32(Asm_RotateLeft(x, amount));
    ensures |BEWordToBitSeq(x)| == 32;
    ensures BEWordToBitSeq_premium(Asm_RotateLeft(x, amount)) == BEWordToBitSeq_premium(x)[amount..] + BEWordToBitSeq_premium(x)[..amount];
    ensures Asm_RotateLeft(x, amount) == RotateLeft(x, amount); //- Fulfills spec
{
    lemma_word32_Word32();
    lemma_IntBit_is_BEWordToBitSeq();
    lemma_bits_match_implies_ints_match_general();
    lemma_IntBit_is_IntBit_spec();
    asm_RotateLeft(x, amount)
}

static function method{:instruction "inout", "in@ECX"} Asm_RotateRight(x:int, amount:int):int
    requires Word32(x);
    requires 0 <= amount < 32;
    ensures Word32(Asm_RotateRight(x, amount));
    ensures |BEWordToBitSeq(x)| == 32;
    ensures BEWordToBitSeq_premium(Asm_RotateRight(x, amount)) == BEWordToBitSeq_premium(x)[32-amount..] + BEWordToBitSeq_premium(x)[..32-amount];
    ensures Asm_RotateRight(x, amount) == RotateRight(x, amount); //- Fulfills spec
{
    lemma_word32_Word32();
    lemma_IntBit_is_BEWordToBitSeq();
    lemma_bits_match_implies_ints_match_general();
    lemma_IntBit_is_IntBit_spec();
    asm_RotateRight(x, amount)
}

static function method{:instruction "inout"} Asm_BitwiseNot(x:int):int
    requires Word32(x);
    ensures Word32(Asm_BitwiseNot(x));
    ensures |BEWordToBitSeq_premium(x)| == |BEWordToBitSeq_premium(Asm_BitwiseNot(x))| == 32;
    ensures forall i {:trigger BEWordToBitSeq(Asm_BitwiseNot(x))[i]} :: 0 <= i < 32 ==>
         BEWordToBitSeq_premium(Asm_BitwiseNot(x))[i] == 1 - BEWordToBitSeq_premium(x)[i];
    ensures Asm_BitwiseNot(x) == BitwiseNot(x); //- Fulfills spec
{
    lemma_word32_Word32();
    lemma_IntBit_is_BEWordToBitSeq();
    lemma_bits_match_implies_ints_match_general();
    lemma_IntBit_is_IntBit_spec();
    asm_BitwiseNot(x)
}

static lemma lemma_bitwise_and_commutative(x:int, y:int)
    requires Word32(x) && Word32(y);
    ensures  Asm_BitwiseAnd(x, y) == Asm_BitwiseAnd(y, x);
{
    forall i | 0 <= i < 32 
        //-ensures Asm_BitwiseAnd(x, y) == Asm_BitwiseAnd(y, x);
        ensures BEWordToBitSeq_premium(Asm_BitwiseAnd(x, y))[i] == BEWordToBitSeq_premium(Asm_BitwiseAnd(y, x))[i];
    {
        calc {
            BEWordToBitSeq_premium(Asm_BitwiseAnd(x, y))[i];
            if (BEWordToBitSeq_premium(x)[i] == 1 && BEWordToBitSeq_premium(y)[i] == 1) then 1 else 0;
            BEWordToBitSeq_premium(Asm_BitwiseAnd(y, x))[i];
        }
    }
    assert BEWordToBitSeq_premium(Asm_BitwiseAnd(x, y)) == BEWordToBitSeq_premium(Asm_BitwiseAnd(y, x));
}

static function method{:instruction "inout", "in"} Asm_BitwiseAnd(x:int, y:int):int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(Asm_BitwiseAnd(x, y));
    ensures |BEWordToBitSeq_premium(x)| == |BEWordToBitSeq_premium(y)| == |BEWordToBitSeq_premium(Asm_BitwiseAnd(x, y))| == 32;
    ensures forall i {:trigger BEWordToBitSeq(Asm_BitwiseAnd(x, y))[i]} :: 0 <= i < 32 ==>
        BEWordToBitSeq_premium(Asm_BitwiseAnd(x, y))[i] == if (BEWordToBitSeq_premium(x)[i] == 1 && BEWordToBitSeq_premium(y)[i] == 1) then 1 else 0;
    ensures Asm_BitwiseAnd(x, y) == BitwiseAnd(x, y); //- Fulfills spec
{
    lemma_word32_Word32();
    lemma_IntBit_is_BEWordToBitSeq();
    lemma_bits_match_implies_ints_match_general();
    lemma_IntBit_is_IntBit_spec();
    asm_BitwiseAnd(x,y)
}

static function method{:instruction "inout", "in"} Asm_BitwiseOr(x:int, y:int):int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(Asm_BitwiseOr(x, y));
    ensures |BEWordToBitSeq_premium(x)| == |BEWordToBitSeq_premium(y)| == |BEWordToBitSeq_premium(Asm_BitwiseOr(x, y))| == 32;
    ensures forall i {:trigger BEWordToBitSeq(Asm_BitwiseOr(x, y))[i]} :: 0 <= i < 32 ==>
        BEWordToBitSeq_premium(Asm_BitwiseOr(x, y))[i] == if (BEWordToBitSeq_premium(x)[i] == 1 || BEWordToBitSeq_premium(y)[i] == 1) then 1 else 0;
    ensures Asm_BitwiseOr(x, y) == BitwiseOr(x, y);
{
    lemma_word32_Word32();
    lemma_IntBit_is_BEWordToBitSeq();
    lemma_bits_match_implies_ints_match_general();
    lemma_IntBit_is_IntBit_spec();
    asm_BitwiseOr(x, y)
}

static function method{:instruction "inout", "in"} Asm_BitwiseXor(x:int, y:int):int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(Asm_BitwiseXor(x, y));
    ensures |BEWordToBitSeq_premium(x)| == |BEWordToBitSeq_premium(y)| == |BEWordToBitSeq_premium(Asm_BitwiseXor(x, y))| == 32;
    ensures forall i {:trigger BEWordToBitSeq(Asm_BitwiseXor(x, y))[i]} :: 0 <= i < 32 ==>
        BEWordToBitSeq_premium(Asm_BitwiseXor(x, y))[i] == if (BEWordToBitSeq_premium(x)[i] != BEWordToBitSeq_premium(y)[i]) then 1 else 0;
    ensures Asm_BitwiseXor(x, y) == BitwiseXor(x, y); //- Fulfills spec
{
    lemma_word32_Word32();
    lemma_IntBit_is_BEWordToBitSeq();
    lemma_bits_match_implies_ints_match_general();
    lemma_IntBit_is_IntBit_spec();
    asm_BitwiseXor(x, y)
}

static method Asm_Rdtsc() returns (high:int, low:int)
    ensures Word32(high);
    ensures Word32(low);
{
    lemma_word32_Word32();
    high, low := asm_Rdtsc();
}

method Asm_declassify_result(concrete:int, ghost result:int) returns (pub_result:int)
    requires Word32(concrete);
    requires relation(declassified(left(result), right(result), left(concrete), right(concrete)));
    ensures pub_result == result;
    ensures public(pub_result);
{
    lemma_word32_Word32();
    pub_result := asm_declassify_result(concrete, result);
}

static method GetBootloaderArgWord_premium(index:int) returns (word:int)
    requires 0 <= index < 256;
    ensures  Word32(word);
{
    lemma_word32_Word32();
    word := GetBootloaderArgWord(index);
}

static method GetBootloaderArgBytes(left:int, right:int) returns (s:seq<int>)
    requires 0 <= left <= right < 256 * 4;
    requires left % 4 == 0;
    ensures IsByteSeqOfLen(s, right - left);
{
    s := [];

    var cur := left;
    var done := false;
    while cur < right
        invariant !done ==> left <= cur <= right < 256 * 4;
        invariant cur % 4 == 0;
        invariant IsByteSeqOfLen(s, cur - left);
    {
        var word := GetBootloaderArgWord_premium(cur / 4);
        var bytes := BEWordToFourBytes_impl(word);
        var reverse_bytes := [bytes[3], bytes[2], bytes[1], bytes[0]];
        s := s + reverse_bytes;
        cur := cur + 4;
        if cur > right {
            done := true;
        }
    }

    if cur > right
    {
        s := s[0..right - left];
    }

    assert IsByteSeqOfLen(s, right - left);
}
