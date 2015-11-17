include "../../Libraries/Util/bytes_and_words.s.dfy"
include "../../Libraries/Util/be_sequences.s.dfy"

//-/////////////////////////////////////////////
//-  Abstract definitions of 32-bit operations
//-  that we may want to talk about in specs
//-/////////////////////////////////////////////

 
static function UndefinedBit(index:int, val:int):bool
static function IntBit_spec(index:int, val:int):bool
{
    var bits := BEWordToBitSeq(val);
    if 0 <= index < |bits| then bits[index] == 1
    else UndefinedBit(index, val)
}


//-static lemma{:decl} lemma_IntBit_spec(index:int, val:int)
//-    ensures Word32(val) && 0 <= index < 32 ==> 
//-            IntBit_spec(index, val) == if (index < 31) then IntBit_spec(index + 1, val / 2) else val % 2 != 0;

static function{:axiom} BitwiseAnd(x:int, y:int) : int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(BitwiseAnd(x, y));
    ensures forall i {:trigger IntBit_spec(i, BitwiseAnd(x, y))} :: 0 <= i < 32 ==> IntBit_spec(i, BitwiseAnd(x, y)) == (IntBit_spec(i, x) && IntBit_spec(i, y));

static function{:axiom} BitwiseOr(x:int, y:int):int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(BitwiseOr(x, y));
    ensures forall i {:trigger IntBit_spec(i, BitwiseOr(x, y))} :: 0 <= i < 32 ==> IntBit_spec(i, BitwiseOr(x, y)) == (IntBit_spec(i, x) || IntBit_spec(i, y));

static function{:axiom} BitwiseNot(x:int) : int
    requires Word32(x);
    ensures Word32(BitwiseNot(x));
    ensures forall i {:trigger IntBit_spec(i, BitwiseNot(x))} :: 0 <= i < 32 ==> IntBit_spec(i, BitwiseNot(x)) == !IntBit_spec(i, x);

static function{:axiom} BitwiseXor(x:int, y:int) : int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(BitwiseXor(x, y));
    ensures forall i {:trigger IntBit_spec(i, BitwiseXor(x, y))} :: 0 <= i < 32 ==> IntBit_spec(i, BitwiseXor(x, y)) == (IntBit_spec(i, x) != IntBit_spec(i, y));

static function{:axiom} RotateRight(x:int, amount:int) : int
    requires Word32(x);
    requires 0 <= amount < 32;
    ensures Word32(RotateRight(x, amount));
    ensures forall i {:trigger IntBit_spec(i, RotateRight(x, amount))} :: 0 <= i < amount ==>  IntBit_spec(i, RotateRight(x, amount)) == IntBit_spec((32 - amount)+i, x);
    ensures forall i {:trigger IntBit_spec(i, RotateRight(x, amount))} :: amount <= i < 32 ==> IntBit_spec(i, RotateRight(x, amount)) == IntBit_spec(i - amount, x);

static function{:axiom} RotateLeft(x:int, amount:int):int
    requires Word32(x);
    requires 0 <= amount < 32;
    ensures Word32(RotateLeft(x, amount));
    ensures forall i {:trigger IntBit_spec(i, RotateLeft(x, amount))} :: 0 <= i < 32 - amount ==> IntBit_spec(i, RotateLeft(x, amount)) == IntBit_spec(i + amount, x);
    ensures forall i {:trigger IntBit_spec(i, RotateLeft(x, amount))} :: 32 - amount <= i < 32 ==> IntBit_spec(i, RotateLeft(x, amount)) == IntBit_spec(i - (32 - amount), x);         

static function{:axiom} RightShift(x:int, amount:int) : int
    requires Word32(x);
    requires 0 <= amount < 32;
    ensures Word32(RightShift(x, amount));
    ensures forall i {:trigger IntBit_spec(i, RightShift(x, amount))} :: 0 <= i < amount ==> IntBit_spec(i, RightShift(x, amount)) == false;            
    ensures forall i {:trigger IntBit_spec(i, RightShift(x, amount))} :: amount <= i < 32 ==> IntBit_spec(i, RightShift(x, amount)) == IntBit_spec(i - amount, x);            

static function{:axiom} LeftShift(x:int, amount:int):int
    requires Word32(x);
    requires 0 <= amount < 32;
    ensures Word32(LeftShift(x, amount));
    ensures forall i {:trigger IntBit_spec(i, LeftShift(x, amount))} :: 32 - amount <= i < 32 ==>  IntBit_spec(i, LeftShift(x, amount)) == false;
    ensures forall i {:trigger IntBit_spec(i, LeftShift(x, amount))} :: 0 <= i < 32 - amount ==> IntBit_spec(i, LeftShift(x, amount)) == IntBit_spec(i + amount, x);

static function{:axiom} Add32(x:int, y:int):int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(Add32(x, y));
    ensures Add32(x, y) == (x + y) % 0x100000000;

static function{:axiom} Sub32(x:int, y:int):int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(Sub32(x, y));
    ensures Sub32(x, y) == (x - y) % 0x100000000;

static function{:axiom} Mul32(x:int, y:int):int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(Mul32(x, y));
    ensures Mul32(x, y) == (x * y) % 0x100000000;

static function{:axiom} Div32(x:int, y:int):int
    requires Word32(x);
    requires Word32(y);
    requires y != 0;
    ensures Word32(Div32(x, y));
    ensures Div32(x, y) == (x / y) % 0x100000000;

static function{:axiom} Mod32(x:int, y:int):int
    requires Word32(x);
    requires Word32(y);
    requires y != 0;
    ensures Word32(Mod32(x, y));
    ensures Mod32(x, y) == (x / y) % 0x100000000;

//-//////////////////////////////////////////////////////////////
//-      Versions with bodies
//-//////////////////////////////////////////////////////////////

/*
static function BitwiseNot(x:int) : int
    requires Word32(x);
    //-ensures Word32(BitwiseNot(x));
{
    BitwiseNot_helper(x, 32)
}

static function BitwiseNot_helper(x:int, bits:int) : int
{
    if bits <= 0 then 0
    else 2*BitwiseNot_helper(x, bits - 1) + (1 - (x % 2))
}

static function BitwiseAnd(x:int, y:int) : int
    requires Word32(x);
    requires Word32(y);
    //-ensures Word32(BitwiseAnd(x, y));
{
    BitwiseAnd_helper(x, y, 32)
}

static function BitwiseAnd_helper(x:int, y:int, bits:int) : int
{
    if bits <= 0 then 0
    else 2*BitwiseAnd_helper(x, y, bits - 1) + if (x % 2) == 1 && (y % 2) == 1 then 1 else 0 
}
*/


/*
static function BitwiseNot(x:int) : int
    requires Word32(x);
    ensures Word32(BitwiseNot(x));
{
    BEBitSeqToInt(BitwiseNot_helper(x, 32))
}

static function BitwiseNot_helper(x:int, bits:int) : seq<int>
{
    if bits <= 0 then []
    else BitwiseNot_helper(x, bits - 1) + [(1 - BEWordToBitSeq(x)[bits-1])]
}
*/

/*
static function BitwiseNot(x:int) : int
    requires Word32(x);
    ensures Word32(BitwiseNot(x));
{
    var z :| Word32(z) && forall i :: 0 <= i < 32 ==>
        BEWordToBitSeq(z)[i] == 1 - BEWordToBitSeq(x)[i];
    z
}

static function BitwiseAnd(x:int, y:int) : int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(BitwiseAnd(x, y));
{
    var z :| Word32(z) && forall i :: 0 <= i < 32 ==> 
        BEWordToBitSeq(z)[i] == if BEWordToBitSeq(x)[i] == 1 && BEWordToBitSeq(y)[i] == 1 then 1 else 0;
    z
}

static function BitwiseXor(x:int, y:int) : int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(BitwiseXor(x, y));
{
    var z :| Word32(z) && forall i :: 0 <= i < 32 ==> 
        BEWordToBitSeq(z)[i] == if BEWordToBitSeq(x)[i] != BEWordToBitSeq(y)[i] then 1 else 0;
    z
}

static function RotateRight(x:int, amount:int) : int
    requires Word32(x);
    requires 0 <= amount < 32;
    ensures Word32(RotateRight(x, amount));
{
    var z :| Word32(z) && forall i :: 0 <= i < 32 ==> 
    BEWordToBitSeq(z) == BEWordToBitSeq(x)[32-amount..] + BEWordToBitSeq(x)[..32-amount];
    z
}

static function RotateLeft(x:int, amount:int):int
    requires Word32(x);
    requires 0 <= amount < 32;
    ensures Word32(RotateLeft(x, amount));
{
    var z :| Word32(z) && forall i :: 0 <= i < 32 ==> 
    BEWordToBitSeq(z) == BEWordToBitSeq(x)[amount..] + BEWordToBitSeq(x)[..amount];
    z
}

static function RightShift(x:int, amount:int) : int
    requires Word32(x);
    requires 0 <= amount < 32;
    ensures Word32(RightShift(x, amount));
{
    var z :| Word32(z) && forall i :: 0 <= i < 32 ==> 
    BEWordToBitSeq(z) == RepeatDigit(0, amount) + BEWordToBitSeq(x)[..32-amount];
    z
}

static function LeftShift(x:int, amount:int):int
    requires Word32(x);
    requires 0 <= amount < 32;
    ensures Word32(LeftShift(x, amount));
{
    var z :| Word32(z) && forall i :: 0 <= i < 32 ==> 
    BEWordToBitSeq(z) == BEWordToBitSeq(x)[amount..] + RepeatDigit(0, amount);
    z
}

static function Add32(x:int, y:int):int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(Add32(x, y));
{
    (x + y) % 0x100000000
}

*/

/*
//- Undefined.  Mapped to Boogie's word32
static function{:imported} word32(x:int):bool
static lemma{:imported} lemma_word32(x:int)
    ensures word32(x) <==> 0 <= x < 0x100000000;

static function{:imported} mod0x100000000(x:int):int
static lemma{:imported} lemma_mod0x100000000(x:int)
    ensures mod0x100000000(x) == x % 0x100000000;

static function{:imported} IntBit_spec(index:int, n:int):bool
static lemma{:imported} lemma_IntBit_spec(index:int, n:int)
    ensures IntBit_spec(index, n) == if (index > 0) then IntBit_spec(index - 1, n / 2) else n % 2 != 0;

static method{:imported} method_Mul(x:int, y:int) returns(r:int)
    ensures  r == x * y;

static method{:imported} method_Div(x:int, y:int) returns(r:int)
    requires y != 0;
    ensures  r == x / y;

static method{:imported} method_Mod(x:int, y:int) returns(r:int)
    requires y != 0;
    ensures  r == x % y;

static function method{:imported} asm_Add(x:int, y:int):int
    requires word32(x);
    requires word32(y);
    ensures word32(asm_Add(x, y));
    ensures asm_Add(x, y) == mod0x100000000(x + y);

static function method{:imported} asm_Sub(x:int, y:int):int
    requires word32(x);
    requires word32(y);
    ensures word32(asm_Sub(x, y));
    ensures asm_Sub(x, y) == mod0x100000000(x - y);

static function method{:imported} asm_Mul(x:int, y:int):int
    requires word32(x);
    requires word32(y);
    ensures word32(asm_Mul(x, y));
    ensures asm_Mul(x, y) == mod0x100000000(x * y);

static function method{:imported} asm_Div(x:int, y:int):int
    requires word32(x);
    requires word32(y);
    requires y > 0;
    ensures word32(asm_Div(x, y));
    ensures asm_Div(x, y) == mod0x100000000(x * y);

static function method{:imported} asm_Mod(x:int, y:int):int
    requires word32(x);
    requires word32(y);
    requires y > 0;
    ensures word32(asm_Mod(x, y));
    ensures asm_Mod(x, y) == x % y;

static function method{:imported} asm_LeftShift(x:int, amount:int):int
    requires word32(x);
    requires 0 <= amount < 32;
    ensures word32(asm_LeftShift(x, amount));
    ensures forall i {:trigger IntBit_spec(i, asm_LeftShift(x, amount))} :: 0 <= i < amount ==>  IntBit_spec(i, asm_LeftShift(x, amount)) == false;
    ensures forall i {:trigger IntBit_spec(i, asm_LeftShift(x, amount))} :: amount <= i < 32 ==> IntBit_spec(i, asm_LeftShift(x, amount)) == IntBit_spec(i - amount, x);

static function method{:imported} asm_RightShift(x:int, amount:int):int
    requires word32(x);
    requires 0 <= amount < 32;
    ensures word32(asm_RightShift(x, amount));
    ensures forall i {:trigger IntBit_spec(i, asm_RightShift(x, amount))} :: 0 <= i < 32 - amount ==>  IntBit_spec(i, asm_RightShift(x, amount)) == IntBit_spec(i + amount, x);
    ensures forall i {:trigger IntBit_spec(i, asm_RightShift(x, amount))} :: 32 - amount <= i < 32 ==> IntBit_spec(i, asm_RightShift(x, amount)) == false;

static function method{:imported} asm_RotateLeft(x:int, amount:int):int
    requires word32(x);
    requires 0 <= amount < 32;
    ensures word32(asm_RotateLeft(x, amount));
    ensures forall i {:trigger IntBit_spec(i, asm_RotateLeft(x, amount))} :: 0 <= i < amount ==>  IntBit_spec(i, asm_RotateLeft(x, amount)) == IntBit_spec(i + 32 - amount, x);
    ensures forall i {:trigger IntBit_spec(i, asm_RotateLeft(x, amount))} :: amount <= i < 32 ==> IntBit_spec(i, asm_RotateLeft(x, amount)) == IntBit_spec(i - amount, x);

static function method{:imported} asm_RotateRight(x:int, amount:int):int
    requires word32(x);
    requires 0 <= amount < 32;
    ensures word32(asm_RotateRight(x, amount));
    ensures forall i {:trigger IntBit_spec(i, asm_RotateRight(x, amount))} :: 0 <= i < 32 - amount ==>  IntBit_spec(i, asm_RotateRight(x, amount)) == IntBit_spec(i + amount, x);
    ensures forall i {:trigger IntBit_spec(i, asm_RotateRight(x, amount))} :: 32 - amount <= i < 32 ==> IntBit_spec(i, asm_RotateRight(x, amount)) == IntBit_spec(i + amount-32, x);

static function method{:imported} asm_BitwiseNot(x:int):int
    requires word32(x);
    ensures word32(asm_BitwiseNot(x));
    ensures forall i {:trigger IntBit_spec(i, asm_BitwiseNot(x))} :: 0 <= i < 32 ==> IntBit_spec(i, asm_BitwiseNot(x)) == !IntBit_spec(i, x);

static function method{:imported} asm_BitwiseAnd(x:int, y:int):int
    requires word32(x);
    requires word32(y);
    ensures word32(asm_BitwiseAnd(x, y));
    ensures forall i {:trigger IntBit_spec(i, asm_BitwiseAnd(x, y))} :: 0 <= i < 32 ==> IntBit_spec(i, asm_BitwiseAnd(x, y)) == (IntBit_spec(i, x) && IntBit_spec(i, y));

static function method{:imported} asm_BitwiseOr(x:int, y:int):int
    requires word32(x);
    requires word32(y);
    ensures word32(asm_BitwiseOr(x, y));
    ensures forall i {:trigger IntBit_spec(i, asm_BitwiseOr(x, y))} :: 0 <= i < 32 ==> IntBit_spec(i, asm_BitwiseOr(x, y)) == (IntBit_spec(i, x) || IntBit_spec(i, y));

static function method{:imported} asm_BitwiseXor(x:int, y:int):int
    requires word32(x);
    requires word32(y);
    ensures word32(asm_BitwiseXor(x, y));
    ensures forall i {:trigger IntBit_spec(i, asm_BitwiseXor(x, y))} :: 0 <= i < 32 ==> IntBit_spec(i, asm_BitwiseXor(x, y)) == (IntBit_spec(i, x) != IntBit_spec(i, y));

*/
