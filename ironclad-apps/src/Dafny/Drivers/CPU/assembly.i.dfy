//-<NuBuild BasmEnableSymdiff true />
include "../../Libraries/base.s.dfy"
include "../../Libraries/Util/relational.s.dfy"
//-include "assembly.s.dfy"

//-//////////////////////////////////////////////////////
//-  You should never need to call these!  Please use the 
//-  routines in assembly_premium.i.dfy instead.
//-  DafnyCC connects these methods to the underlying
//-  Boogie spec for the corresponding assembly 
//-  instructions.  Please do not change them, unless
//-  you also change the underlying Boogie spec.  If
//-  you need more properties, add them to the Premium
//-  versions in assembly_premium.dfy
//-//////////////////////////////////////////////////////

static function {:imported} IntBit(index:int, val:int):bool
static lemma{:decl} lemma_IntBit(index:int, val:int)
    ensures word32(val) && 0 <= index < 32 ==> 
            IntBit(index, val) == if (index < 31) then IntBit(index + 1, val / 2) else val % 2 != 0;

//- Undefined.  Mapped to Boogie's word32
static function{:imported} word32(x:int):bool
static lemma{:decl} lemma_word32(x:int)
    ensures word32(x) <==> 0 <= x < 0x100000000;

static function{:imported} mod0x100000000(x:int):int
static lemma{:decl} lemma_mod0x100000000(x:int)
    ensures mod0x100000000(x) == x % 0x100000000;

static method{:decl}{:dafnycc_heap_unmodified}{:instruction "out@EDX", "inout@EAX", "in"}{:strict_operands} method_Mul(x:int, y:int) returns(hi:int, r:int)
    ensures  r == x * y;

static method{:decl}{:dafnycc_heap_unmodified}{:instruction "inout@EDX", "inout@EAX", "in"}{:strict_operands} method_DivMod(zero:int, x:int, y:int) returns(m:int, d:int)
    requires zero == 0;
    requires y != 0;
    ensures  d == x / y;
    ensures  m == x % y;

static function method{:imported}{:instruction "inout", "in"} asm_Add(x:int, y:int):int
    requires word32(x);
    requires word32(y);
    ensures word32(asm_Add(x, y));
    ensures asm_Add(x, y) == mod0x100000000(x + y);

static function method{:imported}{:instruction "inout", "in"} asm_Sub(x:int, y:int):int
    requires word32(x);
    requires word32(y);
    ensures word32(asm_Sub(x, y));
    ensures asm_Sub(x, y) == mod0x100000000(x - y);

static function method{:imported} asm_Mul(x:int, y:int):int
    requires word32(x);
    requires word32(y);
    ensures word32(asm_Mul(x, y));
    ensures asm_Mul(x, y) == mod0x100000000(x * y);

static method{:imported}{:instruction "out@EDX", "inout@EAX", "in"}{:strict_operands} asm_Mul64(x:int, y:int) returns (hi:int, lo:int)
    requires word32(x);
    requires word32(y);
    ensures word32(hi);
    ensures word32(lo);
    ensures lo == mod0x100000000(x * y);
    ensures hi == (x * y) / 0x100000000;

static function method{:imported} asm_Div(x:int, y:int):int
    requires word32(x);
    requires word32(y);
    requires y > 0;
    ensures word32(asm_Div(x, y));
    ensures asm_Div(x, y) == mod0x100000000(x / y);

static function method{:imported} asm_Mod(x:int, y:int):int
    requires word32(x);
    requires word32(y);
    requires y > 0;
    ensures word32(asm_Mod(x, y));
    ensures asm_Mod(x, y) == x % y;

static function method{:imported}{:instruction "inout", "in@ECX"} asm_LeftShift(x:int, amount:int):int
    requires word32(x);
    requires 0 <= amount < 32;
    ensures word32(asm_LeftShift(x, amount));
    ensures forall i {:trigger IntBit(i, asm_LeftShift(x, amount))} :: 32 - amount <= i < 32 ==>  IntBit(i, asm_LeftShift(x, amount)) == false;
    ensures forall i {:trigger IntBit(i, asm_LeftShift(x, amount))} :: 0 <= i < 32 - amount ==> IntBit(i, asm_LeftShift(x, amount)) == IntBit(i + amount, x);

static function method{:imported}{:instruction "inout", "in@ECX"} asm_RightShift(x:int, amount:int):int
    requires word32(x);
    requires 0 <= amount < 32;
    ensures word32(asm_RightShift(x, amount));
    ensures forall i {:trigger IntBit(i, asm_RightShift(x, amount))} :: 0 <= i < amount ==> IntBit(i, asm_RightShift(x, amount)) == false;            
    ensures forall i {:trigger IntBit(i, asm_RightShift(x, amount))} :: amount <= i < 32 ==> IntBit(i, asm_RightShift(x, amount)) == IntBit(i - amount, x);            

static function method{:imported}{:instruction "inout", "in@ECX"} asm_RotateLeft(x:int, amount:int):int
    requires word32(x);
    requires 0 <= amount < 32;
    ensures word32(asm_RotateLeft(x, amount));
    ensures forall i {:trigger IntBit(i, asm_RotateLeft(x, amount))} :: 0 <= i < 32 - amount ==> IntBit(i, asm_RotateLeft(x, amount)) == IntBit(i + amount, x);
    ensures forall i {:trigger IntBit(i, asm_RotateLeft(x, amount))} :: 32 - amount <= i < 32 ==> IntBit(i, asm_RotateLeft(x, amount)) == IntBit(i - (32 - amount), x);         

static function method{:imported}{:instruction "inout", "in@ECX"} asm_RotateRight(x:int, amount:int):int
    requires word32(x);
    requires 0 <= amount < 32;
    ensures word32(asm_RotateRight(x, amount));
    ensures forall i {:trigger IntBit(i, asm_RotateRight(x, amount))} :: 0 <= i < amount ==>  IntBit(i, asm_RotateRight(x, amount)) == IntBit((32 - amount)+i, x);
    ensures forall i {:trigger IntBit(i, asm_RotateRight(x, amount))} :: amount <= i < 32 ==> IntBit(i, asm_RotateRight(x, amount)) == IntBit(i - amount, x);

static function method{:imported}{:instruction "inout"} asm_BitwiseNot(x:int):int
    requires word32(x);
    ensures word32(asm_BitwiseNot(x));
    ensures forall i {:trigger IntBit(i, asm_BitwiseNot(x))} :: 0 <= i < 32 ==> IntBit(i, asm_BitwiseNot(x)) == !IntBit(i, x);

static function method{:imported}{:instruction "inout", "in"} asm_BitwiseAnd(x:int, y:int):int
    requires word32(x);
    requires word32(y);
    ensures word32(asm_BitwiseAnd(x, y));
    ensures forall i {:trigger IntBit(i, asm_BitwiseAnd(x, y))} :: 0 <= i < 32 ==> IntBit(i, asm_BitwiseAnd(x, y)) == (IntBit(i, x) && IntBit(i, y));

static function method{:imported}{:instruction "inout", "in"} asm_BitwiseOr(x:int, y:int):int
    requires word32(x);
    requires word32(y);
    ensures word32(asm_BitwiseOr(x, y));
    ensures forall i {:trigger IntBit(i, asm_BitwiseOr(x, y))} :: 0 <= i < 32 ==> IntBit(i, asm_BitwiseOr(x, y)) == (IntBit(i, x) || IntBit(i, y));

static function method{:imported}{:instruction "inout", "in"} asm_BitwiseXor(x:int, y:int):int
    requires word32(x);
    requires word32(y);
    ensures word32(asm_BitwiseXor(x, y));
    ensures forall i {:trigger IntBit(i, asm_BitwiseXor(x, y))} :: 0 <= i < 32 ==> IntBit(i, asm_BitwiseXor(x, y)) == (IntBit(i, x) != IntBit(i, y));

static method{:decl} asm_Rdtsc() returns (high:int, low:int)
    ensures word32(high);
    ensures word32(low);

method{:decl} asm_declassify_result(concrete:int, ghost result:int) returns (pub_result:int)
    requires word32(concrete);
    requires relation(declassified(left(result), right(result), left(concrete), right(concrete)));
    ensures pub_result == result;
    ensures public(pub_result);

static method{:decl} GetBootloaderArgWord(index:int) returns (word:int)
    requires 0 <= index < 256;
    ensures  word32(word);
