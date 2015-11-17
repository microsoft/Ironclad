include "../Math/power2.s.dfy"

static predicate IsBit(b:int)
{
    0 <= b < 2
}

static predicate IsByte(b:int)
{
    0 <= b < 256
}

//


//
static predicate Word16(x:int)
{
    0 <= x < 0x10000
}

static predicate Word32(x: int)
{
    0 <= x < power2(32)
}

//

//

static predicate IsWord(w: int)
{
    Word32(w)
}
