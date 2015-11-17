include "../Math/power2.s.dfy"
include "bytes_and_words.s.dfy"

//-////////////////////////////////////////////////////////////////////////////
//- Sequence types
//-////////////////////////////////////////////////////////////////////////////

static predicate IsDigitSeq(place_value:int, digits:seq<int>)
{
    forall i {:trigger digits[i]} :: 0<=i<|digits| ==> 0 <= digits[i] < place_value
}

static predicate IsBitSeq(bs:seq<int>)
{
    IsDigitSeq(power2(1), bs)
}

static predicate IsByteSeq(os:seq<int>)
{
    IsDigitSeq(power2(8), os)
}

static predicate IsWordSeq(ws:seq<int>)
{
    IsDigitSeq(power2(32), ws)
}

static predicate IsBitSeqOfLen(os:seq<int>, len:int)
{
    IsBitSeq(os) && |os| == len
}

static predicate IsByteSeqOfLen(os:seq<int>, len:int)
{
    IsByteSeq(os) && |os| == len
}

static predicate IsWordSeqOfLen(os:seq<int>, len:int)
{
    IsWordSeq(os) && |os| == len
}

//-////////////////////////////////////////////////////////////////////////////
//- Relationships among sequences of different digit sizes
//- (bit, byte, word, and ghost int)
//-////////////////////////////////////////////////////////////////////////////

//- BE/LE refers to the endianness of the transformation. There's no
//- inherent endianness in a sequence until it's interpreted.


static function {:opaque} BEDigitSeqToInt_private(place_value:int, digits:seq<int>) : int
    decreases |digits|;
{
    if (digits==[]) then
        0
    else
        
        
        BEDigitSeqToInt_private(place_value, digits[0..|digits|-1])*place_value + digits[|digits|-1]
}

static function BEDigitSeqToInt(place_value:int, digits:seq<int>) : int
    requires IsDigitSeq(place_value, digits);
{
    BEDigitSeqToInt_private(place_value, digits)
}

static function {:autoReq}BEBitSeqToInt(bits:seq<int>) : int
{
    BEDigitSeqToInt(power2(1), bits)
}

static function {:autoReq} BEByteSeqToInt(bytes:seq<int>) : int
{
    BEDigitSeqToInt(power2(8), bytes)
}

static function {:autoReq} BEWordSeqToInt(words:seq<int>) : int
{
    BEDigitSeqToInt(power2(32), words)
}




static function {:opaque} BEIntToDigitSeq_private(place_value:int, min_places:int, v:int) : seq<int>
    decreases if v>min_places then v else min_places;
{
    if (1<place_value && (0<v || 0<min_places)) then
        (/*call_lemma:*/ property_dafny_cant_see_about_div(v, place_value);
        BEIntToDigitSeq_private(place_value, min_places-1, v/place_value)
            + [ v % place_value ])
    else
        []
}








static lemma {:axiom} property_dafny_cant_see_about_div(n:int, d:int)
    requires 1<d;
    ensures 0<n ==> n/d < n;
    ensures n<=0 ==> n/d <= 0;

static function BEIntToDigitSeq(place_value:int, min_places:int, v:int) : seq<int>
{
        BEIntToDigitSeq_private(place_value, min_places, v)
}

//-////////////////////////////////////////////////////////////////////////////

static predicate BEDigitSeqEqInt(place_value:int, digits:seq<int>, v:int)
{
    IsDigitSeq(place_value, digits)
    && BEDigitSeqToInt(place_value, digits)==v
}

static predicate BEBitSeqEqInt(bitseq:seq<int>, v:int)
{
    BEDigitSeqEqInt(2, bitseq, v)
}

static predicate BEBitSeqEqByte(bitseq:seq<int>, byte:int)
{
    IsByte(byte) && BEBitSeqEqInt(bitseq, byte)
}

static predicate BEBitSeqEqWord(bitseq:seq<int>, word:int)
{
    IsWord(word) && BEBitSeqEqInt(bitseq, word)
}

static predicate BEByteSeqEqInt(byteseq:seq<int>, v:int)
{
    BEDigitSeqEqInt(256, byteseq, v)
}

static predicate BEByteSeqEqWord(byteseq:seq<int>, word:int)
{
    IsWord(word) && BEByteSeqEqInt(byteseq, word)
}

static predicate BEWordSeqEqInt(byteseq:seq<int>, v:int)
{
    BEDigitSeqEqInt(power2(32), byteseq, v)
}

static predicate BEBitSeqEqByteSeq(bitseq:seq<int>, byteseq:seq<int>)
{
    exists v:int ::
        BEBitSeqEqInt(bitseq, v) && BEByteSeqEqInt(byteseq, v)
}

static predicate BEBitSeqEqWordSeq(bitseq:seq<int>, wordseq:seq<int>)
{
    exists v:int ::
        BEBitSeqEqInt(bitseq, v) && BEWordSeqEqInt(wordseq, v)
}

static predicate BEByteSeqEqWordSeq(byteseq:seq<int>, wordseq:seq<int>)
{
    exists v:int ::
        BEByteSeqEqInt(byteseq, v) && BEWordSeqEqInt(wordseq, v)
}

//-////////////////////////////////////////////////////////////////////////////
//- Generator functions (as opposed to recognizer predicates)
//-////////////////////////////////////////////////////////////////////////////





//

static function BEIntToByteSeq(x: int) : seq<int>
{
    BEIntToDigitSeq(power2(8), 0, x)
}

static function BEWordToFourBytes(x: int) : seq<int>
    requires Word32(x);
{
    BEIntToDigitSeq(power2(8), 4, x)
}

static function BEWordToBitSeq(x:int) : seq<int>
{
    BEIntToDigitSeq(power2(1), 32, x)
}

static function {:autoReq} BEWordSeqToBitSeq(wordseq:seq<int>) : seq<int>
{
   BEIntToDigitSeq(power2(1), |wordseq|*32, BEDigitSeqToInt(power2(32), wordseq))
}

static function {:autoReq} BEByteSeqToBitSeq(byteseq:seq<int>) : seq<int>
{
    BEIntToDigitSeq(power2(1), |byteseq|*8, BEDigitSeqToInt(power2(8), byteseq))
}

static function {:autoReq} BEWordSeqToByteSeq(wordseq:seq<int>) : seq<int>
{
    BEIntToDigitSeq(power2(8), |wordseq|*4, BEDigitSeqToInt(power2(32), wordseq))
}

static function RepeatDigit(digit:int, count:int) : seq<int>
    decreases count;
{
    if (count<=0) then [] else RepeatDigit(digit, count-1) + [digit]
}

static function {:opaque} Reverse(os:seq<int>) : seq<int>
    decreases |os|;
{
    if (os==[]) then
        []
    else
        [os[|os|-1]] + Reverse(os[0..|os|-1])
}
