include "integer_sequences_premium.i.dfy"
include "../../Drivers/CPU/assembly_premium.i.dfy"
include "../Math/bit_vector_lemmas_premium.i.dfy"


//-------------------------------------------------------------------------

static lemma lemma_LeftShiftOfOneProperties(e: int)
    requires 0 <= e < 32;
    ensures Word32(1) && Word32(e);
    ensures |BEWordToBitSeq(LeftShift(1, e))| == 32;
    ensures BEWordToBitSeq(LeftShift(1, e)) == SequenceOfZeros(31-e) + [1] + SequenceOfZeros(e);
    ensures forall i :: 0 <= i < 32 ==> BEWordToBitSeq(LeftShift(1, e))[i] == if i == 31 - e then 1 else 0;
{
    lemma_2toX();
    reveal_power2();
    calc {
        BEWordToBitSeq(LeftShift(1, e));
        BEWordToBitSeq(Asm_LeftShift(1, e));
        { lemma_SequenceOfZerosIsRepeatDigitZero(e); }
        BEWordToBitSeq(1)[e..] + SequenceOfZeros(e);
        calc {
            BEWordToBitSeq(1);
            BEIntToDigitSeq(power2(1), 32, 1);
            {
                reveal_BEIntToDigitSeq_private();
                lemma_small_div();
                lemma_small_mod(1, 2);
            }
            BEIntToDigitSeq(power2(1), 31, 0) + [1];
            { lemma_BEIntToDigitSeq_private_zero(power2(1), 31); }
            SequenceOfZeros(31) + [1];
        }
        (SequenceOfZeros(31) + [1])[e..] + SequenceOfZeros(e);
        (SequenceOfZeros(e) + SequenceOfZeros(31-e) + [1])[e..] + SequenceOfZeros(e);
        SequenceOfZeros(31-e) + [1] + SequenceOfZeros(e);
    }

    forall i | 0 <= i < 32
        ensures BEWordToBitSeq(LeftShift(1, e))[i] == if i == 31 - e then 1 else 0;
    {
       if i < 31-e
       {
           calc {
               BEWordToBitSeq(LeftShift(1, e))[i];
               (SequenceOfZeros(31-e) + [1] + SequenceOfZeros(e))[i];
               (SequenceOfZeros(i+1) + SequenceOfZeros(31-e-i-1) + [1] + SequenceOfZeros(e))[i];
               0;                  
           }
       }
       else if i > 31-e {
           calc {
               BEWordToBitSeq(LeftShift(1, e))[i];
               (SequenceOfZeros(31-e) + [1] + SequenceOfZeros(e))[i];
               (SequenceOfZeros(31-e) + [1] + SequenceOfZeros(i-(31-e)) + SequenceOfZeros(31-i))[i];
               0;                  
           }
       }
    }
}

static lemma lemma_bits_of_power2(bs:seq<int>, c:nat)
    requires bs == [1] + SequenceOfZeros(c);
    ensures IsBitSeq(bs);
    ensures BEBitSeqToInt(bs) == power2(c);
    decreases c;
{
    reveal_BEDigitSeqToInt_private();
    lemma_power2_1_is_2();
    var L2 := 2;
    if (|bs|==1)
    {
        calc {
            BEBitSeqToInt(bs);
            BEDigitSeqToInt_private(power2(1), bs);
            BEDigitSeqToInt_private(power2(1), [])*L2 + 1;
                { lemma_mul_basics_forall(); }
            1;
                { lemma_power2_0_is_1(); }
            power2(c);
        }
    }
    else
    {
        var sm := [1] + SequenceOfZeros(c-1);
        assert bs[0..|bs|-1] == sm;
        assert bs[|bs|-1] == 0;
        calc {
            BEBitSeqToInt(bs);
            BEDigitSeqToInt_private(power2(1), bs);
            BEDigitSeqToInt_private(power2(1), sm)*L2 + 0;
                { lemma_bits_of_power2(sm, c-1); }
            power2(c-1)*L2;
                { reveal_power2(); lemma_mul_is_mul_boogie(power2(c-1),L2); }
            power2(c);
        }
        
    }
}

static lemma lemma_ComputePower2_is_power2(e:int, p2:int)
    requires 0 <= e < 32;
    requires Word32(p2);
    requires BEWordToBitSeq(p2) == SequenceOfZeros(31-e) + [1] + SequenceOfZeros(e);
    ensures p2 == power2(e);
{
    var normal_form := [1] + SequenceOfZeros(e);
    lemma_power2_1_is_2();
    var input_string := SequenceOfZeros(31-e) + normal_form;

    calc {
        p2;
        BEBitSeqToInt(BEWordToBitSeq_premium(p2));
            { assert input_string == SequenceOfZeros(31-e) + [1] + SequenceOfZeros(e); }
        BEBitSeqToInt(input_string);
        BEBitSeqToInt(SequenceOfZeros(31-e) + normal_form);
            { lemma_LeadingZeros(2, normal_form, SequenceOfZeros(31-e) + normal_form); }
        BEBitSeqToInt(normal_form);
            { lemma_bits_of_power2(normal_form, e); }
        power2(e);
    }
}

static function method ComputePower2(e:int) : int
    requires 0 <= e < 32;
    ensures Word32(1) && Word32(e);
    ensures |BEWordToBitSeq(ComputePower2(e))| == 32;
    ensures BEWordToBitSeq(ComputePower2(e)) == SequenceOfZeros(31-e) + [1] + SequenceOfZeros(e);
    ensures forall i :: 0 <= i < 32 ==> BEWordToBitSeq(ComputePower2(e))[i] == if i == 31 - e then 1 else 0;
    ensures ComputePower2(e) == power2(e);
{
    lemma_LeftShiftOfOneProperties(e);
    lemma_ComputePower2_is_power2(e, Asm_LeftShift(1, e));
    Asm_LeftShift(1, e)
}

//-------------------------------------------------------------------------

//-static function power2minus1_word(e:nat) : seq<int>
//-    requires 0 <= e <= 32;
//-{
//-    SequenceOfZeros(32-e) + RepeatDigit_premium(1, e)
//-}
//-
//-static lemma lemma_bits_of_power2minus1_word(bs:seq<int>, e:nat)
//-    requires 0 <= e < 32;
//-    ensures Word32(1) && Word32(e);
//-    ensures |BEWordToBitSeq(power2minus1_word(e))| == 32;
//-    ensures forall i :: 0 <= i < 32 ==> BEWordToBitSeq(power2minus1_word(e))[i] == if i < 32-e then 0 else 1;
//-{
//-}

static lemma lemma_bits_of_power2minus1(bs:seq<int>, c:nat)
    requires bs == RepeatDigit_premium(1, c);
    ensures IsBitSeq(bs);
    ensures BEBitSeqToInt(bs) == power2(c)-1;
    decreases c;
{
    reveal_BEDigitSeqToInt_private();
    lemma_power2_0_is_1();
    lemma_power2_1_is_2();
    var L2 := 2;
    if (|bs|==0)
    {
        calc {
            BEBitSeqToInt(bs);
            BEDigitSeqToInt_private(power2(1), bs);
            0;
            power2(c)-1;
        }
    }
    else
    {
        var sm := RepeatDigit(1, c-1);
        assert bs[0..|bs|-1] == sm;
        assert bs[|bs|-1] == 1;
        calc {
            BEBitSeqToInt(bs);
            BEDigitSeqToInt_private(power2(1), bs);
            BEDigitSeqToInt_private(power2(1), sm)*L2 + 1;
                { lemma_bits_of_power2minus1(sm, c-1); }
            (power2(c-1) - 1)*L2 + 1;
                { lemma_mul_is_mul_boogie(power2(c-1)-1,L2); }
            power2(c-1)*2 - 1;
                { reveal_power2(); }
            power2(c) - 1;
        }
        
    }
}

static lemma lemma_ComputePower2Minus1(e:int, p2m1:int)
    requires 0 <= e <= 32;
    requires p2m1 == power2(e)-1;
    ensures Word32(p2m1);
    ensures |BEWordToBitSeq_premium(p2m1)| == 32;
    ensures BEWordToBitSeq(p2m1) == RepeatDigit_premium(0, 32-e) + RepeatDigit_premium(1, e);
    ensures forall i :: 0 <= i < 32 ==> BEWordToBitSeq(p2m1)[i] == if i < 32-e then 0 else 1;
{
    lemma_power2_1_is_2();
    lemma_2toX();
    lemma_power2_increases(e, 32);
    //-assert p2m1 < power2(32);

    var tight := RepeatDigit_premium(1, e);
    lemma_bits_of_power2minus1(tight, e);
    assert BEBitSeqToInt(tight) == power2(e)-1;
    lemma_BEDigitSeqToInt_invertibility(2, p2m1, tight);
    assert BEIntToDigitSeq(2, e, p2m1) == tight;
    lemma_BEIntToDigitSeq_properties(2, 0, p2m1);
    if (e > |BEIntToDigitSeq_private(2, 0, p2m1)|)
    {
        calc {
            power2(e);
            >   { lemma_power2_strictly_increases(|BEIntToDigitSeq_private(2, 0, p2m1)|, e); }
            power2(|BEIntToDigitSeq_private(2, 0, p2m1)|);
                { lemma_power2_is_power_2(|BEIntToDigitSeq_private(2, 0, p2m1)|); }
            power(2, |BEIntToDigitSeq_private(2, 0, p2m1)|);
            >=
            p2m1 + 1;
            power2(e);
        }
    }
    assert e <= |BEIntToDigitSeq(2, 0, p2m1)|;
    lemma_BEIntToDigitSeq_mp_irrelevant(2, e, p2m1);
    assert BEIntToDigitSeq(2, 0, p2m1) == tight;
    calc {
        BEWordToBitSeq(p2m1);
        BEIntToDigitSeq(2, 32, p2m1);
            { lemma_zero_extension(2, 32, p2m1, tight); }
        RepeatDigit_premium(0, 32-|tight|) + tight;
        RepeatDigit_premium(0, 32-e) + tight;
    }
}

static function method ComputePower2Minus1_mostly(e:int) : int
    requires 0 <= e < 32;
    ensures Word32(1) && Word32(e);
    ensures |BEWordToBitSeq(ComputePower2Minus1_mostly(e))| == 32;
    ensures BEWordToBitSeq(ComputePower2Minus1_mostly(e)) == SequenceOfZeros(32-e) + RepeatDigit(1, e);
    ensures forall i :: 0 <= i < 32 ==> BEWordToBitSeq(ComputePower2Minus1_mostly(e))[i] == if i < 32-e then 0 else 1;
    ensures ComputePower2Minus1_mostly(e) == power2(e)-1;
{
    lemma_2toX();
    lemma_ComputePower2Minus1(e, ComputePower2(e)-1);
    ComputePower2(e)-1
}

static lemma lemma_0xffffffff_is_2to32minus1()
    ensures 0xffffffff == power2(32)-1;
{
    lemma_2toX();
}

static function method ComputePower2Minus1(e:int) : int
    requires 0 <= e < 32;
    ensures Word32(1) && Word32(e);
    ensures |BEWordToBitSeq(ComputePower2Minus1(e))| == 32;
    ensures BEWordToBitSeq(ComputePower2Minus1(e)) == SequenceOfZeros(32-e) + RepeatDigit(1, e);
    ensures forall i :: 0 <= i < 32 ==> BEWordToBitSeq(ComputePower2Minus1(e))[i] == if i < 32-e then 0 else 1;
    ensures ComputePower2Minus1(e) == power2(e)-1;
{
    lemma_0xffffffff_is_2to32minus1();
    if (e==32) then 0xffffffff else ComputePower2Minus1_mostly(e)
}

//-------------------------------------------------------------------------

static function GetWordBit(x: int, b: int) : int
    requires Word32(x);
    requires 0 <= b < 32;
    ensures IsBit(GetWordBit(x, b));
{
    BEWordToBitSeq_premium(x)[b]
}

static method UpdateBitOfWord(x: int, pos: int, value: int) returns (y: int)
    requires Word32(x);
    requires 0 <= pos < 32;
    requires IsBit(value);
    ensures Word32(y);
    ensures |BEWordToBitSeq(x)| == |BEWordToBitSeq(y)| == 32;
    ensures BEWordToBitSeq(y)[pos] == value;
    ensures forall i {:trigger BEWordToBitSeq(x)[i]}{:trigger BEWordToBitSeq(y)[i]} ::
                0 <= i < 32 && i != pos ==> BEWordToBitSeq(y)[i] == BEWordToBitSeq(x)[i];
{
    if value == 1
    {
        var y := Asm_BitwiseOr(x, ComputePower2(31-pos));
        forall i | 0 <= i < 32 && i != pos
            ensures BEWordToBitSeq(y)[i] == BEWordToBitSeq(x)[i];
        {
           calc {
               BEWordToBitSeq(y)[i];
               if BEWordToBitSeq(x)[i] == 1 || BEWordToBitSeq(ComputePower2(31-pos))[i] == 1 then 1 else 0;
               if BEWordToBitSeq(x)[i] == 1 || false then 1 else 0;
               if BEWordToBitSeq(x)[i] == 1 then 1 else 0;
               { reveal_power2(); }
               BEWordToBitSeq_premium(x)[i];
               BEWordToBitSeq(x)[i];
           }
        }
        return y;
    }
    else
    {
        var y := Asm_BitwiseAnd(x, Asm_BitwiseNot(ComputePower2(31-pos)));
        forall i | 0 <= i < 32 && i != pos
            ensures BEWordToBitSeq(y)[i] == BEWordToBitSeq(x)[i];
        {
           calc {
               BEWordToBitSeq(y)[i];
               if BEWordToBitSeq(x)[i] == 1 && BEWordToBitSeq(Asm_BitwiseNot(ComputePower2(31-pos)))[i] == 1 then 1 else 0;
               if BEWordToBitSeq(x)[i] == 1 && BEWordToBitSeq(ComputePower2(31-pos))[i] == 0 then 1 else 0;
               if BEWordToBitSeq(x)[i] == 1 then 1 else 0;
               { reveal_power2(); }
               BEWordToBitSeq_premium(x)[i];
               BEWordToBitSeq(x)[i];
           }
        }
        return y;
    }
}

//-------------------------------------------------------------------------

static method TruncateToByte(Value:int)
    returns (NewValue: int)
    requires Word32(Value);
    ensures IsByte(NewValue);
    ensures Word32(0xff);
    ensures NewValue == Asm_BitwiseAnd(Value, 0xff);    //- Help SymDiff out
{
    lemma_2toX();
    lemma_and_with_ff_premium();

    NewValue := Asm_BitwiseAnd(Value, 0xff);
}

static method TruncateToWord16(Value:int)
    returns (NewValue: int)
    requires Word32(Value);
    ensures Word16(NewValue);
    ensures Word32(0xffff);
    ensures NewValue == Asm_BitwiseAnd(Value, 0xffff);  //- Help SymDiff out
{
    lemma_2toX();
    lemma_and_with_ffff_premium();

    NewValue := Asm_BitwiseAnd(Value, 0xffff);
}
