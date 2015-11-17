include "BigNatCore.i.dfy"
include "BigNatBitCount.i.dfy"
include "BigNatCompare.i.dfy"
include "BigNumBEAdaptor.i.dfy"
include "../Math/BitwiseOperations.i.dfy"
include "../Util/word_bits.i.dfy"
include "../Util/arrays_2.i.dfy"

static lemma lemma_SelectBitWord(b:nat, M:seq<int>)
    requires b<|M|*32;
    requires IsWordSeq(M);
    ensures 0 <= b/32 < |M|;
    ensures SelectBit(b, BEWordSeqToInt_premium(M)) == SelectBit(b%32, M[|M|-1-b/32]);
{
    ghost var m := BEWordSeqToInt_premium(M);
    ghost var br := (b/32)*32;
    lemma_div_pos_is_pos(m, power2(br));
    calc {
        SelectBit(b, m);
            { lemma_SelectBit_div(b, m, br); }
        SelectBit(b-br, m / power2(br));
        SelectBit(b%32, m / power2(br));
        {
            lemma_SelectBit_mod(b%32, m/power2(br), 32);
            lemma_mod_pos_bound(m / power2(br), power2(32));
        }
        SelectBit(b%32, (m / power2(br)) % power2(32));
            { lemma_BEWordSeq_extract(M, b/32); }
        SelectBit(b%32, M[|M|-1-b/32]);
    }
}

static method BEBitwiseMask(X:seq<int>, c:nat) returns (M:seq<int>)
    requires IsWordSeq(X);
//-    requires |X| < power2(32);  //- if we want to avoid runtime overflow
    requires Word32(c);
    ensures IsWordSeq(M);
    ensures PureBitwiseAnd(BEWordSeqToInt_premium(X), power2(c)-1) == BEWordSeqToInt(M);
{
    ghost var mask_index := (|X|*32-(1+c))/32;
    var use_mask_index;
    var nonnegative_mask_index;
    if (|X|*32 < 1+c)
    {
        use_mask_index := false;
        nonnegative_mask_index := 0;
    }
    else
    {
        use_mask_index := true;
        nonnegative_mask_index := (|X|*32-(1+c))/32;
    }
    assert use_mask_index ==> nonnegative_mask_index == mask_index;
    assert 0<=nonnegative_mask_index;

    M := [];
    var i:=0;
    lemma_power2_increases(c%32,32);
    ghost var mask := power2(c)-1;
    ghost var x := BEWordSeqToInt_premium(X);
    assert IsWordSeq(RepeatDigit_premium(0,|X|-|M|));

    while (i<|X|)
        invariant |M|==i;
        invariant i<=|X|;
//-        invariant forall i::0<=i<|M|
//-            ==> M[i] == if i==mask_index then Asm_BitwiseAnd(X[i], power2(c%32)-1) else X[i];
        invariant IsWordSeq(M);
        invariant IsWordSeq(M + RepeatDigit(0,|X|-|M|));
        invariant forall b:: ((|X|-|M|)*32 <= b < |X|*32)
            ==> (SelectBit(b, BEWordSeqToInt_premium(M + RepeatDigit(0,|X|-|M|))) ==
                (if b<c then SelectBit(b, x) else false));
    {
        var nextword;
        if (use_mask_index && i<nonnegative_mask_index)
        {
            nextword := 0;
        }
        else if (use_mask_index && i==nonnegative_mask_index)
        {
            var residue := c%32;
            var word_mask := ComputePower2(residue) - 1;
            calc {
                word_mask;
                power2(residue)-1;
                < power2(residue);
                <=  { lemma_power2_increases(residue, 32); }
                power2(32);
            }
            nextword := Asm_BitwiseAnd(X[i], word_mask);
        }
        else
        {
            nextword := X[i];
        }
        var M' := M + [nextword];

        ghost var PM := M + RepeatDigit_premium(0,|X|-|M|);
        ghost var pm := BEWordSeqToInt_premium(PM);
        ghost var PM' := M' + RepeatDigit_premium(0,|X|-|M'|);
        ghost var pm' := BEWordSeqToInt_premium(PM');
        ghost var residue := c%32;
        ghost var word_mask := ComputePower2(residue) - 1;

        //- b is "bit number" in pure int land; b==0 is X%2.
        forall (b | (|X|-|M'|)*32 <= b < |X|*32)
            ensures SelectBit(b, pm') == if b<c then SelectBit(b, x) else false;
        {
            assert |X| == |PM'|;
            ghost var wordi := |X| - 1 - b/32;
            ghost var br := 32*(b/32);
            if (wordi < |M|)
            {
                assert PM'[wordi] == PM[wordi];
                //- Induction hypothesis.
                lemma_SelectBitWord(b, PM');
                lemma_SelectBitWord(b, PM);
                assert SelectBit(b, pm') == if b<c then SelectBit(b, x) else false;
            }
            else
            {
                //- This is the new word we just computed.
                if (wordi < mask_index)
                {
                    assert b>=c;
                    //- ...and we're off the top of the mask.
                    calc {
                        SelectBit(b, pm');
                            { lemma_SelectBitWord(b, PM'); }
                        SelectBit(b%32, PM'[wordi]);
                        SelectBit(b%32, 0);
                        (div(0,power2(b%32))) % 2 == 1;
                            { lemma_div_basics(power2(b%32)); }
                        0 == 1;
                        false;
                        if (b<c) then SelectBit(b, x) else false;
                    }
                }
                else if (wordi == mask_index)
                {
                    //- And it's the word where the mask is "interesting"
                    //- (has both zeros and ones)
                    assert i == wordi;
                    assert i == mask_index;
                    assert nextword == Asm_BitwiseAnd(X[wordi], word_mask);
                    lemma_Asm_BitwiseAnd_is_PureBitwiseAnd(X[wordi], word_mask);
                    assert PureBitwiseAnd(X[wordi], word_mask) == nextword;
                    lemma_BitwiseAnd_equivalence(X[wordi], word_mask, nextword);
                    assert BitwiseAndPredicate(X[wordi], word_mask, nextword);
                    assert SelectBit(b%32, nextword) == 
                        (SelectBit(b%32, X[wordi]) && SelectBit(b%32, word_mask));
                    
                    assert b >= (|X|-|M'|)*32;
                    calc {
                        SelectBit(b, pm');
                            { lemma_SelectBitWord(b, PM'); }
                        SelectBit(b%32, PM'[wordi]);
                        SelectBit(b%32, nextword);
                        SelectBit(b%32, X[wordi]) && SelectBit(b%32, word_mask);
                            { lemma_SelectBitWord(b, X); }
                        SelectBit(b, x) && SelectBit(b%32, word_mask);
                            { lemma_mask_structure(c%32, b%32); }
                        SelectBit(b, x) && (b%32<c%32);
                        SelectBit(b, x) && (b<c);
                        if (b<c) then SelectBit(b, x) else false;
                    }
                }
                else
                {
                    //- ...and we're in the bottom (1-bits) of the mask.
                    assert b<c;
                    calc {
                        SelectBit(b, pm');
                            { lemma_SelectBitWord(b, PM'); }
                        SelectBit(b%32, PM'[wordi]);
                        SelectBit(b%32, X[i]);
                            { lemma_SelectBitWord(b, X); }
                        SelectBit(b, x);
                        if (b<c) then SelectBit(b, x) else false;
                    }

                }
            }
        }
        assert forall b:: ((|X|-|M'|)*32 <= b < |X|*32)
            ==> (SelectBit(b, BEWordSeqToInt_premium(M' + RepeatDigit(0,|X|-|M'|))) ==
                (if b<c then SelectBit(b, x) else false));

        M := M';
//-        assert i<power2(32)-1;    // TODO reinstate if we do modesty checking
        i := i + 1;
    }
    ghost var m := BEWordSeqToInt_premium(M);
    forall (b:nat)
        ensures (SelectBit(b, x) && SelectBit(b, mask)) == SelectBit(b, m);
    {
        lemma_mask_structure(c, b);
        assert M == M + [];
        if (b>=|X|*32)
        {
            lemma_BEWordSeqToInt_bound(M);
            lemma_power2_increases(|X|*32, b);
            lemma_SelectBit_overflow(b,m);
            lemma_BEWordSeqToInt_bound(X);
            lemma_SelectBit_overflow(b,x);
        }
        else if (b<c)
        {
        }
        else
        {
        }
    }
    lemma_BitwiseAnd_equivalence(x, mask, m);
}

static method BitwiseMask(X:BigNat, c:nat) returns (M:BigNat)
    requires WellformedBigNat(X);
//-    requires ModestBigNatWords(X);    // tighten up to |X.words|<2^32?
    requires Word32(c);
    ensures WellformedBigNat(M);
    ensures I(M) == PureBitwiseAnd(I(X), power2(c)-1);
    ensures I(M) == I(X) % power2(c);
{
    lemma_2toX();
    
    
    
    var beX := ReverseDigitSeq(4294967296, X.words);
    lemma_Reverse(X.words, beX);
    lemma_power2_strictly_increases(26,32);
    var beM := BEBitwiseMask(beX, c);
    var betrim := TrimLeadingZeros(4294967296, beM);
    var leM := ReverseDigitSeq(4294967296, betrim);
    lemma_Reverse(betrim, leM);
    M := BigNat_ctor(leM);
    
    calc {
        I(M);
        {
            lemma_Reverse_converts_endianness(Width(), betrim, M.words);
            lemma_BigNatIIsLEDigitSeqToInt(M);
        }
        BEWordSeqToInt(betrim);
        BEWordSeqToInt(beM);
        PureBitwiseAnd(BEWordSeqToInt(beX), power2(c)-1);
        {
            lemma_Reverse_symmetry(beX, X.words);
            lemma_Reverse_converts_endianness(Width(), beX, X.words);
            lemma_BigNatIIsLEDigitSeqToInt(X);
        }
        PureBitwiseAnd(I(X), power2(c)-1);
    }
    calc {
        PureBitwiseAnd(I(X), power2(c)-1);
            { lemma_and_mask(I(X), c); }
        I(X) % power2(c);
    }
}









//






//



























//        










//






//






//














































//




