include "../Math/power.i.dfy"
include "integer_sequences.i.dfy"

//- "Premium" versions of {:autoReq} spec functions, which include
//- explicit requires and appropriate ensures for composition with
//- other functions.

static function BEDigitSeqToInt_premium(place_value:int, digits:seq<int>) : int
    requires 1<place_value;
    requires IsDigitSeq(place_value, digits);
    ensures 0 <= BEDigitSeqToInt(place_value, digits) < power(place_value, |digits|);
{
    lemma_BEDigitSeqToInt_bound(place_value, digits);
    BEDigitSeqToInt(place_value, digits)
}

static function BEBitSeqToInt_premium(bits:seq<int>) : int
    requires IsBitSeq(bits);
{
    BEBitSeqToInt(bits)
}

static function BEByteSeqToInt_premium(bytes:seq<int>) : int
    requires IsByteSeq(bytes);
{
    BEByteSeqToInt(bytes)
}

static function BEWordSeqToInt_premium(words:seq<int>) : int
    requires IsWordSeq(words);
    ensures 0<=BEWordSeqToInt(words);
{
    lemma_BEDigitSeqToInt_bound(power2(32), words);
    BEWordSeqToInt(words)
}

static lemma lemma_BEIntToDigitSeq_IsDigitSeq(place_value:int, min_places:int, v:int)
    requires 1<place_value;
    requires 0<=v;
    ensures IsDigitSeq(place_value, BEIntToDigitSeq(place_value, min_places, v));
    decreases if v>min_places then v else min_places;
//-    decreases if (v>0) then v else 0,min_places;
{
    var sq := BEIntToDigitSeq(place_value, min_places, v);

    reveal_BEIntToDigitSeq_private();
    if (0<v || 0<min_places)
    {
        assert sq == BEIntToDigitSeq_private(place_value, min_places-1, v/place_value)
            + [ v % place_value ];
        var v' := v/place_value;
        var mp' := min_places - 1;
        if (v>0)
        {
            lemma_div_decreases(v, place_value);
            lemma_div_pos_is_pos(v, place_value);
        }
        else
        {
            lemma_small_div();
        }
        lemma_BEIntToDigitSeq_IsDigitSeq(place_value, min_places-1, v/place_value);
        lemma_mod_properties();
    }
    else
    {
        assert |sq|==0;
    }
}

static function BEIntToDigitSeq_premium(place_value:int, min_places:int, v:int) : seq<int>
    requires 1<place_value;
    requires 0 <= v;
    ensures IsDigitSeq(place_value, BEIntToDigitSeq(place_value, min_places, v));
    ensures min_places <= |BEIntToDigitSeq(place_value, min_places, v)|;
    ensures (0<=min_places && v<power(place_value, min_places)) ==> |BEIntToDigitSeq(place_value, min_places, v)| == min_places;
{
    lemma_BEIntToDigitSeq_IsDigitSeq(place_value, min_places, v);
    lemma_BEIntToDigitSeq_properties(place_value, min_places, v);
    BEIntToDigitSeq(place_value, min_places, v)
}

//-////////////////////////////////////////////////////////////////////////////
//- Generator functions (as opposed to recognizer predicates)
//-////////////////////////////////////////////////////////////////////////////

static function BEIntToByteSeq_premium(x: int) : seq<int>
    requires 0 <= x;
    ensures IsByteSeq(BEIntToByteSeq(x));
    ensures BEByteSeqToInt(BEIntToByteSeq(x)) == x;
{
    reveal_power2();
    lemma_BEInt_decoding_general(power2(8), 0, x);
    BEIntToByteSeq(x)
}

//- Lost static tag because lemmas in seqs_transforms aren't static.

static function BEWordToFourBytes_premium(x: int) : seq<int>
    requires Word32(x);
    ensures IsByteSeq(BEWordToFourBytes(x));



{
    reveal_power2();
    calc {
        x;
        < power2(32);
            { lemma_power2_is_power_2(32); }
        power(2, 8*4);
            { lemma_mul_is_mul_boogie(8,4); lemma_power_multiplies(2,8,4); }
        power(power(2,8), 4);
            { lemma_power2_is_power_2(8); }
        power(power2(8), 4);
    }
    lemma_BEIntToDigitSeqProducesRightSizedDigits(power2(8), 4, x);
    
    BEWordToFourBytes(x)
}

static function BEWordToBitSeq_premium(x:int) : seq<int>
    requires Word32(x);
    ensures IsBitSeq(BEWordToBitSeq(x));
    ensures |BEWordToBitSeq(x)| == 32;
    ensures forall i :: 0 <= i < 32 ==> IsBit(BEWordToBitSeq(x)[i]);
    ensures BEBitSeqToInt(BEWordToBitSeq(x)) == x;
{
    reveal_power2();
    lemma_power2_is_power_2(1);
    calc {
        x;
        < power2(32);
            { lemma_power2_is_power_2(32); }
        power(2, 32);
        power(power2(1), 32);
    }
    lemma_BEIntToDigitSeqProducesRightSizedDigits(power2(1), 32, x);
    lemma_BEIntToDigitSeq_private_properties(power2(1), 32, x);
    lemma_BEIntToBitSeq_decoding(x);

    BEWordToBitSeq(x)
}

static function BEWordSeqToBitSeq_premium(wordseq:seq<int>) : seq<int>
    requires IsWordSeq(wordseq);
    ensures IsBitSeq(BEWordSeqToBitSeq(wordseq));
    ensures |BEWordSeqToBitSeq(wordseq)| == |wordseq|*32;


{
    lemma_BEWordSeqToBitSeq_ensures(wordseq);

    BEWordSeqToBitSeq(wordseq)
}

static function BEByteSeqToBitSeq_premium(byteseq:seq<int>) : seq<int>
    requires IsByteSeq(byteseq);
    ensures IsBitSeq(BEByteSeqToBitSeq(byteseq));
    ensures |BEByteSeqToBitSeq(byteseq)| == |byteseq|*8;
//-    ensures BEBitSeqToInt(BEByteSeqToBitSeq(byteseq)) == BEByteSeqToInt(byteseq);
{
    lemma_BEByteSeqToBitSeq_ensures(byteseq);
    
    BEByteSeqToBitSeq(byteseq)
}

static function BEWordSeqToByteSeq_premium(wordseq:seq<int>) : seq<int>
    requires IsWordSeq(wordseq);
    ensures IsByteSeq(BEWordSeqToByteSeq(wordseq));
    ensures |BEWordSeqToByteSeq(wordseq)| == |wordseq|*4;
//-    ensures BEByteSeqToInt(BEWordSeqToByteSeq(wordseq)) == BEWordSeqToInt(wordseq);
{
    lemma_BEWordSeqToByteSeq_ensures(wordseq);
    
    BEWordSeqToByteSeq(wordseq)
}

//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////

//- Two equal-valued DigitSeqs differ only by a zero prefix,
//- regardless of how they are constructed with BEIntToDigitSeq

static lemma lemma_equal_suffixes(pv:int, short:seq<int>, long:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, short);
    requires IsDigitSeq(pv, long);
    requires BEDigitSeqToInt_premium(pv, short) == BEDigitSeqToInt_premium(pv, long);
    requires |short| <= |long|;
    ensures forall i :: 0<=i<|long|-|short| ==> long[i] == 0;
    ensures forall i :: |long|-|short|<=i<|long| ==> long[i] == short[i - (|long|-|short|)];
    decreases |long|;
{
    reveal_BEDigitSeqToInt_private();
    var x := BEDigitSeqToInt_premium(pv, short);
    if (|short|==0)
    {
        if (|long|==0)
        {
        }
        else
        {
            assert BEDigitSeqToInt_premium(pv, short)==0;
            forall (i | 0<=i<|long|-|short|)
                ensures long[i] == 0;
            {
                if (i==|long|-1)
                {
                    calc {
                        0;
                        x;
                        BEDigitSeqToInt_premium(pv, long[0..|long|-1])*pv + long[|long|-1];
                    }
                    lemma_mul_nonnegative(BEDigitSeqToInt_premium(pv, long[0..|long|-1]), pv);
                    assert long[i] == 0;
                }
                else
                {
                    if (BEDigitSeqToInt_premium(pv, long[0..|long|-1])>0)
                    {
                        lemma_mul_strictly_positive(BEDigitSeqToInt_premium(pv, long[0..|long|-1]), pv);
                        assert false;
                    }
                    calc {
                        long[i];
                        long[0..|long|-1][i];
                            { lemma_equal_suffixes(pv, short, long[0..|long|-1]); }
                        0;
                    }
                }
            }
        }
    }
    else
    {
//-        assert x == BEDigitSeqToInt_premium(pv, short[0..|short|-1])*pv + short[|short|-1];
 //-       assert x == BEDigitSeqToInt_premium(pv, long[0..|long|-1])*pv + long[|long|-1];

        lemma_fundamental_div_mod_converse(x, pv, BEDigitSeqToInt_premium(pv, short[0..|short|-1]), short[|short|-1]);
        lemma_fundamental_div_mod_converse(x, pv, BEDigitSeqToInt_premium(pv, long[0..|long|-1]), long[|long|-1]);

        calc {
            BEDigitSeqToInt_premium(pv, short[0..|short|-1]);
            x/pv;
            BEDigitSeqToInt_premium(pv, long[0..|long|-1]);
        }
        calc {
            short[|short|-1];
            x%pv;
            long[|long|-1];
        }
//-        assert short[|short|-1] == long[|long|-1];
        lemma_equal_suffixes(pv, short[0..|short|-1], long[0..|long|-1]);

        forall (i | 0<=i<|long|-|short|)
            ensures long[i] == 0;
        {
            if (i==|long|-1)
            {
                assert long[i] == 0;
            }
            else
            {
                calc {
                    long[i];
                    long[0..|long|-1][i];
                        { lemma_equal_suffixes(pv, short[0..|short|-1], long[0..|long|-1]); }
                    0;
                }
                assert long[i] == 0;
            }
        }
        forall (i | |long|-|short|<=i<|long|)
            ensures long[i] == short[i - (|long|-|short|)];
        {
            if (i==|long|-1)
            {
                assert long[i] == short[i - (|long|-|short|)];
            }
            else
            {
                assert long[i] == short[i - (|long|-|short|)];
            }
        }
    }
}

//////////////////////////////////////////////////////////////////////////////




static lemma lemma_BEIntToDigitSeq_of_zero(pv:int, s:seq<int>)
    requires 1<pv;
    requires s == BEIntToDigitSeq_premium(pv, |s|, 0);
    ensures forall i :: 0<=i<|s| ==> s[i] == 0;
    decreases |s|;
{
    if (|s|==0)
    {
    }
    else if (s[0]==0)
    {
        calc {
            0;
                { lemma_BEInt_decoding_general(pv, |s|, 0); }
            BEDigitSeqToInt(pv, s);
                { lemma_LeadingZeros(pv, s[1..], s); }
            BEDigitSeqToInt(pv, s[1..]);
        }

        lemma_BEDigitSeqToInt_invertibility(pv, 0, s[1..]);
        assert s[1..] == BEIntToDigitSeq(pv, |s[1..]|, 0);
        //- recurse.
        lemma_BEIntToDigitSeq_of_zero(pv, s[1..]);
        forall (i | 0<=i<|s|)
            ensures s[i]==0;
        {
            if (i>0)
            {
                assert s[i] == s[1..][i-1];
            }
        }
    }
    else
    {
        lemma_BEInt_decoding_general(pv, |s|, 0);
        assert BEDigitSeqToInt(pv, s) == 0;
        lemma_BEDigitSeqToInt_bound(pv, s);
        calc {
            0;
            <
            s[0];
            <=  { lemma_power_positive(pv, |s|-1);
                  lemma_mul_increases(power(pv, |s|-1), s[0]); }
            power(pv, |s|-1) * s[0];
                { lemma_mul_is_commutative_forall(); }
            s[0] * power(pv, |s|-1);
            <= BEDigitSeqToInt(pv, s);
            0;
        }   
        assert false;
    }
}

static lemma lemma_BEDigitSeqToInt_of_zeros(pv:int, s:seq<int>)
    requires 1<pv;
    requires forall i :: 0<=i<|s| ==> s[i] == 0;
    ensures BEDigitSeqToInt(pv, s) == 0;
    decreases |s|;
{
    if (|s|==0)
    {
        reveal_BEDigitSeqToInt_private();
    }
    else
    {
        calc {
            BEDigitSeqToInt(pv, s);
                { reveal_BEDigitSeqToInt_private(); }
            BEDigitSeqToInt_private(pv, s[0..|s|-1])*pv + s[0];
                { lemma_BEDigitSeqToInt_of_zeros(pv, s[0..|s|-1]); }
            mul(0,pv) + s[0];
                { lemma_mul_basics_forall(); }
            0;
        }
    }
}
        
//////////////////////////////////////////////////////////////////////////////




static lemma lemma_select_from_transform(inseq:seq<int>, headseq:seq<int>, tailseq:seq<int>, outbits:nat, scale:nat, inbits:nat, crop:nat)
    requires IsDigitSeq(power2(inbits), inseq);
    requires IsDigitSeq(power2(inbits), inseq);
    requires IsDigitSeq(power2(inbits), headseq);
    requires IsDigitSeq(power2(inbits), tailseq);
    requires inseq == headseq + tailseq;
    requires 0<outbits;
    requires 0<inbits;
    requires 0<scale;
    requires outbits*scale == inbits;
    requires crop == |headseq|*scale;
    decreases |tailseq|;
    ensures 1<power2(outbits);
    ensures 1<power2(inbits);
    ensures
        var short := BEIntToDigitSeq_premium(power2(outbits), |headseq|*scale, BEDigitSeqToInt_premium(power2(inbits), headseq));
        var long := BEIntToDigitSeq_premium(power2(outbits), |inseq|*scale, BEDigitSeqToInt_premium(power2(inbits), inseq));
        crop <= |long|
        && short == long[..crop];
    
    
{
    lemma_power2_strictly_increases(0,outbits);
    lemma_power2_strictly_increases(0,inbits);
    lemma_mul_inequality(|headseq|, |inseq|, scale);

    var hsi := BEDigitSeqToInt_premium(power2(inbits), headseq);
    var tsi := BEDigitSeqToInt_premium(power2(inbits), tailseq);
    var hstsi := BEDigitSeqToInt_premium(power2(inbits), inseq);

    var hs := BEIntToDigitSeq_premium(power2(outbits), |headseq|*scale, hsi);
    var ts := BEIntToDigitSeq_premium(power2(outbits), |tailseq|*scale, tsi);
    var hsts := BEIntToDigitSeq_premium(power2(outbits), |inseq|*scale, hstsi);

    lemma_SeqTransformChop(inseq, headseq, tailseq, outbits, scale, inbits);

    assert BEIntToDigitSeq(power2(outbits), |headseq|*scale, BEDigitSeqToInt(power2(inbits), headseq))
        + BEIntToDigitSeq(power2(outbits), |tailseq|*scale, BEDigitSeqToInt(power2(inbits), tailseq))
        == BEIntToDigitSeq(power2(outbits), |inseq|*scale, BEDigitSeqToInt(power2(inbits), inseq));

    assert BEIntToDigitSeq(power2(outbits), |headseq|*scale, hsi)
        + BEIntToDigitSeq(power2(outbits), |tailseq|*scale, tsi)
        == BEIntToDigitSeq(power2(outbits), |inseq|*scale, hstsi);

    assert hs + ts == hsts;
    assert hsts[..|hs|] == hs;

    lemma_mul_nonnegative(|headseq|, scale);
    calc {
        hsi;
        <
        power(power2(inbits), |headseq|);
            { lemma_power2_is_power_2(inbits); }
        power(power(2,inbits), |headseq|);
            { lemma_power_multiplies(2, inbits, |headseq|); }
        power(2,inbits*|headseq|);
            { lemma_mul_is_commutative_forall();
              lemma_mul_is_associative_forall(); }
        power(2,outbits*(|headseq|*scale));
            { lemma_power_multiplies(2, outbits, |headseq|*scale); }
        power(power(2,outbits),|headseq|*scale);
            { lemma_power2_is_power_2(outbits); }
        power(power2(outbits),|headseq|*scale);
    }

    lemma_BEIntToDigitSeq_when_mp_dominates_x(power2(outbits), |headseq|*scale, hsi);
    assert |hs| == |headseq|*scale;
    calc {
        BEIntToDigitSeq_premium(power2(outbits), |headseq|*scale, BEDigitSeqToInt_premium(power2(inbits), headseq));
        BEIntToDigitSeq_premium(power2(outbits), |headseq|*scale, hsi);
        hs;
        hsts[..|hs|];
        BEIntToDigitSeq_premium(power2(outbits), |inseq|*scale, hstsi)[..|hs|];
        BEIntToDigitSeq_premium(power2(outbits), |inseq|*scale, hstsi)[..|headseq|*scale];
        BEIntToDigitSeq_premium(power2(outbits), |inseq|*scale, BEDigitSeqToInt_premium(power2(inbits), inseq))[..|headseq|*scale];
    }
}


