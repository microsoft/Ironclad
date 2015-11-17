include "BigNatCompare.i.dfy"
include "BigNatBitCount.i.dfy"
include "../Crypto/RandomNumberGen.s.dfy"
include "BigNumBEAdaptor.i.dfy"
include "BigNatBitwise.i.dfy"
include "../../Drivers/TPM/tpm-wrapper.i.dfy"


static predicate CandidateSeedWorksheetValid_precondition(worksheet:CandidateSeedWorksheet)
{
    0 < |worksheet.rows|
}

static method truncate_high_zeros(ws:seq<int>) returns (ts:seq<int>)
    decreases |ws|;
    ensures |ts| <= |ws|;
    ensures forall i:nat :: i<|ts| ==> ws[i]==ts[i];
    ensures 0<|ts| ==> ts[|ts|-1] != 0;
{
    var n := |ws|;
    while (n > 0)
        invariant 0 <= n <= |ws|;
        invariant forall i :: n <= i < |ws| ==> ws[i] == 0;
        decreases n;
    {
        n := n - 1;
        if (ws[n] != 0)
        {
            ts := ws[0..n+1];
            return;
        }
    }
    ts := [];
}

method BigNatRandomPower2(c:nat) returns (R:BigNat, ghost randoms:seq<int>)
    requires Word32(c);
    requires TPM_ready();
    ensures WellformedBigNat(R);
    ensures I(R) < power2(c);
    ensures |randoms| == DivideRoundingUp(c, 8);
    ensures IsByteSeq(randoms);
    ensures I(R) == BEByteSeqToInt(randoms) % power2(c);
    ensures TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPMs_match_except_for_randoms(old(TPM), TPM);
    ensures old(TPM).random_index <= TPM.random_index;
    ensures randoms == TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index);
{
    lemma_2to32();
    var full_bytes,extra_bits := Divide32(c, 8);
    assert full_bytes*8+extra_bits == c;
    var byte_count := full_bytes;
    if (extra_bits > 0)
    {
        //- pluck an extra byte to get the extra bits from
        byte_count := full_bytes + 1;
    }
    lemma_mod_pos_bound(extra_bits, 8);
    assert c == full_bytes*8+extra_bits;
    lemma_fundamental_div_mod_converse(c, 8, full_bytes, extra_bits);
    ghost var L8 := 8;
    assert full_bytes == c/L8;
    assert extra_bits == c%L8;

    calc {
        DivideRoundingUp_premium(c, 8);
        { lemma_div_is_div_boogie(c+7, 8); }
        (c+7)/8;
        (c-1)/8 + 1;
    }

    calc {
        (c-1)/8 + 1;
            { lemma_hoist_over_denominator(c-1, 1, 8); }
        (c-1+1*8)/8;
        (c+7)/8;
    }
    if (extra_bits==0)
    {
        calc {
            byte_count;
            full_bytes;
            c/L8;
                { lemma_round_down(c, 7, 8); }
            (L8*((c+7)/L8))/L8;
            {
                lemma_hoist_over_denominator(0, (c+7)/L8, L8);
                lemma_mul_is_commutative_forall();
            }
            div(0,L8) + (c+7)/L8;
                { lemma_div_basics(L8); }
            (c+7)/L8;
                { lemma_div_is_div_boogie(c+7,8); }
            (c+7)/8;
            (c-1)/8+1;
        }
    }
    else
    {
        calc {
            byte_count;
            full_bytes+1;
            c/L8+1;
            {
                calc {
                    c - c%L8;
                    c - extra_bits;
                    <=
                    c-1;
                }
                lemma_mod_properties();
                assert c-1 < c + L8 - c%L8;
                if (c<L8)
                {
                    lemma_small_mod(c,L8);
                    assert 0 <= c-c%L8;
                }
                else
                {
                    lemma_mod_properties();
                    assert 0 <= c-c%L8;
                }
                lemma_indistinguishable_quotients(c, c-1, 8);
            }
            (c-1)/L8+1;
                { lemma_div_is_div_boogie(c-1,8); }
            (c-1)/8+1;
        }
    }
    var byte_seq := get_random(byte_count);
//-    assert byte_count<power2(29);
//-    assert |byte_seq|<power2(29);
    randoms := byte_seq;
    assert |randoms| == byte_count == (c-1)/8+1;
    var word_seq,padding := BEByteSeqToWordSeq_impl(byte_seq);
    var trim_seq := TrimLeadingZeros(4294967296, word_seq);
    var le_seq := ReverseDigitSeq(4294967296, trim_seq);
    lemma_Reverse(trim_seq, le_seq);
    R := BigNat_ctor(le_seq);
    assert WellformedBigNat(R);
    calc {
        I(R);
            { lemma_BigNatIIsLEDigitSeqToInt(R); }
        LEDigitSeqToInt(Width(), le_seq);
            { lemma_Reverse_converts_endianness(Width(), trim_seq, le_seq); }
        BEDigitSeqToInt(Width(), trim_seq);
        BEDigitSeqToInt(Width(), word_seq);
        BEDigitSeqToInt(Width(), word_seq);
        BEByteSeqToInt(randoms);
    }

    
    
    
    
    
    R := BitwiseMask(R, c);
    assert I(R) == BEByteSeqToInt(randoms) % power2(c);
    lemma_mod_properties();
    assert I(R) < power2(c);
}

static predicate CandidateSeedWorksheetValid_incremental(req:SelectRandomRequest, worksheet:CandidateSeedWorksheet, last_succeeds:bool)
{
    (forall i :: 0<=i<|worksheet.rows| ==> CandidateSeedWorksheetRowValid(req, worksheet.rows[i]))
    //- all but last row fail
    && (forall i:int :: 0<=i<|worksheet.rows|-1 ==> !worksheet.rows[i].accepted)
    //- last as specified
    && (|worksheet.rows|>0 ==>
            worksheet.rows[|worksheet.rows|-1].accepted == last_succeeds)
    //- randoms properly accounted for
    && CandidateSeedWorksheetConsumesRandoms(worksheet.rows) == worksheet.randoms
}

method BigNatRandomFromInclusiveRange(L:BigNat, H:BigNat, ghost req:SelectRandomRequest) returns (R:BigNat, ghost worksheet:CandidateSeedWorksheet)
    requires WellformedBigNat(L);
    requires ModestBigNatWords(H);
    requires I(L) <= I(H);
    requires req.l == I(L);
    requires req.h == I(H);
    requires SelectRandomRequestValid(req);
    requires TPM_ready();
    ensures TPM_ready();
    ensures WellformedBigNat(R);
    ensures I(L) <= I(R) <= I(H);
    ensures CandidateSeedWorksheetValid(req, worksheet);
    ensures I(R) == CandidateSeedWorksheetOutput(worksheet);
    modifies this`TPM;   
    modifies this`IoMemPerm;
    ensures TPMs_match_except_for_randoms(old(TPM), TPM);
    ensures old(TPM).random_index <= TPM.random_index;
    ensures worksheet.randoms == TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index);
{
    var c:nat := BigNatCountBits(H);

    lemma_bit_count_is_unique(I(H), c, req.h_bits);
        
    var lobound:bool := false;
    var hibound:bool := false;

    ghost var randoms;
    worksheet := CandidateSeedWorksheet_c([], []);

    ghost var started := false;
    R := L; //- dafnycc: initialize variable
    var accepted := false;
    while (!accepted)
        decreases *;    //- Possibly doesn't terminate.
        invariant started ==> WellformedBigNat(R);
        invariant started ==> lobound == (I(L)<=I(R));
        invariant started ==> hibound == (I(R)<=I(H));
        invariant started ==> 0<|worksheet.rows|;
        invariant accepted ==> started;
        invariant CandidateSeedWorksheetValid_incremental(req, worksheet, accepted);
        invariant accepted ==> CandidateSeedWorksheetOutput(worksheet) == I(R);
        invariant TPM_ready();
        invariant TPMs_match_except_for_randoms(old(TPM), TPM);
        invariant old(TPM).random_index <= TPM.random_index;
        invariant worksheet.randoms == TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index);
        invariant TPM.random_index - old(TPM).random_index == |worksheet.randoms|;
    {
        R,randoms := BigNatRandomPower2(c);
        lobound := BigNatLe(L, R);
        hibound := BigNatLe(R, H);
        started := true;
        accepted := lobound && hibound;

        ghost var row := CandidateSeedWorksheetRow_c(I(R), accepted, randoms);
        ghost var worksheet' := CandidateSeedWorksheet_c(
            worksheet.rows + [row],
            worksheet.randoms + randoms);
        lemma_random_comprehension(old(TPM).random_index, worksheet.randoms, randoms);

        worksheet := worksheet';
    }
}
