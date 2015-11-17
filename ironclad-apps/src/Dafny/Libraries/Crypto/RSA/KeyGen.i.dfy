include "KeyGen.s.dfy"
include "MillerRabin.i.dfy"




static predicate PrimeGenerationWorksheetValid_precondition(worksheet:PrimeGenerationWorksheet)
{
    0 < |worksheet.rows|
//-    && CandidateSeedWorksheetValid_precondition(worksheet.rows[|worksheet.rows|-1].candidate)
}

static predicate PrimeGenerationWorksheetValid_incremental(keybits:int, worksheet:PrimeGenerationWorksheet, last_succeeds:bool)
    requires 0<keybits;
{
    //- each row locally valid
    (forall i :: 0<=i<|worksheet.rows| ==> PrimeGenerationWorksheetRowValid(keybits, worksheet.rows[i]))
    //- all but last row fail, last row as specified
    &&
     (forall i :: 0<=i<|worksheet.rows|-1 ==> !worksheet.rows[i].miller_rabin_worksheet.is_probably_prime)
    && (
        0<|worksheet.rows| ==> 
        worksheet.rows[|worksheet.rows|-1].miller_rabin_worksheet.is_probably_prime == last_succeeds
       )
    //- randoms properly accounted for
    && PrimeGenerationWorksheetConsumesRandoms(worksheet.rows) == worksheet.randoms
}

static function PrimeGenerationWorksheetAppend(keybits:int, worksheet:PrimeGenerationWorksheet, worksheet_row:PrimeGenerationWorksheetRow, last_accepted:bool) : PrimeGenerationWorksheet
    requires 0<keybits;
//-    requires PrimeGenerationWorksheetValid_precondition(worksheet);
    requires PrimeGenerationWorksheetValid_incremental(keybits, worksheet, false);
{
    PrimeGenerationWorksheet_c(
        worksheet.rows + [worksheet_row],
        worksheet.randoms + worksheet_row.randoms)
}   

static lemma PrimeGenerationWorksheetAppend_lemma(keybits:int, worksheet:PrimeGenerationWorksheet, row:PrimeGenerationWorksheetRow, last_accepted:bool, worksheet':PrimeGenerationWorksheet)
    requires 0<keybits;
//-    requires PrimeGenerationWorksheetValid_precondition(worksheet);
    requires PrimeGenerationWorksheetValid_incremental(keybits, worksheet, false);
    requires PrimeGenerationWorksheetAppend(keybits, worksheet, row, last_accepted) == worksheet';
    requires CandidatePrimeWorksheetValid(keybits, row.candidate);
    requires MillerRabinWorksheetValid(row.candidate.candidate, row.miller_rabin_worksheet);
    requires row.miller_rabin_worksheet.is_probably_prime == last_accepted;
    requires row.randoms == row.candidate.randoms + row.miller_rabin_worksheet.randoms;
    ensures PrimeGenerationWorksheetRowValid(keybits, row);
    ensures PrimeGenerationWorksheetValid_precondition(worksheet');
    ensures PrimeGenerationWorksheetValid_incremental(keybits, worksheet', last_accepted);
    ensures PrimeGenerationWorksheetConsumesRandoms(worksheet'.rows) == worksheet'.randoms;
    ensures 0 < |worksheet'.rows|;
{
}

method GenRandomPrime(keybits:nat) returns (Random:array<int>, ghost worksheet:PrimeGenerationWorksheet)
    requires 3 < keybits;
    requires keybits < power2(32);
    ensures WellformedFatNat(Random);
    ensures IsProbablyPrime(J(Random), Configure_MillerRabinStrength());
    ensures power2(keybits-1) <= J(Random) < power2(keybits);
    ensures PrimeGenerationWorksheetValid_precondition(worksheet);
    ensures PrimeGenerationWorksheetValid(keybits, worksheet);
    ensures PrimeGenerationOutput(worksheet) == J(Random);

    
    
    
    requires TPM_ready();
    ensures TPM_ready();
    modifies this`TPM;   
    modifies this`IoMemPerm;
    ensures TPMs_match_except_for_randoms(old(TPM), TPM);
    ensures old(TPM).random_index <= TPM.random_index;
    ensures worksheet.randoms == TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index);
{
    var isProbablyPrime:bool := false;
    worksheet := PrimeGenerationWorksheet_c([], []);

    lemma_power2_strictly_increases(30,32);
//-    assert(Word32(keybits-1));
    var Offset := FatPower2(keybits-1);
    Random := Offset; //- dafnycc: initialize variable
    ghost var started := false;

    while (!isProbablyPrime)
        decreases *;
        invariant WellformedFatNat(Offset);
        invariant J(Offset) == power2(keybits-1);
        invariant isProbablyPrime ==> WellformedFatNat(Random);
        invariant isProbablyPrime ==> power2(keybits-1) <= J(Random) < power2(keybits);
        invariant isProbablyPrime ==> IsProbablyPrime(J(Random), Configure_MillerRabinStrength());
        invariant PrimeGenerationWorksheetValid_incremental(keybits, worksheet, isProbablyPrime);
        invariant isProbablyPrime ==> 0 < |worksheet.rows|;
        invariant isProbablyPrime ==> started;
        invariant started ==> PrimeGenerationWorksheetValid_precondition(worksheet);
        invariant isProbablyPrime ==> PrimeGenerationOutput(worksheet) == J(Random);
        invariant TPM_ready();
        invariant TPMs_match_except_for_randoms(old(TPM), TPM);
        invariant old(TPM).random_index <= TPM.random_index;
        invariant worksheet.randoms == TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index);
    {
        var Entropy:array<int>;
        ghost var randoms:seq<int>;
        ghost var loop_TPM_index := TPM.random_index;
        Entropy,randoms := FatNatRandomPower2(keybits-1);
        assert randoms == TPM_random_bytes_premium(loop_TPM_index, TPM.random_index);

        assert 0<=J(Entropy)<power2(keybits-1);
        Random := FatNatAdd(Entropy, Offset);
        assert power2(keybits-1)==J(Offset)<=J(Random)<power2(keybits-1)+J(Offset);
        calc {
            J(Random);
            < power2(keybits-1)+J(Offset);
            power2(keybits-1)+power2(keybits-1);
                { lemma_mul_is_mul_boogie(2,power2(keybits-1)); }
            mul(2,power2(keybits-1));
                { lemma_power2_1_is_2(); }
            mul(power2(1),power2(keybits-1));
                { lemma_power2_adds(1, keybits-1); }
            power2(keybits);
        }
        calc {
            3;
            < 4;
                { lemma_power2_1_is_2(); reveal_power2(); }
            power2(2);
            <   { lemma_power2_strictly_increases(2, keybits-1); }
            power2(keybits-1);
            <= J(Random);
        }
//-        calc {
//-            J(Random);
//-            < power2(keybits);
//-            <   { lemma_power2_strictly_increases(keybits, power2(30)); }
//-            power2(power2(30));
//-            Frump();
//-        }
        assert WellformedFatNat(Random);
        assert {:split_here} true;

        ghost var candidate_worksheet := CandidatePrimeWorksheet_c(
            J(Random), J(Entropy),  randoms);

        
        

        ghost var miller_rabin_worksheet;
        ghost var miller_TPM_index := TPM.random_index;
        isProbablyPrime, miller_rabin_worksheet := MillerRabinTest(Random, Configure_MillerRabinStrength());
        assert miller_rabin_worksheet.randoms == TPM_random_bytes_premium(miller_TPM_index, TPM.random_index);

        assert old(TPM).random_index+|worksheet.randoms| == loop_TPM_index;
        assert old(TPM).random_index+|worksheet.randoms|+|candidate_worksheet.randoms| == miller_TPM_index; // OBSERVE trigger
        assert TPM_random_bytes_premium(loop_TPM_index, miller_TPM_index) == candidate_worksheet.randoms;   // OBSERVE trigger
        assert TPM_random_bytes_premium(old(TPM).random_index+|worksheet.randoms|, old(TPM).random_index+|worksheet.randoms|+|candidate_worksheet.randoms|) == candidate_worksheet.randoms;
        lemma_random_comprehension(old(TPM).random_index, worksheet.randoms, candidate_worksheet.randoms);
        assert TPM_random_bytes_premium(old(TPM).random_index, miller_TPM_index) == worksheet.randoms + candidate_worksheet.randoms;

        assert {:split_here} true;
        assert old(TPM).random_index + |worksheet.randoms+candidate_worksheet.randoms| == miller_TPM_index;
        assert old(TPM).random_index + |worksheet.randoms+candidate_worksheet.randoms| + |miller_rabin_worksheet.randoms| == TPM.random_index;
        assert TPM_random_bytes_premium(old(TPM).random_index, old(TPM).random_index+|worksheet.randoms+candidate_worksheet.randoms|)
            == worksheet.randoms+candidate_worksheet.randoms;
        assert old(TPM).random_index+|worksheet.randoms+candidate_worksheet.randoms|+|miller_rabin_worksheet.randoms| == TPM.random_index;
        assert TPM_random_bytes_premium(
            old(TPM).random_index+|worksheet.randoms+candidate_worksheet.randoms|,
            old(TPM).random_index+|worksheet.randoms+candidate_worksheet.randoms|+|miller_rabin_worksheet.randoms|)
            == miller_rabin_worksheet.randoms;
        lemma_random_comprehension(old(TPM).random_index, worksheet.randoms+candidate_worksheet.randoms, miller_rabin_worksheet.randoms);
        calc {
            TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index);
            (worksheet.randoms + candidate_worksheet.randoms)+miller_rabin_worksheet.randoms;
            worksheet.randoms + (candidate_worksheet.randoms+miller_rabin_worksheet.randoms);
        }
        assert {:split_here} true;

        ghost var worksheet_row := PrimeGenerationWorksheetRow_c(
            candidate_worksheet, miller_rabin_worksheet,
            candidate_worksheet.randoms+miller_rabin_worksheet.randoms);
        lemma_random_comprehension(loop_TPM_index, candidate_worksheet.randoms, miller_rabin_worksheet.randoms);
        ghost var worksheet' := PrimeGenerationWorksheetAppend(keybits, worksheet, worksheet_row, isProbablyPrime);

        lemma_div_is_div_boogie((keybits-1)-1, 8);
        assert ((keybits-1)-1)/8 + 1 == DivideRoundingUp_premium(keybits-1, 8); //- OBSERVE (premium)
        PrimeGenerationWorksheetAppend_lemma(keybits, worksheet, worksheet_row, isProbablyPrime, worksheet');

        assert {:split_here} true;
        assert TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index) == worksheet'.randoms;
        
//        assert worksheet'.randoms == TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index);
//        assert TPM.random_index == old(TPM).random_index+|worksheet'.randoms|;
//        assert TPM_random_bytes(old(TPM).random_index, old(TPM).random_index+|worksheet'.randoms|) == worksheet'.randoms;
//        lemma_random_comprehension(old(TPM).random_index, worksheet'.randoms, worksheet_row.randoms);
        worksheet := worksheet';
        started := true;
    }
}
