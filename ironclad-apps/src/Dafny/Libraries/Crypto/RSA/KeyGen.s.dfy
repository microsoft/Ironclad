include "MillerRabin.s.dfy"
include "../RandomTracing.s.dfy"

//------------------------------------------------------------//

//- CandidatePrimeWorksheet is used to select a candidate for
//- prime generation. This doesn't need to reject any candidates,
//- so it's much simpler (and admits a faster implementation, which
//- already happens to exist) than CandidateSeedWorksheet's
//- SelectRandomRequest.




datatype CandidatePrimeWorksheet = CandidatePrimeWorksheet_c(
    candidate:int, raw:int, randoms:seq<int>);

static predicate CandidatePrimeWorksheetValid(keybits:int, worksheet:CandidatePrimeWorksheet)
    requires 0<keybits;
{
    IsByteSeq(worksheet.randoms)
    && |worksheet.randoms| == ((keybits-1)-1)/8 + 1
    && worksheet.raw == BEByteSeqToInt(worksheet.randoms) % power2(keybits-1)
    && worksheet.candidate == worksheet.raw + power2(keybits-1)
}

//------------------------------------------------------------//

datatype PrimeGenerationWorksheetRow = PrimeGenerationWorksheetRow_c(
    candidate:CandidatePrimeWorksheet,
    miller_rabin_worksheet:MillerRabinWorksheet,
    randoms:seq<int>);

static predicate PrimeGenerationWorksheetRowValid(keybits:int, row:PrimeGenerationWorksheetRow)
    requires 0<keybits;
{
    CandidatePrimeWorksheetValid(keybits, row.candidate)
    && MillerRabinWorksheetValid(row.candidate.candidate, row.miller_rabin_worksheet)
    && row.randoms == row.candidate.randoms + row.miller_rabin_worksheet.randoms
}

//------------------------------------------------------------//

datatype PrimeGenerationWorksheet = PrimeGenerationWorksheet_c(
    rows:seq<PrimeGenerationWorksheetRow>,
    randoms:seq<int>);

static function PrimeGenerationWorksheetConsumesRandoms(rows:seq<PrimeGenerationWorksheetRow>) : seq<int>
{
    if (rows==[]) then
        []
    else
        PrimeGenerationWorksheetConsumesRandoms(rows[..|rows|-1]) + rows[|rows|-1].randoms
}

static predicate {:autoReq} PrimeGenerationWorksheetValid(keybits:int, worksheet:PrimeGenerationWorksheet)
{
    //- each row locally valid
    (forall i :: 0<=i<|worksheet.rows| ==> PrimeGenerationWorksheetRowValid(keybits, worksheet.rows[i]))
    //- all but last row fail, last row succeeds
    && (forall i :: 0<=i<|worksheet.rows|-1 ==> !worksheet.rows[i].miller_rabin_worksheet.is_probably_prime)
    && 0<|worksheet.rows|
    && worksheet.rows[|worksheet.rows|-1].miller_rabin_worksheet.is_probably_prime
    //- randoms properly accounted for
    && PrimeGenerationWorksheetConsumesRandoms(worksheet.rows) == worksheet.randoms
}

static function {:autoReq} PrimeGenerationOutput(worksheet:PrimeGenerationWorksheet) : int
    requires 0<|worksheet.rows|;
{
    worksheet.rows[|worksheet.rows|-1].candidate.candidate
}


