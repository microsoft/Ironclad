include "../Math/power2.s.dfy"
include "../Math/round.s.dfy"
include "../Util/be_sequences.s.dfy"
include "RandomTracing.s.dfy"

//------------------------------------------------------------//

//- Selecting a random number in a range
//- Used to select the seeds for MillerRabin tests.

datatype SelectRandomRequest = SelectRandomRequest_c(
    l:int, h:int, h_bits:int);

static predicate SelectRandomRequestValid(req:SelectRandomRequest)
    
    
{
    0<req.h_bits
    && req.h < power2(req.h_bits)
    && power2(req.h_bits-1) <= req.h
}

datatype CandidateSeedWorksheetRow = CandidateSeedWorksheetRow_c(
    n:int,
    accepted:bool,
    randoms:seq<int>);

static predicate CandidateSeedWorksheetRowValid(req:SelectRandomRequest, row:CandidateSeedWorksheetRow)
{
    //- consume exactly the required number of random bytes
    SelectRandomRequestValid(req)
    && |row.randoms| == DivideRoundingUp(req.h_bits, 8)
    && IsByteSeq(row.randoms)
    && row.n == BEByteSeqToInt(row.randoms) % power2(req.h_bits)
    && row.accepted == (req.l<=row.n && row.n<=req.h)
}

//------------------------------------------------------------//

datatype CandidateSeedWorksheet = CandidateSeedWorksheet_c(
    rows:seq<CandidateSeedWorksheetRow>,
    randoms:seq<int>);

//- NB Every predicate of the form *ConsumesRandoms() has exactly the same
//- body -- they're duplicated because they're talking about different
//- row types, and those types aren't polymorphic.

static function CandidateSeedWorksheetConsumesRandoms(rows:seq<CandidateSeedWorksheetRow>) : seq<int>
{
    if (rows==[]) then
        []
    else
        CandidateSeedWorksheetConsumesRandoms(rows[..|rows|-1]) + rows[|rows|-1].randoms
}

static predicate CandidateSeedWorksheetValid(req:SelectRandomRequest, worksheet:CandidateSeedWorksheet)
{
    //- there is at least one candidate
    0<|worksheet.rows|
    //- each row locally valid
    && (forall i :: 0<=i<|worksheet.rows| ==> CandidateSeedWorksheetRowValid(req, worksheet.rows[i]))
    //- all but last row fail, last row succeeds
    && (forall i:int :: 0<=i<|worksheet.rows|-1 ==> !worksheet.rows[i].accepted)
    && worksheet.rows[|worksheet.rows|-1].accepted
    //- randoms properly accounted for
    && CandidateSeedWorksheetConsumesRandoms(worksheet.rows) == worksheet.randoms
}

static function CandidateSeedWorksheetOutput(worksheet:CandidateSeedWorksheet) : int
    requires 0<|worksheet.rows|;
{
    worksheet.rows[|worksheet.rows|-1].n
}

//------------------------------------------------------------//
