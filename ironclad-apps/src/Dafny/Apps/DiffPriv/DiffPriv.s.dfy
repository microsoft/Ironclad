include "../../Libraries/Util/be_sequences.s.dfy"
include "../../Libraries/Crypto/RSA/RSASpec.s.dfy"
include "../../Libraries/Crypto/RSA/rfc4251.s.dfy"
include "../Common/CommonState.s.dfy"
include "../../Drivers/TPM/tpm-device.s.dfy"
include "Mapper.s.dfy"
include "SumReducer.s.dfy"
include "Noise.s.dfy"

datatype DiffPrivState = DiffPrivState_ctor(db:seq<Row>, budget:real, rows_received:int);

static predicate DiffPrivStateValid (s:DiffPrivState)
{
    DatabaseValid(s.db) &&
    s.budget >= 1.0
}

static function PublicPartOfDiffPrivState (s:DiffPrivState) : DiffPrivState
{
    DiffPrivState_ctor([], s.budget, s.rows_received)
}

//- This function is used to ensure that DiffPriv initialization operates correctly.

static predicate {:autoReq} DiffPrivInitializeValid(diffpriv_state:DiffPrivState)
{
    diffpriv_state.db == [] &&
    diffpriv_state.budget == 1.0 &&
    diffpriv_state.rows_received == 0
}

datatype QueryParameters = QueryParameters_ctor(program_encoding:seq<int>, row_min:int, row_max:int,
                                                answer_units:int, answer_min:int, answer_max:int,
                                                alpha:real, beta:real)

static predicate QueryParametersValid (q:QueryParameters)
{
    Word32(q.row_min) &&
    Word32(q.row_max) &&
    Word32(q.answer_units) &&
    Word32(q.answer_min) &&
    Word32(q.answer_max) &&
    q.row_min <= q.row_max &&
    q.answer_min <= q.answer_max &&
    q.alpha > 1.0 &&
    q.beta > 1.0 &&
    q.answer_units > 0 &&
    IsWordSeq(q.program_encoding) &&
    ProgramValid(MessageToProgram(q.program_encoding))
}

static predicate DiffPrivInitializedDBCorrectly (old_state:DiffPrivState, new_state:DiffPrivState, budget:real)
{
    DiffPrivStateValid(new_state) &&
    budget >= 1.0 &&
    old_state.rows_received == 0 &&
    new_state.db == [] &&
    new_state.budget == budget &&
    new_state.rows_received == old_state.rows_received
}

datatype DecryptedAddRowRequest = DecryptedAddRowRequest_c(row:Row, max_budget_num:int, max_budget_den:int) |
                                  InvalidAddRowRequest_c() |
                                  UndecryptableAddRowRequest_c();

static function ParseDecryptedAddRowRequest(plaintext:seq<int>) : DecryptedAddRowRequest
    requires IsByteSeq(plaintext);
{
    if |plaintext| < 16 then
        InvalidAddRowRequest_c()
    else
    (
        var row_nonce_size := BEByteSeqToInt(plaintext[0..4]);
        var row_data_size := BEByteSeqToInt(plaintext[4..8]);
        if row_nonce_size < 0 || row_data_size < 0 || |plaintext| < 16 + row_nonce_size + row_data_size || row_data_size % 4 != 0 then
            InvalidAddRowRequest_c()
        else
            (var fields := plaintext[8          :4                         :4                         :row_nonce_size :row_data_size ];
            var                     _,         max_budget_num,            max_budget_den,            row_nonce,      row_data       :=
                                    fields[0], BEByteSeqToInt(fields[1]), BEByteSeqToInt(fields[2]), fields[3],      fields[4]      ;
            var row_data_words := BEIntToDigitSeq(power2(32), |row_data|/4, BEDigitSeqToInt(power2(8), row_data));
            DecryptedAddRowRequest_c(Row_ctor(row_nonce, row_data_words), max_budget_num, max_budget_den))
    )
}

static predicate AddRowRequestDecryptedCorrectly(ciphertext:seq<int>, key_pair:RSAKeyPairSpec, request:DecryptedAddRowRequest)
    requires IsByteSeq(ciphertext);
{
    (
        exists plaintext:seq<int> :: RSADecryptionRelation(key_pair, ciphertext, plaintext) &&
                                     request == ParseDecryptedAddRowRequest(plaintext)
    )
    ||
    (
        request == UndecryptableAddRowRequest_c()
        && !exists plaintext:seq<int> :: RSADecryptionRelation(key_pair, ciphertext, plaintext)
    )
}

static predicate DiffPrivRowAddedCorrectly (old_state:DiffPrivState, new_state:DiffPrivState, key_pair:RSAKeyPairSpec,
                                            request_ciphertext:seq<int>)
{
    IsByteSeq(request_ciphertext) &&
    DiffPrivStateValid(new_state) &&
    new_state.budget == old_state.budget &&
    new_state.rows_received == old_state.rows_received + 1 &&
    (
        exists request:DecryptedAddRowRequest ::
            AddRowRequestDecryptedCorrectly(request_ciphertext, key_pair, request) &&
            if request.DecryptedAddRowRequest_c?
               && request.max_budget_den > 0
               && old_state.budget <= real(request.max_budget_num) / real(request.max_budget_den)
               && !DatabaseContainsNonce(old_state.db, request.row.nonce) then
                new_state.db == old_state.db + [request.row]
            else
                new_state.db == old_state.db
    )
}

static function QueryResponse (db:seq<Row>, q:QueryParameters, noise:int) : int
    requires DatabaseValid(db);
    requires QueryParametersValid(q);
{
    var program := MessageToProgram(q.program_encoding);
    var sum := MapperSum(db, program, q.row_min, q.row_max);
    var scaled_sum := Scale(sum, q.answer_units);
    var answer := Clip(scaled_sum, q.answer_min, q.answer_max);
    var noised_answer := answer + noise;
    Clip(noised_answer, q.answer_min, q.answer_max)
}

static function QueryParametersToDiffPrivParameters (q:QueryParameters) : DiffPrivParameters
    requires QueryParametersValid(q);
{
    DiffPrivParameters_ctor(q.alpha,
                            q.beta,
                            DivideRoundingUp(q.row_max - q.row_min, q.answer_units),
                            q.answer_max - q.answer_min)
}

static predicate QuerySuccessful (old_state:DiffPrivState, new_state:DiffPrivState, q:QueryParameters, response:int,
                                  randoms_used:seq<int>, noise:int)
    requires DiffPrivStateValid(old_state);
    requires QueryParametersValid(q);
{
    var p := QueryParametersToDiffPrivParameters(q);

    DiffPrivParametersValid(p) &&
    old_state.budget >= p.beta &&
    new_state.db == old_state.db &&
    new_state.rows_received == old_state.rows_received &&
    new_state.budget == old_state.budget / p.beta &&
    NoiseComputedCorrectly(p, randoms_used, noise) &&
    response == QueryResponse(old_state.db, q, noise) &&
    (forall db1:seq<Row>, db2:seq<Row> ::
        (var program, row_min, row_max, answer_units, answer_min, answer_max :=
            MessageToProgram(q.program_encoding), q.row_min, q.row_max, q.answer_units, q.answer_min, q.answer_max;
        var delta := DivideRoundingUp(row_max - row_min, answer_units);
        DatabaseValid(db1) && DatabaseValid(db2) && DatabasesSimilar(db1, db2) ==>
        -delta <= Clip(Scale(MapperSum(db1, program, row_min, row_max), answer_units), answer_min, answer_max) -
                  Clip(Scale(MapperSum(db2, program, row_min, row_max), answer_units), answer_min, answer_max) <= delta)
    )
}

static predicate QuerySuccessfulTrigger (noise:int)
{
    true
}

static predicate {:opaque} DiffPrivQueryPerformedCorrectly (old_state:DiffPrivState, new_state:DiffPrivState, q:QueryParameters,
                                                            response:int, old_TPM:TPM_struct, new_TPM:TPM_struct)
    requires DiffPrivStateValid(old_state);
{
    DiffPrivStateValid(new_state) &&
    QueryParametersValid(q) &&
    TPMs_match(new_TPM, old_TPM[random_index := new_TPM.random_index]) &&
    (exists noise:int {:trigger QuerySuccessfulTrigger(noise)} ::
         QuerySuccessful(old_state, new_state, q, response, TPM_random_bytes(old_TPM.random_index, new_TPM.random_index), noise))
}
