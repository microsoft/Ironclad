//-<NuBuild BasmEnableSymdiff true />
//- <NuBuild AddDafnyFlag /z3opt:NL_ARITH=true/>
include "../../Libraries/BigNum/BigRat.i.dfy"
include "../../Libraries/Util/relational.s.dfy"
include "../../Libraries/Util/arrays_and_seqs.i.dfy"
include "../../Drivers/TPM/tpm-wrapper.i.dfy"
include "../../Libraries/Crypto/RSA/RSA_Decrypt.i.dfy"
include "DiffPriv.s.dfy"
include "PacketParsing.i.dfy"
include "ErrorCodes.i.dfy"
include "Noise.i.dfy"
include "SumReducer.i.dfy"
include "RelationalProperties.i.dfy"
include "../Common/CommonState.i.dfy"

static function method{:CompiledSpec} CompiledSpec_Clip (value:int, min:int, max:int):int

//-////////////////////////////////////////////
//- DiffPrivStateImpl
//-////////////////////////////////////////////

datatype DiffPrivStateImpl = DiffPrivStateImpl_ctor(db:seq<Row>, budget:BigRat, rows_received:int);

static function DiffPrivStateImplToSpec(s:DiffPrivStateImpl) : DiffPrivState
{
    DiffPrivState_ctor(s.db, if WellformedBigRat(s.budget) then RV(s.budget) else 0.0, s.rows_received)
}

//-////////////////////////////////////////////
//- Query parameters
//-////////////////////////////////////////////

static method GetDiffPrivParametersFromQueryParameters (q:QueryParametersImpl) returns (p:DiffPrivParametersImpl)
    requires QueryParametersImplValid(q);
    requires QueryParametersValid(QueryParametersImplToSpec(q));
    ensures WellformedDiffPrivParameters(p);
    ensures DiffPrivParametersImplToSpec(p) == QueryParametersToDiffPrivParameters(QueryParametersImplToSpec(q));

    requires public(q);
    ensures public(p);
{
    var alpha := BigRat_ctor(MakeSmallLiteralBigNum(q.alpha_num), MakeSmallLiteralBigNat(q.alpha_den));
    var beta := BigRat_ctor(MakeSmallLiteralBigNum(q.beta_num), MakeSmallLiteralBigNat(q.beta_den));
    var delta := DivideRoundingUp(q.row_max - q.row_min, q.answer_units);
    Lemma_DivideRoundingUpPreservesWord32(q.row_max - q.row_min, q.answer_units);
    var B := q.answer_max - q.answer_min;

    assert RV(alpha) == real(q.alpha_num) / real(q.alpha_den);
    assert RV(beta) == real(q.beta_num) / real(q.beta_den);

    p := DiffPrivParametersImpl_ctor(alpha, beta, delta, B);
}

//-////////////////////////////////////////////
//- Comparing to one
//-////////////////////////////////////////////

static lemma Lemma_CompareDivisionToOne(x:int, y:int)
    requires x >= 0;
    requires y > 0;
    ensures var x_over_y := real(x) / real(y);
            (x < y ==> x_over_y < 1.0) &&
            (x == y ==> x_over_y == 1.0) &&
            (x > y ==> x_over_y > 1.0);
{
    if x == 0 {
        assert x < y;
        assert real(x) / real(y) == 0.0 < 1.0;
    }
    else {
        assert real(x) / real(x) == 1.0;

        if x == y {
            calc {
                real(x) / real(y);
                { assert real(y) == real(x); }
                real(x) / real(x);
            }
        }
        else if x < y {
            calc {
                real(x) / real(y);
                < { assert real(y) > real(x); }
                real(x) / real(x);
            }
        }
        else {
            assert x > y;
            calc {
                real(x) / real(y);
                > { lemma_real_div_gt(real(x), real(y)); }
                real(x) / real(x);
            }
        }
    }
}

//-////////////////////////////////////////////
//- Decrypting add-row requests
//-////////////////////////////////////////////

static predicate WellformedDecryptedAddRowRequest(request:DecryptedAddRowRequest)
{
    match request
        case DecryptedAddRowRequest_c(row, max_budget_num, max_budget_den) =>
            RowValid(row) && Word32(max_budget_num) && Word32(max_budget_den)
        case InvalidAddRowRequest_c => true
        case UndecryptableAddRowRequest_c => true
}

static lemma Lemma_WellformedDecryptedAddRowRequest(request:DecryptedAddRowRequest)
    requires request.DecryptedAddRowRequest_c?;
    requires RowValid(request.row);
    requires Word32(request.max_budget_num);
    requires Word32(request.max_budget_den);
    ensures WellformedDecryptedAddRowRequest(request);
{
}

static method ParseDecryptedAddRowRequest_impl (plaintext:seq<int>) returns (request:DecryptedAddRowRequest)
    requires IsByteSeq(plaintext);
    ensures WellformedDecryptedAddRowRequest(request);
    ensures request == ParseDecryptedAddRowRequest(plaintext);
{
    if |plaintext| < 16 {
        request := InvalidAddRowRequest_c();
        return;
    }

    var row_nonce_size := BEFourBytesToWord_impl(plaintext[0..4]);
    var row_data_size := BEFourBytesToWord_impl(plaintext[4..8]);
    assert row_nonce_size == BEByteSeqToInt(plaintext[0..4]);
    assert row_data_size == BEByteSeqToInt(plaintext[4..8]);
    if row_nonce_size < 0 || row_data_size < 0 || |plaintext| < 16 + row_nonce_size + row_data_size || row_data_size % 4 != 0 {
        request := InvalidAddRowRequest_c();
        return;
    }
    assert row_nonce_size >= 0 && row_data_size >= 0 && |plaintext| >= 16 + row_nonce_size + row_data_size && row_data_size % 4 == 0;

    ghost var fields := plaintext[8:4:4:row_nonce_size:row_data_size];

    var max_budget_num := BEFourBytesToWord_impl(plaintext[8..12]);
    assert max_budget_num == BEByteSeqToInt(fields[1]);
    var max_budget_den := BEFourBytesToWord_impl(plaintext[12..16]);
    assert max_budget_den == BEByteSeqToInt(fields[2]);
    var row_nonce := plaintext[16..16+row_nonce_size];
    assert row_nonce == fields[3];
    var row_data := plaintext[16+row_nonce_size..16+row_nonce_size+row_data_size];
    assert row_data == fields[4];
    var row_data_words, padbytes := BEByteSeqToWordSeq_impl(row_data);
    assert row_data_words == BEByteSeqToWordSeq(row_data);

    var row:Row := Row_ctor(row_nonce, row_data_words);
    request := DecryptedAddRowRequest_c(row, max_budget_num, max_budget_den);

    Lemma_WellformedDecryptedAddRowRequest(request);
}

method DecryptAddRowRequest_impl(ciphertext:seq<int>, key_pair:RSAKeyPairImpl) returns (request:DecryptedAddRowRequest)
    requires IsByteSeq(ciphertext);
    requires |ciphertext| > 0;
    requires WellformedRSAKeyPairImpl(key_pair);
    ensures AddRowRequestDecryptedCorrectly(ciphertext, KeyPairImplToSpec(key_pair), request);
    ensures WellformedDecryptedAddRowRequest(request);
{
    var success, plaintext := Decrypt(key_pair, ciphertext);
    if !success {
        request := UndecryptableAddRowRequest_c();
        return;
    }
    request := ParseDecryptedAddRowRequest_impl(plaintext);
}

//-////////////////////////////////////////////
//- Exported methods
//-////////////////////////////////////////////

method DiffPrivInitialize() returns (diffpriv_state:DiffPrivStateImpl)
    ensures DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state));
    ensures DiffPrivInitializeValid(DiffPrivStateImplToSpec(diffpriv_state));
    ensures public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state)));
{
    lemma_2toX();
    var one := MakeSmallLiteralBigRat(1);
    diffpriv_state := DiffPrivStateImpl_ctor([], one, 0);
    assert PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state)) == DiffPrivState_ctor([], 1.0, 0);
}

static method DiffPrivInitializeDB(old_state:DiffPrivStateImpl, budget_num:int, budget_den:int)
                                  returns (error_code:int, new_state:DiffPrivStateImpl)
    requires DiffPrivStateValid(DiffPrivStateImplToSpec(old_state));
    requires Word32(budget_num);
    requires Word32(budget_den);
    requires budget_den != 0;
    ensures Word32(error_code);
    ensures error_code == 0 ==> DiffPrivInitializedDBCorrectly(DiffPrivStateImplToSpec(old_state), DiffPrivStateImplToSpec(new_state),
                                                               real(budget_num) / real(budget_den));
    ensures error_code != 0 ==> new_state == old_state;

    requires public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(old_state)));
    requires public(budget_num);
    requires public(budget_den);
    ensures public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(new_state)));
    ensures public(error_code);
{
    lemma_2toX();

    if (old_state.rows_received != 0) {
        error_code := ErrorInitializingTooLate();
        new_state := old_state;
        return;
    }

    assert real(budget_num) >= 0.0;
    assert real(budget_den) > 0.0;

    Lemma_CompareDivisionToOne(budget_num, budget_den);
    if budget_num < budget_den {
        error_code := ErrorBudgetLessThanOne();
        new_state := old_state;
        return;
    }

    error_code := 0;

    //- At this point, the error code is set so we can look at private data.

    var budget := BigRat_ctor(MakeSmallLiteralBigNum(budget_num), MakeSmallLiteralBigNat(budget_den));
    assert RV(budget) == real(budget_num) / real(budget_den);
    new_state := DiffPrivStateImpl_ctor([], budget, old_state.rows_received);
}

lemma Lemma_AddingValidRowToValidDatabasePreservesValidity (db_prev:seq<Row>, row:Row, db_next:seq<Row>)
    requires DatabaseValid(db_prev);
    requires RowValid(row);
    requires db_next == db_prev + [row];
    ensures DatabaseValid(db_next);
{
}

method DiffPrivAddRow (old_state:DiffPrivStateImpl, key_pair:RSAKeyPairImpl, request_ciphertext:seq<int>)
                      returns (new_state:DiffPrivStateImpl)
    requires DiffPrivStateValid(DiffPrivStateImplToSpec(old_state));
    requires WellformedRSAKeyPairImpl(key_pair);
    requires IsByteSeq(request_ciphertext);
    requires |request_ciphertext| > 0;
    ensures DiffPrivRowAddedCorrectly(DiffPrivStateImplToSpec(old_state), DiffPrivStateImplToSpec(new_state),
                                      KeyPairImplToSpec(key_pair), request_ciphertext);

    requires public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(old_state)));
    ensures public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(new_state)));
{
    lemma_2toX();

    var request := DecryptAddRowRequest_impl(request_ciphertext, key_pair);
    new_state := old_state[rows_received := old_state.rows_received + 1];

    if !request.DecryptedAddRowRequest_c? {
        return;
    }

    if request.max_budget_den == 0 {
        return;
    }

    var max_budget := BigRat_ctor(MakeSmallLiteralBigNum(request.max_budget_num), MakeSmallLiteralBigNat(request.max_budget_den));
    var insufficient := BigRatGt(old_state.budget, max_budget);
    if insufficient {
        return;
    }

    //- At this point, the error code is set so we can look at private data.

    var already_exists:bool := DoesDatabaseContainNonce(old_state.db, request.row.nonce);
    if !already_exists {
        new_state := DiffPrivStateImpl_ctor(old_state.db + [request.row], old_state.budget, old_state.rows_received + 1);
        Lemma_AddingValidRowToValidDatabasePreservesValidity(old_state.db, request.row, new_state.db);
        assert DatabaseValid(DiffPrivStateImplToSpec(new_state).db);
    } 
}

//-////////////////////////////////////////////
//- Helpers
//-////////////////////////////////////////////

static method DoesDatabaseContainNonce (db:seq<Row>, nonce:seq<int>) returns (already_exists:bool)
    requires DatabaseValid(db);
    ensures already_exists == DatabaseContainsNonce(db, nonce);
{
    var i:int := 0;
    while i < |db|
        invariant 0 <= i <= |db|;
        invariant forall j :: 0 <= j < i ==> db[j].nonce != nonce;
    {
        if db[i].nonce == nonce {
            already_exists := true;
            return;
        }
        i := i + 1;
    }

    already_exists := false;
}

static method DetermineIfQueryParametersValid (q:QueryParametersImpl) returns (error_code:int, program:seq<Operation>)
    requires QueryParametersImplValid(q);
    ensures Word32(error_code);
    ensures error_code == 0 <==> QueryParametersValid(QueryParametersImplToSpec(q));
    ensures error_code == 0 ==> program == MessageToProgram(q.program_encoding);

    requires public(q);
    ensures public(error_code);
    ensures public(program);
{
    lemma_2toX();

    //-
    //- Validate the input values.
    //-
    program := []; //- dafnycc: initialize variable

    if (q.row_min > q.row_max) {
        error_code := ErrorRowMinGreaterThanRowMax();
        return;
    }
    if (q.answer_min > q.answer_max) {
        error_code := ErrorAnswerMinGreaterThanAnswerMax();
        return;
    }
    if (q.answer_units <= 0) {
        error_code := ErrorAnswerUnitsNotPositive();
        return;
    }

    Lemma_CompareDivisionToOne(q.alpha_num, q.alpha_den);
    if (q.alpha_num <= q.alpha_den) {
        error_code := ErrorAlphaNotGreaterThanOne();
        return;
    }

    Lemma_CompareDivisionToOne(q.beta_num, q.beta_den);
    if (q.beta_num <= q.beta_den) {
        error_code := ErrorBetaNotGreaterThanOne();
        return;
    }

    //-
    //- Convert the program encoding into a program and validate it.
    //-

    program := ConvertMessageToProgram(q.program_encoding);
    var valid:bool := DetermineIfProgramIsValid(program);
    if (!valid) {
        error_code := ErrorProgramInvalid();
        return;
    }

    error_code := 0;
}

method ParseQueryParameters (q:QueryParametersImpl) returns (error_code:int, program:seq<Operation>, p:DiffPrivParametersImpl)
    requires QueryParametersImplValid(q);
    ensures Word32(error_code);
    ensures error_code == 0 ==> QueryParametersValid(QueryParametersImplToSpec(q)) &&
                                program == MessageToProgram(q.program_encoding) &&
                                ProgramValid(program) &&
                                Word32(q.answer_units * 2) &&
                                WellformedDiffPrivParameters(p) &&
                                DiffPrivParametersImplToSpec(p) == QueryParametersToDiffPrivParameters(QueryParametersImplToSpec(q)) &&
                                DiffPrivParametersValid(DiffPrivParametersImplToSpec(p));

    requires public(q);
    ensures public(error_code);
    ensures public(program);
    ensures public(p);
{
    //-
    //- Validate the input values.
    //-

    program := []; //- dafnycc: initialize variable
    var r0 := MakeSmallLiteralBigRat(0);
    p := DiffPrivParametersImpl_ctor(r0, r0, 0, 0); //- dafnycc: initialize variable

    error_code, program := DetermineIfQueryParametersValid(q);
    if (error_code != 0) {
        return;
    }

    //-
    //- Make sure the answer units aren't too high.
    //-

    error_code := TestAnswerUnits(q.answer_units);
    if (error_code != 0) {
        return;
    }

    //-
    //- Compute noise parameters and validate them.
    //-

    p := GetDiffPrivParametersFromQueryParameters(q);
    error_code := DetermineIfDiffPrivParametersValid(p);
}

method GetErrorCodeForPerformQuery (q:QueryParametersImpl, budget:BigRat)
                                   returns (error_code:int, program:seq<Operation>, p:DiffPrivParametersImpl,
                                            num_randoms_needed:nat)
    requires QueryParametersImplValid(q);
    requires WellformedBigRat(budget);
    ensures Word32(error_code);
    ensures error_code == 0 ==> QueryParametersValid(QueryParametersImplToSpec(q)) &&
                                program == MessageToProgram(q.program_encoding) &&
                                ProgramValid(program) &&
                                Word32(q.answer_units * 2) &&
                                WellformedDiffPrivParameters(p) &&
                                DiffPrivParametersImplToSpec(p) == QueryParametersToDiffPrivParameters(QueryParametersImplToSpec(q)) &&
                                DiffPrivParametersValid(DiffPrivParametersImplToSpec(p)) &&
                                RV(budget) >= RV(p.beta) &&
                                Word32((num_randoms_needed-1)*8+1) &&
                                SufficientBytesForNoiseGeneration(DiffPrivParametersImplToSpec(p), num_randoms_needed);

    requires public(q);
    requires public(RV(budget));
    ensures public(error_code);
    ensures public(program);
    ensures public(p);
    ensures public(num_randoms_needed);
{
    lemma_2toX();

    error_code, program, p := ParseQueryParameters(q);
    num_randoms_needed := 0; //- dafnycc: initialize variable
    if error_code != 0 {
        return;
    }

    //-
    //- See if there's sufficient budget.
    //-

    var InsufficientPrivacyBudget:bool := BigRatGt(p.beta, budget);
    if InsufficientPrivacyBudget {
        error_code := ErrorInsufficientPrivacyBudget();
        return;
    }

    //-
    //- Determine how many random numbers we need.
    //-

    error_code, num_randoms_needed := ComputeBytesForNoiseGeneration(p);
}

method GenerateNoise (p:DiffPrivParametersImpl, budget:BigRat, num_randoms_needed:nat)
                     returns (negate_noise:bool, absolute_noise:nat, ghost noise:int,
                              remaining_budget:BigRat, randoms_used:seq<int>)
    requires WellformedDiffPrivParameters(p);
    requires DiffPrivParametersValid(DiffPrivParametersImplToSpec(p));
    requires WellformedBigRat(budget);
    requires Word32((num_randoms_needed-1)*8+1);
    requires SufficientBytesForNoiseGeneration(DiffPrivParametersImplToSpec(p), num_randoms_needed);
    requires RV(budget) >= RV(p.beta) >= 1.0;

    ensures Word32(absolute_noise);
    ensures WellformedBigRat(remaining_budget);
    ensures IsByteSeq(randoms_used);
    ensures noise == (if negate_noise then -absolute_noise else absolute_noise);
    ensures NoiseComputedCorrectly(DiffPrivParametersImplToSpec(p), randoms_used, noise);
    ensures randoms_used == TPM_random_bytes(old(TPM.random_index), TPM.random_index);
    ensures RV(remaining_budget) == RV(budget) / RV(p.beta);

    requires TPM_ready();
    ensures TPM_ready();
    ensures TPMs_match_except_for_randoms(old(TPM), TPM);
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures old(TPM.random_index) <= TPM.random_index;
{
    ghost var old_random_index := TPM.random_index;

    randoms_used := get_random(num_randoms_needed);

    //- Compute the noise to use.

    negate_noise, absolute_noise, noise := ComputeNoise(p, randoms_used);

    //- Reduce the budget by beta.

    Lemma_IfBigRatGeOneItsNotZero(p.beta);
    remaining_budget := BigRatDiv(budget, p.beta);

    assert SufficientBytesForNoiseGeneration(DiffPrivParametersImplToSpec(p), num_randoms_needed);
    assert SufficientBytesForNoiseGeneration(DiffPrivParametersImplToSpec(p), |randoms_used|);
}

static method TestAnswerUnits (answer_units:int) returns (error_code:int)
    requires Word32(answer_units);
    ensures Word32(error_code);
    ensures error_code == 0 ==> Word32(answer_units * 2);

    requires public(answer_units);
    ensures public(error_code);
{
    lemma_2toX();
    error_code := if answer_units < 0x80000000 then 0 else ErrorAnswerUnitsTooLarge();
}

static method AddNoise (ghost db:seq<Row>, ghost sum:int, answer:int, q:QueryParametersImpl,
                        negate_noise:bool, absolute_noise:nat, ghost noise:int)
                        returns (response:int)
    requires DatabaseValid(db);
    requires QueryParametersImplValid(q);
    requires QueryParametersValid(QueryParametersImplToSpec(q));
    requires sum == MapperSum(db, MessageToProgram(q.program_encoding), q.row_min, q.row_max);
    requires answer == Clip(Scale(sum, q.answer_units), q.answer_min, q.answer_max);
    requires noise == if negate_noise then -absolute_noise else absolute_noise;
    requires Word32(absolute_noise);
    ensures Word32(response);
    ensures sum == MapperSum(db, MessageToProgram(q.program_encoding), q.row_min, q.row_max);
    ensures response == QueryResponse(db, QueryParametersImplToSpec(q), noise);
{
    var noised_answer:int;
    if negate_noise {
        if (answer < absolute_noise) {
            noised_answer := 0;
        }
        else {
            noised_answer := answer - absolute_noise;
        }
    }
    else {
        noised_answer := SaturatingAdd(answer, absolute_noise);
    }

    //-
    //- Clip the noised answer to get the response.
    //-

    response := Clip(noised_answer, q.answer_min, q.answer_max);
    Lemma_QueryResponseComputedCorrectly(db, sum, QueryParametersImplToSpec(q), negate_noise, absolute_noise, noise, answer, noised_answer, response);
}

//-////////////////////////
//- Lemmas
//-////////////////////////

static lemma {:timeLimitMultiplier 3} Lemma_QueryPerformedCorrectly (old_state:DiffPrivState, new_state:DiffPrivState, q:QueryParameters,
                                                                     p:DiffPrivParameters, old_TPM:TPM_struct, new_TPM:TPM_struct, ghost noise:int,
                                                                     response:int)
    requires DiffPrivStateValid(old_state);
    requires QueryParametersValid(q);
    requires DiffPrivParametersValid(p);
    requires p == QueryParametersToDiffPrivParameters(q);
    requires Word32(response);
    requires old_state.budget >= p.beta >= 1.0;
    requires new_state.db == old_state.db;
    requires new_state.rows_received == old_state.rows_received;
    requires new_state.budget == old_state.budget / p.beta;
    requires TPMs_match_except_for_randoms(old_TPM, new_TPM);
    requires NoiseComputedCorrectly(p, TPM_random_bytes(old_TPM.random_index, new_TPM.random_index), noise);
    requires response == QueryResponse(old_state.db, q, noise);
    ensures DiffPrivQueryPerformedCorrectly(old_state, new_state, q, response, old_TPM, new_TPM);
    ensures new_state.budget >= 1.0;
{
    reveal_DiffPrivQueryPerformedCorrectly();

    var program := MessageToProgram(q.program_encoding);
    Lemma_DividingBySmallerProducesAtLeastOne(old_state.budget, p.beta);

    assert QuerySuccessfulTrigger(noise);
    Lemma_SensitivityOfComputeSum(program, q.row_min, q.row_max, q.answer_units, q.answer_min, q.answer_max,
                                  DivideRoundingUp(q.row_max - q.row_min, q.answer_units));
    assert QuerySuccessful(old_state, new_state, q, response, TPM_random_bytes(old_TPM.random_index, new_TPM.random_index), noise);
}

static lemma Lemma_QueryResponseComputedCorrectly (ghost db:seq<Row>, ghost sum:int, q:QueryParameters,
                                                   negate_noise:bool, absolute_noise:nat, ghost noise:int,
                                                   answer:int, noised_answer:int, response:int)
    requires DatabaseValid(db);
    requires QueryParametersValid(q);
    requires Word32(absolute_noise);
    requires Word32(answer);
    requires Word32(noised_answer);
    requires Word32(response);
    requires sum == MapperSum(db, MessageToProgram(q.program_encoding), q.row_min, q.row_max);
    requires answer == Clip(Scale(sum, q.answer_units), q.answer_min, q.answer_max);
    requires noise == if negate_noise then -absolute_noise else absolute_noise;
    requires noised_answer == (if negate_noise then
                                   (if answer < absolute_noise then 0 else answer - absolute_noise)
                               else
                                   SaturatingAdd(answer, absolute_noise));
    requires response == Clip(noised_answer, q.answer_min, q.answer_max);
    ensures response == QueryResponse(db, q, noise);
{
}

static lemma Lemma_DividingBySmallerProducesAtLeastOne (x:real, y:real)
    requires x >= y > 0.0;
    ensures x/y >= 1.0;
{
}

static lemma Lemma_IfBigRatGeOneItsNotZero (Q:BigRat)
    requires WellformedBigRat(Q);
    requires RV(Q) >= 1.0;
    ensures nonzero(Q.n.value);
{
    if !nonzero(Q.n.value) {
        calc {
            RV(Q);
            real(BV(Q.n)) / real(I(Q.d));
            0.0 / real(I(Q.d));
            0.0;
        }
        assert false;
    }
}

static lemma Lemma_IndexingIntoSequenceConcatenation (seq1:seq<int>, seq2:seq<int>, i:nat)
    requires |seq1| <= i < |seq1| + |seq2|;
    ensures (seq1 + seq2)[i] == seq2[i-|seq1|];
{
}
