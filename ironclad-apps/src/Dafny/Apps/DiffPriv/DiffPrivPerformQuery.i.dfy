//-<NuBuild BasmEnableSymdiff true />
//- <NuBuild AddDafnyFlag /z3opt:NL_ARITH=true/>
include "../../Libraries/BigNum/BigRat.i.dfy"
include "../../Libraries/Util/relational.s.dfy"
include "../../Libraries/Util/arrays_and_seqs.i.dfy"
include "../../Drivers/TPM/tpm-wrapper.i.dfy"
include "DiffPriv.s.dfy"
include "ErrorCodes.i.dfy"
include "Noise.i.dfy"
include "SumReducer.i.dfy"
include "../Common/CommonState.i.dfy"
include "DiffPriv.i.dfy"

method {:dafnycc_conservative_seq_triggers} {:timeLimitMultiplier 3} DiffPrivPerformQuery
    (old_state:DiffPrivStateImpl, q:QueryParametersImpl)
    returns (error_code:int, response:int, new_state:DiffPrivStateImpl)
    requires DiffPrivStateValid(DiffPrivStateImplToSpec(old_state));
    requires QueryParametersImplValid(q);
    ensures DiffPrivStateValid(DiffPrivStateImplToSpec(new_state));
    ensures Word32(error_code);
    ensures Word32(response);
    ensures error_code == 0 ==> DiffPrivQueryPerformedCorrectly(DiffPrivStateImplToSpec(old_state), DiffPrivStateImplToSpec(new_state),
                                                                QueryParametersImplToSpec(q), response, old(TPM), TPM);
    ensures error_code != 0 ==> TPM == old(TPM) && new_state == old_state;

    requires public(q);
    requires public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(old_state)));
    ensures public(error_code);
    ensures public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(new_state)));

    //- TPM stuff:
    requires TPM_ready();
    ensures TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
{
    var program:seq<Operation>, p:DiffPrivParametersImpl, num_randoms_needed:nat;
    error_code, program, p, num_randoms_needed := GetErrorCodeForPerformQuery(q, old_state.budget);
    if error_code != 0 {
        response := 0;
        new_state := old_state;
        return;
    }

    //-
    //- At this point, the error code is set so we can look at private data.
    //- (All we looked at before was old_state.budget and |old_state.randoms|.)
    //-

    //-
    //- Generate the noise.
    //-

    var negate_noise:bool, absolute_noise:nat, remaining_budget:BigRat, remaining_randoms:seq<int>;
    ghost var noise:int, randoms_used:seq<int>;
    negate_noise, absolute_noise, noise, remaining_budget, randoms_used := GenerateNoise(p, old_state.budget, num_randoms_needed);

    //-
    //- Run the reducer.
    //-

    var answer:int;
    ghost var sum:int;
    answer, sum := ComputeSum(old_state.db, program, q.row_min, q.row_max, q.answer_units, q.answer_min, q.answer_max);

    //-
    //- Convert the answer into a response by adding noise and clipping.
    //-

    response := AddNoise(old_state.db, sum, answer, q, negate_noise, absolute_noise, noise);

    //-
    //- Update the state to reduce the privacy budget and remove the random numbers used.
    //-

    new_state := DiffPrivStateImpl_ctor(old_state.db, remaining_budget, old_state.rows_received);
    Lemma_QueryPerformedCorrectly(DiffPrivStateImplToSpec(old_state), DiffPrivStateImplToSpec(new_state), QueryParametersImplToSpec(q),
                                  DiffPrivParametersImplToSpec(p), old(TPM), TPM, noise, response);
}

