include "../../Libraries/Util/be_sequences.s.dfy"
include "../../Libraries/Crypto/Hash/sha256.s.dfy"
include "../../Drivers/TPM/tpm-device.s.dfy"

//-///////////////////////////////////////////////////
//- Structures
//-///////////////////////////////////////////////////

datatype PassHashState = PassHashStateConstructor(secret:seq<int>);

//-///////////////////////////////////////////////////
//- Specifications for correct method operation
//-///////////////////////////////////////////////////

static predicate {:autoReq} PassHashInitializeValid(passhash_state:PassHashState, before_TPM:TPM_struct, after_TPM:TPM_struct)
{
    TPMs_match(after_TPM, before_TPM[random_index := after_TPM.random_index]) &&
    passhash_state.secret == TPM_random_bytes(before_TPM.random_index, after_TPM.random_index) &&
    IsByteSeq(passhash_state.secret) &&
    |passhash_state.secret| >= 32
}

static predicate {:autoReq} PassHashPerformHashValid(passhash_state:PassHashState, message_in:seq<int>, salt_in:seq<int>,
                                                     error_code_out:int, passhash_hash_out:seq<int>)
{
    if error_code_out == 0 then
        IsByteSeq(passhash_state.secret) &&
        passhash_hash_out == BEWordSeqToByteSeq(SHA256(BEByteSeqToBitSeq(passhash_state.secret + salt_in + message_in)))
    else
        passhash_hash_out == RepeatDigit(0, 32)
}
