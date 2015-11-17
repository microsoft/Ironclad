include "../../Libraries/Crypto/RSA/RSASpec.s.dfy"
include "../../Libraries/Crypto/RSA/rfc4251.s.dfy"
include "../../Libraries/Crypto/Hash/sha1.s.dfy"
include "../../Libraries/Util/integer_sequences.s.dfy"
include "../../Libraries/Util/be_sequences.s.dfy"
include "../../Libraries/Math/power2.s.dfy"
include "../../Drivers/TPM/tpm-device.s.dfy"

datatype CommonState = CommonStateConstructor(key_pair:RSAKeyPairSpec, key_bits:nat)

datatype CommonStateMachine = CommonStateMachine_ctor(initialized:bool, common_state:CommonState, TPM:TPM_struct)

ghost var {:readonly} current_common_state:CommonStateMachine;

static predicate {:autoReq} PCR19ReflectsKey (state:CommonState, before_TPM:TPM_struct, after_TPM:TPM_struct)
{
    var encoded_public_key := rfc4251_sshrsa_encoding(state.key_pair.pub.e, state.key_pair.pub.n);
    after_TPM.PCR_19 == before_TPM.PCR_19 + [BEWordSeqToByteSeq(SHA1(BEByteSeqToBitSeq(encoded_public_key)))]
}

static predicate {:autoReq} CommonStateGeneratedCorrectly (key_bits:nat, state:CommonState, before_TPM:TPM_struct, after_TPM:TPM_struct)
{
    state.key_bits == key_bits
    && RSAKeyGenerationValid(state.key_bits, state.key_pair, TPM_random_bytes(before_TPM.random_index, after_TPM.random_index))
    && Locality3_obtained()
    && TPM_valid(after_TPM)
    && TPM_satisfies_integrity_policy(after_TPM)
    && PCR19ReflectsKey(state, before_TPM, after_TPM)
    && TPMs_match(after_TPM, before_TPM[random_index := after_TPM.random_index][PCR_19 := after_TPM.PCR_19])
}

//- This function is used to ensure that the routine to get a quote operates correctly.
//- It should output the public key and quote.

static predicate {:autoReq} HandleGetQuoteRequestValid (state:CommonState, old_TPM:TPM_struct, new_TPM:TPM_struct,
                                                        nonce_external_in:seq<int>, encoded_public_key_out:seq<int>,
                                                        pcr_info_bytes_out:seq<int>, sig_bytes_out:seq<int>)
{
    TPMs_match(new_TPM, old_TPM)
    && encoded_public_key_out == rfc4251_sshrsa_encoding(state.key_pair.pub.e, state.key_pair.pub.n)
    && Verve_quote(pcr_info_bytes_out, sig_bytes_out, nonce_external_in, old_TPM.PCR_19)
}

ghost method {:axiom} {:autoReq} InitializeCommonStateMachine(common_state:CommonState)
    requires !current_common_state.initialized;
    requires CommonStateGeneratedCorrectly(1024, common_state, current_common_state.TPM, TPM);
    ensures current_common_state == CommonStateMachine_ctor(true, common_state, TPM);
    modifies this`current_common_state;

ghost method {:axiom} {:autoReq} AdvanceCommonStateMachineViaGetQuote
   (nonce_external_in:seq<int>, encoded_public_key_out:seq<int>, pcr_info_bytes_out:seq<int>, sig_bytes_out:seq<int>)
   returns (declassified_encoded_public_key_out:seq<int>, declassified_pcr_info_bytes_out:seq<int>, declassified_sig_bytes_out:seq<int>)
    requires current_common_state.initialized;
    requires public(nonce_external_in);
    requires HandleGetQuoteRequestValid(current_common_state.common_state, current_common_state.TPM, TPM, nonce_external_in,
                                        encoded_public_key_out, pcr_info_bytes_out, sig_bytes_out);
    modifies this`current_common_state;
    ensures current_common_state == old(current_common_state)[TPM := TPM];
    ensures IsByteSeqOfLen(declassified_encoded_public_key_out, |encoded_public_key_out|);
    ensures public(|encoded_public_key_out|);
    ensures relation(forall i :: left(i) == right(i) && 0 <= left(i) < left(|declassified_encoded_public_key_out|) ==>
                                 declassified(left(declassified_encoded_public_key_out[i]), right(declassified_encoded_public_key_out[i]),
                                              left(encoded_public_key_out[i]), right(encoded_public_key_out[i])));
    ensures IsByteSeqOfLen(declassified_pcr_info_bytes_out, |pcr_info_bytes_out|);
    ensures public(|pcr_info_bytes_out|);
    ensures relation(forall i :: left(i) == right(i) && 0 <= left(i) < left(|declassified_pcr_info_bytes_out|) ==>
                                 declassified(left(declassified_pcr_info_bytes_out[i]), right(declassified_pcr_info_bytes_out[i]),
                                              left(pcr_info_bytes_out[i]), right(pcr_info_bytes_out[i])));
    ensures public(|sig_bytes_out|);
    ensures IsByteSeqOfLen(declassified_sig_bytes_out, |sig_bytes_out|);
    ensures relation(forall i :: left(i) == right(i) && 0 <= left(i) < left(|declassified_sig_bytes_out|) ==>
                                 declassified(left(declassified_sig_bytes_out[i]), right(declassified_sig_bytes_out[i]),
                                              left(sig_bytes_out[i]), right(sig_bytes_out[i])));
