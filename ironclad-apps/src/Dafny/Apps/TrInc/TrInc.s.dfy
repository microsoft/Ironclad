include "../../Libraries/Util/be_sequences.s.dfy"
include "../../Libraries/Crypto/RSA/RSASpec.s.dfy"
include "../../Libraries/Crypto/RSA/rfc4251.s.dfy"
include "../Common/CommonState.s.dfy"
include "../../Drivers/TPM/tpm-device.s.dfy"

//-///////////////////////////////////////////////////
//- Structures
//-///////////////////////////////////////////////////

//- Each counter has an RSA public key associated with it; only users
//- in possession of the corresponding private key are allowed to
//- advance the counter.

datatype TrIncCounter = TrIncCounterConstructor(public_key:RSAPubKeySpec, counter_value:nat);
datatype TrIncState = TrIncStateConstructor(counters:seq<TrIncCounter>);

//-///////////////////////////////////////////////////
//- Helpers
//-///////////////////////////////////////////////////

static predicate TrIncStateValid(state:TrIncState)
{
    Word32(|state.counters|) &&
    (forall i :: 0 <= i < |state.counters| ==> WellformedRSAPubKeySpec(state.counters[i].public_key))
}

static function {:autoReq} TrIncCounterAdvanceStatement(counter_index:nat, old_counter_value:nat, new_counter_value:nat,
                                                        message:seq<int>) : seq<int>
{
    [34] /* counter advance */ + rfc4251_word32_encoding(counter_index) + rfc4251_mpint_encoding(old_counter_value)
         + rfc4251_mpint_encoding(new_counter_value) + message
}

//-///////////////////////////////////////////////////
//- Specifications for correct method operation
//-///////////////////////////////////////////////////

//- This function is used to ensure that TrInc initialization operates correctly.
//- It should initialize the counter set to be empty.

static predicate {:autoReq} TrIncInitializeValid(state:TrIncState)
{
    |state.counters| == 0
}

//- This function is used to ensure that TrIncCreateCounter operates correctly.
//- That method is supposed to create a new counter with the given public key.
//- It returns the index of the new counter.

static predicate {:autoReq} TrIncCreateCounterValid(in_state:TrIncState, out_state:TrIncState, common_state:CommonState,
                                                    public_key_encoding_in:seq<int>, counter_index_out:nat)
    requires IsByteSeq(public_key_encoding_in);
{
    TrIncStateValid(out_state) &&
    exists public_key_in:RSAPubKeySpec ::
        public_key_encoding_in == rfc4251_sshrsa_encoding(public_key_in.e, public_key_in.n) &&
        out_state.counters == in_state.counters + [TrIncCounterConstructor(public_key_in, 0)] &&
        counter_index_out == |in_state.counters|
}

//- This function is used to ensure that TrIncAdvanceCounter operates
//- correctly.  That method is supposed to advance the given counter to the
//- given new counter value.  It should then return an attestation that the
//- counter was advanced.

static predicate {:autoReq} TrIncAdvanceCounterValid(in_state:TrIncState, out_state:TrIncState, common_state:CommonState,
                                                     counter_index_in:nat, new_counter_value_encoding_in:seq<int>,
                                                     message_in:seq<int>, request_attestation_in:seq<int>,
                                                     TrInc_statement_out:seq<int>, TrInc_attestation_out:seq<int>)
    requires IsByteSeq(new_counter_value_encoding_in);
    requires IsByteSeq(message_in);
    requires IsByteSeq(request_attestation_in);
{
    //- Note that, as in the TrInc paper, it is acceptable to advance the counter to
    //- the same value that it had before.  This is OK because the attestation will
    //- state the old and new counter values, so the recipient of that attestation
    //- can't mistake it for a non-zero counter advance.

    TrIncStateValid(out_state) &&
    exists new_counter_value_in:nat ::
        //- The parameters are valid

        0 <= counter_index_in < |in_state.counters| &&
        new_counter_value_encoding_in == rfc4251_mpint_encoding(new_counter_value_in) &&
        in_state.counters[counter_index_in].counter_value <= new_counter_value_in &&
        WellformedRSAPubKeySpec(in_state.counters[counter_index_in].public_key) &&
        RSAVerificationRelation(in_state.counters[counter_index_in].public_key, new_counter_value_encoding_in + message_in, request_attestation_in) &&

        //- Most of the state stays the same...

        |out_state.counters| == |in_state.counters| &&
        (forall i :: 0 <= i < |in_state.counters| && i != counter_index_in ==> out_state.counters[i] == in_state.counters[i]) &&
        out_state.counters[counter_index_in].public_key == in_state.counters[counter_index_in].public_key &&

        //- ...except for the counter value for the counter with the given index...

        out_state.counters[counter_index_in].counter_value == new_counter_value_in &&

        //- ...and an attestation is returned.

        TrInc_statement_out == TrIncCounterAdvanceStatement(counter_index_in, in_state.counters[counter_index_in].counter_value,
                                                            new_counter_value_in, message_in) &&
        TrInc_attestation_out == RSASignature(common_state.key_pair, TrInc_statement_out)
}
