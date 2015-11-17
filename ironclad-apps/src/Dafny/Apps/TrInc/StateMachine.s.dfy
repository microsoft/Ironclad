include "TrInc.s.dfy"

//-///////////////////////////
//- State machine
//-///////////////////////////

datatype TrIncStateMachine = TrIncStateMachine_ctor(initialized:bool, trinc_state:TrIncState)

ghost var {:readonly} current_trinc_state:TrIncStateMachine;

ghost method {:axiom} {:autoReq} InitializeTrIncStateMachine(trinc_state:TrIncState)
    requires !current_trinc_state.initialized;
    requires TrIncInitializeValid(trinc_state);
    ensures current_trinc_state == TrIncStateMachine_ctor(true, trinc_state);
    modifies this`current_trinc_state;

ghost method {:axiom} {:autoReq} AdvanceTrIncStateMachineViaCreateCounter
   (public_key_encoding_in:seq<int>, new_trinc_state:TrIncState, counter_index_out:nat)
    requires current_trinc_state.initialized;
    requires current_common_state.initialized;
    requires current_common_state.TPM == TPM;
    requires public(public_key_encoding_in);
    requires public(new_trinc_state);
    requires TrIncCreateCounterValid(current_trinc_state.trinc_state, new_trinc_state, current_common_state.common_state,
                                     public_key_encoding_in, counter_index_out);
    modifies this`current_trinc_state;
    ensures current_trinc_state == old(current_trinc_state)[trinc_state := new_trinc_state];

ghost method {:axiom} {:autoReq} AdvanceTrIncStateMachineViaAdvanceCounter
    (counter_index_in:nat, new_counter_value_encoding_in:seq<int>, message_in:seq<int>, message_attestation_in:seq<int>,
     new_trinc_state:TrIncState, trinc_statement_out:seq<int>, trinc_attestation_out:seq<int>)
    returns (declassified_trinc_attestation_out:seq<int>)
    requires current_trinc_state.initialized;
    requires current_common_state.initialized;
    requires current_common_state.TPM == TPM;
    requires public(counter_index_in);
    requires public(new_counter_value_encoding_in);
    requires public(message_in);
    requires public(message_attestation_in);
    requires public(new_trinc_state);
    requires TrIncAdvanceCounterValid(current_trinc_state.trinc_state, new_trinc_state, current_common_state.common_state,
                                      counter_index_in, new_counter_value_encoding_in, message_in, message_attestation_in,
                                      trinc_statement_out, trinc_attestation_out);
    modifies this`current_trinc_state;
    ensures current_trinc_state == old(current_trinc_state)[trinc_state := new_trinc_state];
    ensures IsByteSeqOfLen(declassified_trinc_attestation_out, |trinc_attestation_out|);
    ensures public(|trinc_attestation_out|);
    ensures relation(forall i :: left(i) == right(i) && 0 <= left(i) < left(|declassified_trinc_attestation_out|) ==>
                                 declassified(left(declassified_trinc_attestation_out[i]), right(declassified_trinc_attestation_out[i]),
                                              left(trinc_attestation_out[i]), right(trinc_attestation_out[i])));
