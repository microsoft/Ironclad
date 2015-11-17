include "PassHash.s.dfy"

datatype StateMachine = StateMachine_ctor(initialized:bool, passhash_state:PassHashState, TPM:TPM_struct)

ghost var {:readonly} current_state:StateMachine;

ghost method {:axiom} InitializeStateMachine(passhash_state:PassHashState)
    requires !current_state.initialized;
    requires PassHashInitializeValid(passhash_state, current_state.TPM, TPM);
    ensures current_state == StateMachine_ctor(true, passhash_state, TPM);
    modifies this`current_state;

ghost method {:axiom} {:autoReq} AdvanceStateMachineViaPerformHash(message_in:seq<int>, salt_in:seq<int>,
                                                                   error_code_out:int, hash_out:seq<int>)
                                                                   returns (declassified_hash_out:seq<int>)
    requires current_state.initialized;
    requires current_state.TPM == TPM;
    requires public(message_in);
    requires public(salt_in);
    requires PassHashPerformHashValid(current_state.passhash_state, message_in, salt_in, error_code_out, hash_out);

    ensures IsByteSeqOfLen(declassified_hash_out, |hash_out|);
    ensures relation(forall i :: left(i) == right(i) && 0 <= left(i) < left(|declassified_hash_out|) ==>
                                 declassified(left(declassified_hash_out[i]), right(declassified_hash_out[i]),
                                              left(hash_out[i]), right(hash_out[i])));
