include "Notary.s.dfy"
include "../Common/CommonState.s.dfy"

//-///////////////////////////
//- State machine
//-///////////////////////////

datatype NotaryStateMachine = NotaryStateMachine_ctor(initialized:bool, notary_state:NotaryState)

ghost var {:readonly} current_notary_state:NotaryStateMachine;

ghost method {:axiom} {:autoReq} InitializeNotaryStateMachine(notary_state:NotaryState)
    requires !current_notary_state.initialized;
    requires NotaryInitializeValid(notary_state);
    ensures current_notary_state == NotaryStateMachine_ctor(true, notary_state);
    modifies this`current_notary_state;

ghost method {:axiom} {:autoReq} AdvanceNotaryStateMachineViaAdvanceCounter
   (message_in:seq<int>, new_notary_state:NotaryState, notary_statement_out:seq<int>, notary_attestation_out:seq<int>)
   returns (declassified_notary_attestation_out:seq<int>)
    requires current_notary_state.initialized;
    requires current_common_state.initialized;
    requires current_common_state.TPM == TPM;
    requires public(message_in);
    requires public(new_notary_state);
    requires NotaryAdvanceCounterValid(current_notary_state.notary_state, new_notary_state, current_common_state.common_state, message_in,
                                       notary_statement_out, notary_attestation_out);
    modifies this`current_notary_state;
    ensures current_notary_state == old(current_notary_state)[notary_state := new_notary_state];
    ensures IsByteSeqOfLen(declassified_notary_attestation_out, |notary_attestation_out|);
    ensures public(|notary_attestation_out|);
    ensures relation(forall i :: left(i) == right(i) && 0 <= left(i) < left(|declassified_notary_attestation_out|) ==>
                                 declassified(left(declassified_notary_attestation_out[i]), right(declassified_notary_attestation_out[i]),
                                              left(notary_attestation_out[i]), right(notary_attestation_out[i])));
