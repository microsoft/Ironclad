include "DiffPriv.s.dfy"
include "../../Drivers/TPM/tpm-device.s.dfy"
include "../../Libraries/Crypto/RSA/RSASpec.s.dfy"
include "../../Libraries/Util/be_sequences.s.dfy"

//-///////////////////////////
//- State machine
//-///////////////////////////

datatype DiffPrivStateMachine = DiffPrivStateMachine_ctor(initialized:bool, diffpriv_state:DiffPrivState)

ghost var {:readonly} current_diffpriv_state:DiffPrivStateMachine;

ghost method {:axiom} {:autoReq} InitializeDiffPrivStateMachine(diffpriv_state:DiffPrivState)
    requires !current_diffpriv_state.initialized;
    requires DiffPrivInitializeValid(diffpriv_state);
    ensures current_diffpriv_state == DiffPrivStateMachine_ctor(true, diffpriv_state);
    modifies this`current_diffpriv_state;

ghost method {:axiom} {:autoReq} AdvanceDiffPrivStateMachineByInitializingDB(budget_in:real, new_diffpriv_state:DiffPrivState)
    requires current_diffpriv_state.initialized;
    requires current_common_state.initialized;
    requires current_common_state.TPM == TPM;
    requires public(budget_in);
    requires public(PublicPartOfDiffPrivState(new_diffpriv_state));
    requires DiffPrivInitializedDBCorrectly(current_diffpriv_state.diffpriv_state, new_diffpriv_state, budget_in);
    modifies this`current_diffpriv_state;
    ensures current_diffpriv_state == old(current_diffpriv_state)[diffpriv_state := new_diffpriv_state];

ghost method {:axiom} {:autoReq} AdvanceDiffPrivStateMachineByAddingRow
    (request_ciphertext_in:seq<int>, new_diffpriv_state:DiffPrivState)
    requires current_diffpriv_state.initialized;
    requires current_common_state.initialized;
    requires current_common_state.TPM == TPM;
    requires public(request_ciphertext_in);
    requires public(PublicPartOfDiffPrivState(new_diffpriv_state));
    requires DiffPrivRowAddedCorrectly(current_diffpriv_state.diffpriv_state, new_diffpriv_state,
                                       current_common_state.common_state.key_pair, request_ciphertext_in);
    modifies this`current_diffpriv_state;
    ensures current_diffpriv_state == old(current_diffpriv_state)[diffpriv_state := new_diffpriv_state];

ghost method {:axiom} {:autoReq} AdvanceDiffPrivStateMachineByAnsweringQuery
    (query_parameters_in:QueryParameters, new_diffpriv_state:DiffPrivState, response_out:int)
    returns (declassified_response_out:int)
    requires current_diffpriv_state.initialized;
    requires current_common_state.initialized;
    requires public(query_parameters_in);
    requires public(PublicPartOfDiffPrivState(new_diffpriv_state));
    requires DiffPrivQueryPerformedCorrectly(current_diffpriv_state.diffpriv_state, new_diffpriv_state, query_parameters_in,
                                             response_out, current_common_state.TPM, TPM);
    requires Word32(response_out);
    modifies this`current_common_state;
    modifies this`current_diffpriv_state;
    ensures current_common_state == old(current_common_state)[TPM := TPM];
    ensures current_diffpriv_state == old(current_diffpriv_state)[diffpriv_state := new_diffpriv_state];
    ensures relation(declassified(left(declassified_response_out), right(declassified_response_out), left(response_out), right(response_out)));
    ensures Word32(declassified_response_out);
