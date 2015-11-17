//-<NuBuild BasmEnableSymdiff true />
//-<NuBuild AddBoogieFlag /timeLimit:600 />
include "StateMachine.s.dfy"
include "DiffPriv.i.dfy"
include "DiffPrivPerformQuery.i.dfy"
include "StateMachine2.i.dfy"
include "../../Libraries/Net/Udp.i.dfy"
include "../../Libraries/Util/Halter.i.dfy"
include "../../Libraries/Util/relational.i.dfy"

method HandleQueryRequest(diffpriv_state_in:DiffPrivStateImpl, common_state:CommonStateImpl, q:QueryParametersImpl)
                         returns (diffpriv_state_out:DiffPrivStateImpl, response:DiffPrivResponse)
    requires CommonStateImplValid(common_state);
    requires TPM_ready();
    requires DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_in));
    requires current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state), TPM);
    requires current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_in));
    requires QueryParametersImplValid(q);

    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_diffpriv_state;
    modifies this`current_common_state;

    ensures DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_out));
    ensures TPM_ready();
    ensures WellformedResponse(response);
    ensures current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_out));
    ensures current_common_state == old(current_common_state)[TPM := TPM];

    requires public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_in)));
    requires public(q);
    ensures public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_out)));
    ensures public(response);
{
    var query_error_code:int, answer:int;
    query_error_code, answer, diffpriv_state_out := DiffPrivPerformQuery(diffpriv_state_in, q);
    var usable_answer:int;
    if query_error_code != 0 {
        usable_answer := 0;
    }
    else {
        ghost var declassified_answer :=
            AdvanceDiffPrivStateMachineByAnsweringQuery(QueryParametersImplToSpec(q),
                                                        DiffPrivStateImplToSpec(diffpriv_state_out),
                                                        answer);
        usable_answer := Asm_declassify_result(answer, declassified_answer);
    }
    response := QueryResponse_ctor(query_error_code, usable_answer);
}


method HandleOneRequest (request:DiffPrivRequestImpl, diffpriv_state_in:DiffPrivStateImpl, common_state_in:CommonStateImpl)
                        returns (response:DiffPrivResponse, diffpriv_state_out:DiffPrivStateImpl, common_state_out:CommonStateImpl)
    requires CommonStateImplValid(common_state_in);
    requires common_state_in.key_pair.pub.size >= 1024 / 8;
    requires TPM_ready();
    requires DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_in));
    requires current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state_in), TPM);
    requires current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_in));
    requires WellformedDiffPrivRequest(request);

    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_diffpriv_state;
    modifies this`current_common_state;

    ensures DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_out));
    ensures TPM_ready();
    ensures WellformedResponse(response);
    ensures current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_out));
    ensures current_common_state == old(current_common_state)[TPM := TPM];
    ensures CommonStateImplValid(common_state_out);
    ensures CommonStateImplToSpec(common_state_out) == CommonStateImplToSpec(common_state_in);

    requires public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_in)));
    requires public(request);
    ensures public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_out)));
    ensures public(response);
{
    match request {
        case InvalidRequestImpl_ctor =>
            response := NullResponse_ctor();
            diffpriv_state_out := diffpriv_state_in;
            common_state_out := common_state_in;

        case GetQuoteRequestImpl_ctor(nonce_external) =>
            diffpriv_state_out := diffpriv_state_in;
            response, common_state_out := HandleGetDiffPrivQuoteRequest(common_state_in, nonce_external);

        case InitializeDBRequestImpl_ctor(budget_num, budget_den) =>
            diffpriv_state_out, response := HandleInitializeDBRequest(diffpriv_state_in, budget_num, budget_den);
            common_state_out := common_state_in;

        case AddRowRequestImpl_ctor(request_ciphertext) =>
            diffpriv_state_out, response := HandleAddRowRequest(diffpriv_state_in, common_state_in, request_ciphertext);
            common_state_out := common_state_in;

        case QueryRequestImpl_ctor(q) =>
            diffpriv_state_out, response := HandleQueryRequest(diffpriv_state_in, common_state_in, q);
            common_state_out := common_state_in;
    }
}

method HandleOneRequestRaw (request_bytes:seq<int>, diffpriv_state_in:DiffPrivStateImpl, common_state_in:CommonStateImpl)
                           returns (response_bytes:seq<int>, diffpriv_state_out:DiffPrivStateImpl, common_state_out:CommonStateImpl)
    requires CommonStateImplValid(common_state_in);
    requires common_state_in.key_pair.pub.size >= 1024 / 8;
    requires TPM_ready();
    requires DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_in));
    requires current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state_in), TPM);
    requires current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_in));
    requires IsByteSeq(request_bytes);

    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_diffpriv_state;
    modifies this`current_common_state;

    ensures DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_out));
    ensures TPM_ready();
    ensures IsByteSeq(response_bytes);
    ensures current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_out));
    ensures current_common_state == old(current_common_state)[TPM := TPM];
    ensures CommonStateImplValid(common_state_out);
    ensures CommonStateImplToSpec(common_state_out) == CommonStateImplToSpec(common_state_in);

    requires public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_in)));
    requires public(request_bytes);
    ensures public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_out)));
    ensures public(response_bytes);
{
    var request := ParseRequestPacket(request_bytes);
    var response:DiffPrivResponse;
    response, diffpriv_state_out, common_state_out := HandleOneRequest(request, diffpriv_state_in, common_state_in);
    response_bytes := FormResponsePacket(response);
}
