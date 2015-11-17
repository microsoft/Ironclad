//-<NuBuild BasmEnableSymdiff true />
include "StateMachine.s.dfy"
include "PacketParsing.i.dfy"
include "TrInc.i.dfy"
include "../../Libraries/Crypto/RSA/RSA.i.dfy"
include "../../Libraries/Crypto/RSA/RSAOps.i.dfy"
include "../../Libraries/Net/Udp.i.dfy"
include "../../Libraries/Util/relational.i.dfy"

method {:timeLimitMultiplier 4} HandleOneRequest (request:TrIncRequest, trinc_state_in:TrIncStateImpl, common_state_in:CommonStateImpl)
                        returns (response:TrIncResponse, trinc_state_out:TrIncStateImpl, common_state_out:CommonStateImpl)
    requires TrIncStateImplValid(trinc_state_in);
    requires CommonStateImplValid(common_state_in);
    requires common_state_in.key_pair.pub.size >= 1024 / 8;
    requires TPM_ready();
    requires current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state_in), TPM);
    requires current_trinc_state == TrIncStateMachine_ctor(true, TrIncStateImplToSpec(trinc_state_in));
    requires RequestValid(request);

    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_trinc_state;
    modifies this`current_common_state;

    ensures TrIncStateImplValid(trinc_state_out);
    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM));
    ensures WellformedResponse(response);
    ensures current_trinc_state == TrIncStateMachine_ctor(true, TrIncStateImplToSpec(trinc_state_out));
    ensures current_common_state == old(current_common_state)[TPM := TPM];
    ensures CommonStateImplValid(common_state_out);
    ensures CommonStateImplToSpec(common_state_out) == CommonStateImplToSpec(common_state_in);

    requires public(TrIncStateImplToSpec(trinc_state_in));
    requires public(request);
    ensures public(TrIncStateImplToSpec(trinc_state_out));
    ensures public(response);
{
    match request {
        case InvalidRequest_ctor =>
            response := NullResponse_ctor();
            trinc_state_out := trinc_state_in;
            common_state_out := common_state_in;

        case GetQuoteRequest_ctor(nonce_external) =>
            var encoded_public_key:seq<int>, pcr_info_bytes:seq<int>, sig_bytes:seq<int>;
            common_state_out, encoded_public_key, pcr_info_bytes, sig_bytes := HandleGetQuoteRequest(common_state_in, nonce_external);
            ghost var declassified_encoded_public_key, declassified_pcr_info_bytes, declassified_sig_bytes :=
                AdvanceCommonStateMachineViaGetQuote(nonce_external, encoded_public_key, pcr_info_bytes, sig_bytes);
            var usable_encoded_public_key := UseDeclassifiedByteSequence(encoded_public_key, declassified_encoded_public_key);
            var usable_pcr_info_bytes := UseDeclassifiedByteSequence(pcr_info_bytes, declassified_pcr_info_bytes);
            var usable_sig_bytes := UseDeclassifiedByteSequence(sig_bytes, declassified_sig_bytes);
            trinc_state_out := trinc_state_in;
            response := GetQuoteResponse_ctor(0, usable_encoded_public_key, usable_pcr_info_bytes, usable_sig_bytes);

        case CreateCounterRequest_ctor(public_key_encoding) =>
            var create_error_code:int, counter_index:nat;
            trinc_state_out, create_error_code, counter_index := TrIncCreateCounter(trinc_state_in, common_state_in, public_key_encoding);
            if create_error_code == 0 {
                AdvanceTrIncStateMachineViaCreateCounter(public_key_encoding, TrIncStateImplToSpec(trinc_state_out), counter_index);
            }
            response := CreateCounterResponse_ctor(create_error_code, counter_index);
            common_state_out := common_state_in;

        case AdvanceCounterRequest_ctor(counter_index, new_counter_value_encoding, message, message_attestation) =>
            var advance_error_code:int, trinc_statement:seq<int>, trinc_attestation:seq<int>;
            trinc_state_out, advance_error_code, trinc_statement, trinc_attestation :=
                TrIncAdvanceCounter(trinc_state_in, common_state_in, counter_index, new_counter_value_encoding, message, message_attestation);
            var usable_trinc_attestation:seq<int>;
            if advance_error_code != 0 {
                usable_trinc_attestation := [];
            }
            else {
                ghost var declassified_trinc_attestation :=
                    AdvanceTrIncStateMachineViaAdvanceCounter(counter_index, new_counter_value_encoding, message,
                                                              message_attestation, TrIncStateImplToSpec(trinc_state_out),
                                                              trinc_statement, trinc_attestation);
                usable_trinc_attestation := UseDeclassifiedByteSequence(trinc_attestation, declassified_trinc_attestation);
            }
            response := AdvanceCounterResponse_ctor(advance_error_code, trinc_statement, usable_trinc_attestation);
            common_state_out := common_state_in;
    }
}

method HandleOneRequestRaw (request_bytes:seq<int>, trinc_state_in:TrIncStateImpl, common_state_in:CommonStateImpl)
                           returns (response_bytes:seq<int>, trinc_state_out:TrIncStateImpl, common_state_out:CommonStateImpl)
    requires TrIncStateImplValid(trinc_state_in);
    requires CommonStateImplValid(common_state_in);
    requires common_state_in.key_pair.pub.size >= 1024 / 8;
    requires TPM_ready();
    requires current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state_in), TPM);
    requires current_trinc_state == TrIncStateMachine_ctor(true, TrIncStateImplToSpec(trinc_state_in));
    requires IsByteSeq(request_bytes);

    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_trinc_state;
    modifies this`current_common_state;

    ensures TrIncStateImplValid(trinc_state_out);
    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM));
    ensures IsByteSeq(response_bytes);
    ensures current_trinc_state == TrIncStateMachine_ctor(true, TrIncStateImplToSpec(trinc_state_out));
    ensures current_common_state == old(current_common_state)[TPM := TPM];
    ensures CommonStateImplValid(common_state_out);
    ensures CommonStateImplToSpec(common_state_out) == CommonStateImplToSpec(common_state_in);

    requires public(TrIncStateImplToSpec(trinc_state_in));
    requires public(request_bytes);
    ensures public(TrIncStateImplToSpec(trinc_state_out));
    ensures public(response_bytes);
{
    var request := ParseRequestPacket(request_bytes);
    var response:TrIncResponse;
    response, trinc_state_out, common_state_out := HandleOneRequest(request, trinc_state_in, common_state_in);
    response_bytes := FormResponsePacket(response);
}
