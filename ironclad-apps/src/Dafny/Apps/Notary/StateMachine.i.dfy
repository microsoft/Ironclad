//-<NuBuild BasmEnableSymdiff true />
include "StateMachine.s.dfy"
include "PacketParsing.i.dfy"
include "Notary.i.dfy"
include "../../Libraries/Crypto/RSA/RSA.i.dfy"
include "../../Libraries/Crypto/RSA/RSAOps.i.dfy"
include "../../Libraries/Net/Udp.i.dfy"
include "../../Libraries/Util/Halter.i.dfy"
include "../../Libraries/Util/relational.i.dfy"

method {:timeLimitMultiplier 6} HandleOneRequest (request:NotaryRequest, notary_state_in:NotaryStateImpl, common_state_in:CommonStateImpl)
                        returns (response:NotaryResponse, notary_state_out:NotaryStateImpl, common_state_out:CommonStateImpl)
    requires NotaryStateImplValid(notary_state_in);
    requires CommonStateImplValid(common_state_in);
    requires common_state_in.key_pair.pub.size >= 1024 / 8;
    requires TPM_ready();
    requires current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state_in), TPM);
    requires current_notary_state == NotaryStateMachine_ctor(true, NotaryStateImplToSpec(notary_state_in));
    requires RequestValid(request);

    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_notary_state;
    modifies this`current_common_state;

    ensures NotaryStateImplValid(notary_state_out);
    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM));
    ensures WellformedResponse(response);
    ensures current_notary_state == NotaryStateMachine_ctor(true, NotaryStateImplToSpec(notary_state_out));
    ensures current_common_state == old(current_common_state)[TPM := TPM];
    ensures CommonStateImplValid(common_state_out);
    ensures CommonStateImplToSpec(common_state_out) == CommonStateImplToSpec(common_state_in);

    requires public(NotaryStateImplToSpec(notary_state_in));
    requires public(request);
    ensures public(NotaryStateImplToSpec(notary_state_out));
    ensures public(response);
{
    ghost var old_TPM := TPM;

    match request {
        case InvalidRequest_ctor =>
            notary_state_out := notary_state_in;
            response := NullResponse_ctor();
            common_state_out := common_state_in;

        case GetQuoteRequest_ctor(nonce_external) =>
            var encoded_public_key:seq<int>, pcr_info_bytes:seq<int>, sig_bytes:seq<int>;
            common_state_out, encoded_public_key, pcr_info_bytes, sig_bytes := HandleGetQuoteRequest(common_state_in, nonce_external);
            ghost var declassified_encoded_public_key, declassified_pcr_info_bytes, declassified_sig_bytes :=
                AdvanceCommonStateMachineViaGetQuote(nonce_external, encoded_public_key, pcr_info_bytes, sig_bytes);
            var usable_encoded_public_key := UseDeclassifiedByteSequence(encoded_public_key, declassified_encoded_public_key);
            var usable_pcr_info_bytes := UseDeclassifiedByteSequence(pcr_info_bytes, declassified_pcr_info_bytes);
            var usable_sig_bytes := UseDeclassifiedByteSequence(sig_bytes, declassified_sig_bytes);
            notary_state_out := notary_state_in;
            response := GetQuoteResponse_ctor(0, usable_encoded_public_key, usable_pcr_info_bytes, usable_sig_bytes);

        case AdvanceCounterRequest_ctor(message) =>
            var error_code:int, notary_statement:seq<int>, notary_attestation:seq<int>;
            notary_state_out, error_code, notary_statement, notary_attestation :=
                NotaryAdvanceCounter(notary_state_in, common_state_in, message);
            var usable_notary_attestation:seq<int>;
            if error_code != 0 {
                usable_notary_attestation := [];
            }
            else {
                ghost var declassified_notary_attestation :=
                    AdvanceNotaryStateMachineViaAdvanceCounter(message, NotaryStateImplToSpec(notary_state_out),
                                                               notary_statement, notary_attestation);
                usable_notary_attestation := UseDeclassifiedByteSequence(notary_attestation, declassified_notary_attestation);
            }
            response := AdvanceCounterResponse_ctor(error_code, notary_statement, usable_notary_attestation);
            common_state_out := common_state_in;
    }
}

method HandleOneRequestRaw (request_bytes:seq<int>, notary_state_in:NotaryStateImpl, common_state_in:CommonStateImpl)
                           returns (response_bytes:seq<int>, notary_state_out:NotaryStateImpl, common_state_out:CommonStateImpl)
    requires NotaryStateImplValid(notary_state_in);
    requires CommonStateImplValid(common_state_in);
    requires common_state_in.key_pair.pub.size >= 1024 / 8;
    requires TPM_ready();
    requires current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state_in), TPM);
    requires current_notary_state == NotaryStateMachine_ctor(true, NotaryStateImplToSpec(notary_state_in));
    requires IsByteSeq(request_bytes);

    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_notary_state;
    modifies this`current_common_state;

    ensures NotaryStateImplValid(notary_state_out);
    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM));
    ensures IsByteSeq(response_bytes);
    ensures current_notary_state == NotaryStateMachine_ctor(true, NotaryStateImplToSpec(notary_state_out));
    ensures current_common_state == old(current_common_state)[TPM := TPM];
    ensures CommonStateImplValid(common_state_out);
    ensures CommonStateImplToSpec(common_state_out) == CommonStateImplToSpec(common_state_in);

    requires public(NotaryStateImplToSpec(notary_state_in));
    requires public(request_bytes);
    ensures public(NotaryStateImplToSpec(notary_state_out));
    ensures public(response_bytes);
{
    var request := ParseRequestPacket(request_bytes);
    var response:NotaryResponse;
    response, notary_state_out, common_state_out := HandleOneRequest(request, notary_state_in, common_state_in);
    response_bytes := FormResponsePacket(response);
}
