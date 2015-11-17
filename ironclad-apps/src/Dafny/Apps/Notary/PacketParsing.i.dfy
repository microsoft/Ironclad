//-<NuBuild BasmEnableSymdiff true />
include "PacketParsing.c.dfy"
include "../../Libraries/Crypto/RSA/RSA.i.dfy"
include "../../Libraries/Util/Halter.i.dfy"

//-//////////////////////////
//- Request parsing
//-//////////////////////////

static predicate RequestValid (request:NotaryRequest)
{
    match request
        case InvalidRequest_ctor => true
        case GetQuoteRequest_ctor(nonce_external) => IsByteSeq(nonce_external) && |nonce_external| == 20
        case AdvanceCounterRequest_ctor(message) => IsByteSeq(message)
}

static method ParseRequestPacket (data:seq<int>) returns (request:NotaryRequest)
    requires IsByteSeq(data);
    requires public(data);
    ensures RequestParsedCorrectly(data, request);
    ensures RequestValid(request);
    ensures public(request);
{
    if |data| == 0 {
        request := InvalidRequest_ctor();
        return;
    }
    if data[0] == 1 {
        request := ParseGetQuoteRequestPacket(data);
        return;
    }
    if data[0] == 2 {
        request := ParseAdvanceCounterRequestPacket(data);
        return;
    }
    request := InvalidRequest_ctor();
}

static method ParseGetQuoteRequestPacket (data:seq<int>) returns (request:NotaryRequest)
    requires IsByteSeq(data);
    requires |data| > 0;
    requires data[0] == 1;
    requires public(data);
    ensures GetQuoteRequestParsedCorrectly(data, request);
    ensures RequestValid(request);
    ensures public(request);
{
    if |data| < 21 {
        request := InvalidRequest_ctor();
        return;
    }
    var nonce_external := data[1..21];
    return GetQuoteRequest_ctor(nonce_external);
}

static method ParseAdvanceCounterRequestPacket (data:seq<int>) returns (request:NotaryRequest)
    requires IsByteSeq(data);
    requires |data| > 0;
    requires data[0] == 2;
    requires public(data);
    ensures AdvanceCounterRequestParsedCorrectly(data, request);
    ensures RequestValid(request);
    ensures public(request);
{
    if |data| < 2 {
        request := InvalidRequest_ctor();
        return;
    }
    var message_len := data[1];
    if |data| < 2 + message_len {
        request := InvalidRequest_ctor();
        return;
    }
    request := AdvanceCounterRequest_ctor(data[2..2+message_len]);
}

//-//////////////////////////
//- Response forming
//-//////////////////////////

static predicate WellformedResponse (response:NotaryResponse)
{
    match response
        case NullResponse_ctor => true

        case GetQuoteResponse_ctor(error_code, encoded_public_key, pcr_info_bytes, sig_bytes) =>
            Word32(error_code)
            && Word32(|encoded_public_key|)
            && Word32(|pcr_info_bytes|)
            && Word32(|sig_bytes|)
            && IsByteSeq(encoded_public_key)
            && IsByteSeq(pcr_info_bytes)
            && IsByteSeq(sig_bytes)

        case AdvanceCounterResponse_ctor(error_code, statement, attestation) =>
            Word32(error_code)
            && Word32(|statement|)
            && Word32(|attestation|)
            && IsByteSeq(statement)
            && IsByteSeq(attestation)
}

static method FormResponsePacket (response:NotaryResponse) returns (data:seq<int>)
    requires WellformedResponse(response);
    requires public(response);
    ensures IsByteSeq(data);
    ensures ResponseFormedCorrectly(response, data);
    ensures public(data);
{
    lemma_2toX();

    match response {
        case NullResponse_ctor =>
            data := [0];
            assert ResponseFormedCorrectly(response, data);

        case GetQuoteResponse_ctor(get_quote_error_code, encoded_public_key, pcr_info_bytes, sig_bytes) =>
            var get_quote_error_code_encoded := BEWordToFourBytes_impl(get_quote_error_code);
            var encoded_public_key_len_encoded := BEWordToFourBytes_impl(|encoded_public_key|);
            var pcr_info_bytes_len_encoded := BEWordToFourBytes_impl(|pcr_info_bytes|);
            var sig_bytes_len_encoded := BEWordToFourBytes_impl(|sig_bytes|);
            data := [1] + get_quote_error_code_encoded + encoded_public_key_len_encoded + pcr_info_bytes_len_encoded +
                    sig_bytes_len_encoded + encoded_public_key + pcr_info_bytes + sig_bytes;
            assert forall i :: 0 <= i < |data| ==> IsByte(data[i]);
            assert ResponseFormedCorrectly(response, data);

        case AdvanceCounterResponse_ctor(advance_error_code, notary_statement, notary_attestation) =>
            var advance_error_code_encoded := BEWordToFourBytes_impl(advance_error_code);
            var notary_statement_len_encoded := BEWordToFourBytes_impl(|notary_statement|);
            var notary_attestation_len_encoded := BEWordToFourBytes_impl(|notary_attestation|);
            data := [2] + advance_error_code_encoded + notary_statement_len_encoded + notary_attestation_len_encoded +
                    notary_statement + notary_attestation;
            assert forall i :: 0 <= i < |data| ==> IsByte(data[i]);
            assert ResponseFormedCorrectly(response, data);
    }
}
