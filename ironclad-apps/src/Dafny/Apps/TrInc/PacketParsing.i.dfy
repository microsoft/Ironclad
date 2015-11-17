//-<NuBuild BasmEnableSymdiff true />
include "PacketParsing.c.dfy"
include "../../Libraries/Util/seqs_transforms.i.dfy"

//-//////////////////////////
//- Request parsing
//-//////////////////////////

static predicate RequestValid (request:TrIncRequest)
{
    match request
        case InvalidRequest_ctor => true
        case GetQuoteRequest_ctor(nonce_external) => IsByteSeq(nonce_external) && |nonce_external| == 20
        case CreateCounterRequest_ctor(public_key_encoding) => IsByteSeq(public_key_encoding)
        case AdvanceCounterRequest_ctor(counter_index, new_counter_value_encoding, message, message_attestation) =>
            Word32(counter_index) && IsByteSeq(new_counter_value_encoding) && IsByteSeq(message) && IsByteSeq(message_attestation)
}

static method ParseRequestPacket (data:seq<int>) returns (request:TrIncRequest)
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
        request := ParseCreateCounterRequestPacket(data);
        return;
    }
    if data[0] == 3 {
        request := ParseAdvanceCounterRequestPacket(data);
        return;
    }
    request := InvalidRequest_ctor();
}

static method ParseGetQuoteRequestPacket (data:seq<int>) returns (request:TrIncRequest)
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

static method ParseCreateCounterRequestPacket (data:seq<int>) returns (request:TrIncRequest)
    requires IsByteSeq(data);
    requires |data| > 0;
    requires data[0] == 2;
    requires public(data);
    ensures CreateCounterRequestParsedCorrectly(data, request);
    ensures RequestValid(request);
    ensures public(request);
{
    request := InvalidRequest_ctor();
    if |data| < 5 {
        request := InvalidRequest_ctor();
        return;
    }

    var public_key_len := BEFourBytesToWord_impl(data[1..5]);
    if public_key_len < 0 || |data| < 5 + public_key_len {
        request := InvalidRequest_ctor();
        return;
    }

    request := CreateCounterRequest_ctor(data[5..5+public_key_len]);
}

static method ParseAdvanceCounterRequestPacket (data:seq<int>) returns (request:TrIncRequest)
    requires IsByteSeq(data);
    requires |data| > 0;
    requires data[0] == 3;
    requires public(data);
    ensures AdvanceCounterRequestParsedCorrectly(data, request);
    ensures RequestValid(request);
    ensures public(request);
{
    if |data| < 17 {
        request := InvalidRequest_ctor();
        return;
    }

    var counter_index := BEFourBytesToWord_impl(data[1..5]);
    var new_counter_len := BEFourBytesToWord_impl(data[5..9]);
    var message_len := BEFourBytesToWord_impl(data[9..13]);
    var request_attestation_len := BEFourBytesToWord_impl(data[13..17]);

    if new_counter_len < 0 || message_len < 0 || request_attestation_len < 0 || |data| < 17 + new_counter_len + message_len + request_attestation_len {
        request := InvalidRequest_ctor();
        return;
    }

    lemma_2toX();
    reveal_power2();
    assert Word32(counter_index);

    request := AdvanceCounterRequest_ctor(counter_index, data[17..17+new_counter_len],
                                          data[17+new_counter_len..17+new_counter_len+message_len],
                                          data[17+new_counter_len+message_len..17+new_counter_len+message_len+request_attestation_len]);
}

//-//////////////////////////
//- Response forming
//-//////////////////////////

static predicate WellformedResponse (response:TrIncResponse)
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

        case CreateCounterResponse_ctor(error_code, counter_index) => Word32(error_code) && Word32(counter_index)

        case AdvanceCounterResponse_ctor(error_code, statement, attestation) =>
                 Word32(error_code) && Word32(|statement|) && Word32(|attestation|) && IsByteSeq(statement) && IsByteSeq(attestation)
}

static method FormResponsePacket (response:TrIncResponse) returns (data:seq<int>)
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

        case GetQuoteResponse_ctor(get_quote_error_code, encoded_public_key, pcr_info_bytes, sig_bytes) =>
            var get_quote_error_code_encoded := BEWordToFourBytes_impl(get_quote_error_code);
            var encoded_public_key_len_encoded := BEWordToFourBytes_impl(|encoded_public_key|);
            var pcr_info_bytes_len_encoded := BEWordToFourBytes_impl(|pcr_info_bytes|);
            var sig_bytes_len_encoded := BEWordToFourBytes_impl(|sig_bytes|);
            data := [1] + get_quote_error_code_encoded + encoded_public_key_len_encoded + pcr_info_bytes_len_encoded +
                    sig_bytes_len_encoded + encoded_public_key + pcr_info_bytes + sig_bytes;
            assert forall i :: 0 <= i < |data| ==> IsByte(data[i]);
            assert ResponseFormedCorrectly(response, data);

        case CreateCounterResponse_ctor(create_error_code, counter_index) =>
            var create_error_code_encoded := BEWordToFourBytes_impl(create_error_code);
            var counter_index_encoded := BEWordToFourBytes_impl(counter_index);
            data := [2] + create_error_code_encoded + counter_index_encoded;
            assert ResponseFormedCorrectly(response, data);

        case AdvanceCounterResponse_ctor(advance_error_code, TrInc_statement, TrInc_attestation) =>
            var advance_error_code_encoded := BEWordToFourBytes_impl(advance_error_code);
            var TrInc_statement_len_encoded := BEWordToFourBytes_impl(|TrInc_statement|);
            var TrInc_attestation_len_encoded := BEWordToFourBytes_impl(|TrInc_attestation|);
            data := [3] + advance_error_code_encoded + TrInc_statement_len_encoded + TrInc_attestation_len_encoded +
                    TrInc_statement + TrInc_attestation;
            assert IsByteSeq(data);
            assert ResponseFormedCorrectly(response, data);
    }
}
