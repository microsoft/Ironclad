include "TrInc.s.dfy"

//-///////////////////////////
//- Request parsing
//-///////////////////////////

datatype TrIncRequest = InvalidRequest_ctor()
                        | GetQuoteRequest_ctor(nonce_external:seq<int>)
                        | CreateCounterRequest_ctor(public_key_encoding:seq<int>)
                        | AdvanceCounterRequest_ctor(counter_index:nat, new_counter_value_encoding:seq<int>, message:seq<int>, request_attestation:seq<int>)

static predicate RequestParsedCorrectly (data:seq<int>, request:TrIncRequest)
    requires IsByteSeq(data);
{
    if |data| == 0 then
        request.InvalidRequest_ctor?
    else if data[0] == 1 then
        GetQuoteRequestParsedCorrectly(data, request)
    else if data[0] == 2 then
        CreateCounterRequestParsedCorrectly(data, request)
    else if data[0] == 3 then
        AdvanceCounterRequestParsedCorrectly(data, request)
    else
        request.InvalidRequest_ctor?
}

static predicate GetQuoteRequestParsedCorrectly(data:seq<int>, request:TrIncRequest)
    requires |data| > 0;
    requires data[0] == 1;
{
    if |data| < 21 then
        request.InvalidRequest_ctor?
    else
        request.GetQuoteRequest_ctor?
        && request.nonce_external == data[1..21]
}

static predicate CreateCounterRequestParsedCorrectly (data:seq<int>, request:TrIncRequest)
    requires IsByteSeq(data);
    requires |data| > 0;
    requires data[0] == 2;
{
    if |data| < 5 then
        request.InvalidRequest_ctor?
    else
    (
        var public_key_length := BEByteSeqToInt(data[1..5]);
        if public_key_length < 0 || |data| < 5 + public_key_length then
            request.InvalidRequest_ctor?
        else
            request.CreateCounterRequest_ctor? &&
            request.public_key_encoding == data[5..5+public_key_length]
    )
}

static predicate AdvanceCounterRequestParsedCorrectly (data:seq<int>, request:TrIncRequest)
    requires IsByteSeq(data);
    requires |data| > 0;
    requires data[0] == 3;
{
    if |data| < 17 then
        request.InvalidRequest_ctor?
    else
    (
        var counter_index := BEByteSeqToInt(data[1..5]);
        var new_counter_len := BEByteSeqToInt(data[5..9]);
        var message_len := BEByteSeqToInt(data[9..13]);
        var request_attestation_len := BEByteSeqToInt(data[13..17]);
        if new_counter_len < 0 || message_len < 0 || request_attestation_len < 0 || |data| < 17 + new_counter_len + message_len + request_attestation_len then
            request.InvalidRequest_ctor?
        else
            request.AdvanceCounterRequest_ctor? &&
            request.counter_index == counter_index &&
            request.new_counter_value_encoding == data[17..17+new_counter_len] &&
            request.message == data[17+new_counter_len..17+new_counter_len+message_len] &&
            request.request_attestation == data[17+new_counter_len+message_len..17+new_counter_len+message_len+request_attestation_len]
    )
}

//-///////////////////////////
//- Response parsing
//-///////////////////////////

datatype TrIncResponse = NullResponse_ctor()
                         | GetQuoteResponse_ctor(get_quote_error_code:int, encoded_public_key:seq<int>, pcr_info_bytes:seq<int>, sig_bytes:seq<int>)
                         | CreateCounterResponse_ctor(create_error_code:int, counter_index:nat)
                         | AdvanceCounterResponse_ctor(advance_error_code:int, TrInc_statement:seq<int>, TrInc_attestation:seq<int>)

static function ResponseFormedCorrectly (response:TrIncResponse, data:seq<int>) : bool
    requires IsByteSeq(data);
{
    match response
        case NullResponse_ctor =>
            |data| >= 1 && data[0] == 0

        case GetQuoteResponse_ctor(get_quote_error_code, encoded_public_key, pcr_info_bytes, sig_bytes) =>
            Word32(get_quote_error_code)
            && Word32(|encoded_public_key|)
            && Word32(|pcr_info_bytes|)
            && Word32(|sig_bytes|)
            && IsByteSeq(encoded_public_key)
            && IsByteSeq(pcr_info_bytes)
            && IsByteSeq(sig_bytes)
            && data == [1] + BEWordToFourBytes(get_quote_error_code) + BEWordToFourBytes(|encoded_public_key|) +
                       BEWordToFourBytes(|pcr_info_bytes|) + BEWordToFourBytes(|sig_bytes|) + encoded_public_key +
                       pcr_info_bytes + sig_bytes

        case CreateCounterResponse_ctor(create_error_code, counter_index) =>
            Word32(create_error_code)
            && Word32(counter_index)
            && data == [2] + BEWordToFourBytes(create_error_code) + BEWordToFourBytes(counter_index)

        case AdvanceCounterResponse_ctor(advance_error_code, TrInc_statement, TrInc_attestation) =>
            Word32(advance_error_code)
            && IsByteSeq(TrInc_statement)
            && IsByteSeq(TrInc_attestation)
            && Word32(|TrInc_statement|)
            && Word32(|TrInc_attestation|)
            && data == [3] + BEWordToFourBytes(advance_error_code) + BEWordToFourBytes(|TrInc_statement|) +
                       BEWordToFourBytes(|TrInc_attestation|) + TrInc_statement + TrInc_attestation
}
