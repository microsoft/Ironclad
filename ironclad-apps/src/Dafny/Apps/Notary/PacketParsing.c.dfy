include "Notary.s.dfy"

//-///////////////////////////
//- Request parsing
//-///////////////////////////

datatype NotaryRequest = InvalidRequest_ctor()
                         | GetQuoteRequest_ctor(nonce_external:seq<int>)
                         | AdvanceCounterRequest_ctor(message:seq<int>)

static predicate RequestParsedCorrectly(data:seq<int>, request:NotaryRequest)
{
    if |data| == 0 then
        request.InvalidRequest_ctor?
    else if data[0] == 1 then
        GetQuoteRequestParsedCorrectly(data, request)
    else if data[0] == 2 then
        AdvanceCounterRequestParsedCorrectly(data, request)
    else
        request.InvalidRequest_ctor?
}

static predicate GetQuoteRequestParsedCorrectly(data:seq<int>, request:NotaryRequest)
    requires |data| > 0;
    requires data[0] == 1;
{
    if |data| < 21 then
        request.InvalidRequest_ctor?
    else
        request.GetQuoteRequest_ctor?
        && request.nonce_external == data[1..21]
}

static predicate AdvanceCounterRequestParsedCorrectly(data:seq<int>, request:NotaryRequest)
    requires |data| > 0;
    requires data[0] == 2;
{
    if |data| < 2 then
        request.InvalidRequest_ctor?
    else
    (
        var message_len := data[1];
        if message_len < 0 || |data| < 2 + message_len then
            request.InvalidRequest_ctor?
        else
            request.AdvanceCounterRequest_ctor?
            && request.message == data[2..2+message_len]
    )
}

//-///////////////////////////
//- Response parsing
//-///////////////////////////

datatype NotaryResponse = NullResponse_ctor()
                          | GetQuoteResponse_ctor(get_quote_error_code:int, encoded_public_key:seq<int>,
                                                  pcr_info_bytes:seq<int>, sig_bytes:seq<int>)
                          | AdvanceCounterResponse_ctor(advance_error_code:int, notary_statement:seq<int>, notary_attestation:seq<int>)

static predicate ResponseFormedCorrectly(response:NotaryResponse, data:seq<int>)
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

        case AdvanceCounterResponse_ctor(advance_error_code, notary_statement, notary_attestation) =>
            Word32(advance_error_code)
            && IsByteSeq(notary_statement)
            && IsByteSeq(notary_attestation)
            && Word32(|notary_statement|)
            && Word32(|notary_attestation|)
            && data == [2] + BEWordToFourBytes(advance_error_code) + BEWordToFourBytes(|notary_statement|) +
                       BEWordToFourBytes(|notary_attestation|) + notary_statement + notary_attestation
}
