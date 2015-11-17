include "DiffPriv.s.dfy"

//-///////////////////////////
//- Request parsing
//-///////////////////////////

datatype DiffPrivRequest = InvalidRequest_ctor()
                         | GetQuoteRequest_ctor(nonce_external:seq<int>)
                         | InitializeDBRequest_ctor(budget:real)
                         | AddRowRequest_ctor(request_ciphertext:seq<int>)
                         | QueryRequest_ctor(q:QueryParameters);

static predicate RequestParsedCorrectly (data:seq<int>, request:DiffPrivRequest)
    requires IsByteSeq(data);
{
    if |data| == 0 then
        request.InvalidRequest_ctor?
    else if data[0] == 1 then
        GetQuoteRequestParsedCorrectly(data, request)
    else if data[0] == 2 then
        InitializeDBRequestParsedCorrectly(data, request)
    else if data[0] == 3 then
        AddRowRequestParsedCorrectly(data, request)
    else if data[0] == 4 then
        QueryRequestParsedCorrectly(data, request)
    else
        request.InvalidRequest_ctor?
}

static predicate GetQuoteRequestParsedCorrectly(data:seq<int>, request:DiffPrivRequest)
    requires |data| > 0;
    requires data[0] == 1;
{
    if |data| < 21 then
        request.InvalidRequest_ctor?
    else
        request.GetQuoteRequest_ctor?
        && request.nonce_external == data[1..21]
}

static predicate InitializeDBRequestParsedCorrectly (data:seq<int>, request:DiffPrivRequest)
    requires IsByteSeq(data);
    requires |data| > 0;
    requires data[0] == 2;
{
    if |data| < 9 then
        request.InvalidRequest_ctor?
    else
        (var fields := data[1          :4                         :4                        ];
        var                 _,         budget_num,                budget_den                :=
                            fields[0], BEByteSeqToInt(fields[1]), BEByteSeqToInt(fields[2]) ;
        if budget_den == 0 then
            request.InvalidRequest_ctor?
        else
            request.InitializeDBRequest_ctor? &&
            request.budget == real(budget_num) / real(budget_den))
}

static predicate AddRowRequestParsedCorrectly (data:seq<int>, request:DiffPrivRequest)
    requires IsByteSeq(data);
    requires |data| > 0;
    requires data[0] == 3;
{
    if |data| == 1 then
        request == InvalidRequest_ctor()
    else
        request == AddRowRequest_ctor(data[1..])
}

static predicate QueryRequestParsedCorrectly (data:seq<int>, request:DiffPrivRequest)
    requires IsByteSeq(data);
    requires |data| > 0;
    requires data[0] == 4;
{
    if |data| < 41 then
        request.InvalidRequest_ctor?
    else
    (
        var program_size := BEByteSeqToInt(data[1..5]);
        if program_size < 0 || |data| < 41 + program_size || program_size % 4 != 0 then
            request.InvalidRequest_ctor?
        else
            (var fields := data[5:4:4:4:4:4:4:4:4:4:program_size];
            var _, row_min, row_max, answer_units, answer_min, answer_max, alpha_num, alpha_den, beta_num, beta_den, program_encoding :=
                fields[0], BEByteSeqToInt(fields[1]), BEByteSeqToInt(fields[2]), BEByteSeqToInt(fields[3]),
                BEByteSeqToInt(fields[4]), BEByteSeqToInt(fields[5]), BEByteSeqToInt(fields[6]), BEByteSeqToInt(fields[7]),
                BEByteSeqToInt(fields[8]), BEByteSeqToInt(fields[9]), fields[10];
            if alpha_den == 0 || beta_den == 0 then
                request.InvalidRequest_ctor?
            else
                request.QueryRequest_ctor? &&
                request.q.row_min == row_min &&
                request.q.row_max == row_max &&
                request.q.answer_units == answer_units &&
                request.q.answer_min == answer_min &&
                request.q.answer_max == answer_max &&
                request.q.alpha == real(alpha_num) / real(alpha_den) &&
                request.q.beta == real(beta_num) / real(beta_den) &&
                request.q.program_encoding == BEIntToDigitSeq(power2(32), |program_encoding|/4, BEDigitSeqToInt(power2(8), program_encoding)))
    )
}

//-///////////////////////////
//- Response parsing
//-///////////////////////////

datatype DiffPrivResponse = NullResponse_ctor()
                          | GetQuoteResponse_ctor(get_quote_error_code:int, encoded_public_key:seq<int>, pcr_info_bytes:seq<int>, sig_bytes:seq<int>)
                          | InitializeDBResponse_ctor(init_error_code:int)
                          | AddRowResponse_ctor()
                          | QueryResponse_ctor(query_error_code:int, response:int);

static predicate ResponseFormedCorrectly (response:DiffPrivResponse, data:seq<int>)
    requires IsByteSeq(data);
{
    match response
        case NullResponse_ctor =>
            |data| >= 1 &&
            data[0] == 0

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

        case InitializeDBResponse_ctor(error_code) =>
            Word32(error_code)
            && data == [2] + BEWordToFourBytes(error_code)

        case AddRowResponse_ctor =>
            data == [3]
            //- The error code is not public, so we can't output it.

        case QueryResponse_ctor(error_code, response_value) =>
            Word32(error_code)
            && Word32(response_value)
            && data == [4] + BEWordToFourBytes(error_code) + BEWordToFourBytes(response_value)
}
