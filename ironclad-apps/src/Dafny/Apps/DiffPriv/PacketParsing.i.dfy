//-<NuBuild BasmEnableSymdiff true />
include "PacketParsing.c.dfy"
include "../../Libraries/Util/seqs_transforms.i.dfy"

//-//////////////////////////
//- Query parameters
//-//////////////////////////

datatype QueryParametersImpl = QueryParametersImpl_ctor(program_encoding:seq<int>, row_min:int, row_max:int,
                                                        answer_units:int, answer_min:int, answer_max:int,
                                                        alpha_num:int, alpha_den:int, beta_num:int, beta_den:int)

static predicate QueryParametersImplValid (q:QueryParametersImpl)
{
    (forall i :: 0 <= i < |q.program_encoding| ==> Word32(q.program_encoding[i])) &&
    Word32(q.row_min) &&
    Word32(q.row_max) &&
    Word32(q.answer_units) &&
    Word32(q.answer_min) &&
    Word32(q.answer_max) &&
    Word32(q.alpha_num) &&
    Word32(q.alpha_den) &&
    Word32(q.beta_num) &&
    Word32(q.beta_den) &&
    q.alpha_den != 0 &&
    q.beta_den != 0
}

static function QueryParametersImplToSpec(q:QueryParametersImpl) : QueryParameters
    requires QueryParametersImplValid(q);
{
    QueryParameters_ctor(q.program_encoding, q.row_min, q.row_max, q.answer_units, q.answer_min, q.answer_max,
                         real(q.alpha_num) / real(q.alpha_den), real(q.beta_num) / real(q.beta_den))
}

//-//////////////////////////
//- Request implementation
//-//////////////////////////

datatype DiffPrivRequestImpl = InvalidRequestImpl_ctor()
                             | GetQuoteRequestImpl_ctor(nonce_external:seq<int>)
                             | InitializeDBRequestImpl_ctor(budget_num:int, budget_den:int)
                             | AddRowRequestImpl_ctor(request_ciphertext:seq<int>)
                             | QueryRequestImpl_ctor(q:QueryParametersImpl)

static predicate WellformedDiffPrivRequest(request:DiffPrivRequestImpl)
{
    match request
        case InvalidRequestImpl_ctor => true
        case GetQuoteRequestImpl_ctor(nonce_external) => IsByteSeqOfLen(nonce_external, 20)
        case InitializeDBRequestImpl_ctor(budget_num, budget_den) => Word32(budget_num) && Word32(budget_den) && budget_den != 0
        case AddRowRequestImpl_ctor(request_ciphertext) => IsByteSeq(request_ciphertext) && |request_ciphertext| > 0
        case QueryRequestImpl_ctor(q) => QueryParametersImplValid(q)
}

static function DiffPrivRequestImplToSpec(request:DiffPrivRequestImpl) : DiffPrivRequest
    requires WellformedDiffPrivRequest(request);
{
    match request
        case InvalidRequestImpl_ctor => InvalidRequest_ctor()
        case GetQuoteRequestImpl_ctor(nonce_external) => GetQuoteRequest_ctor(nonce_external)
        case InitializeDBRequestImpl_ctor(budget_num, budget_den) => InitializeDBRequest_ctor(real(budget_num) / real(budget_den))
        case AddRowRequestImpl_ctor(request_ciphertext) => AddRowRequest_ctor(request_ciphertext)
        case QueryRequestImpl_ctor(q:QueryParametersImpl) => QueryRequest_ctor(QueryParametersImplToSpec(q))
}

//-//////////////////////////
//- Request parsing
//-//////////////////////////

static lemma Lemma_InitializeDBWellformedDiffPrivRequest(request:DiffPrivRequestImpl)
    requires request.InitializeDBRequestImpl_ctor?;
    requires Word32(request.budget_num);
    requires Word32(request.budget_den);
    requires request.budget_den != 0;
    ensures WellformedDiffPrivRequest(request);
{
}

static lemma Lemma_QueryWellformedDiffPrivRequest(request:DiffPrivRequestImpl)
    requires request.QueryRequestImpl_ctor?;
    requires QueryParametersImplValid(request.q);
    ensures WellformedDiffPrivRequest(request);
{
}

method ParseRequestPacket (data:seq<int>) returns (request:DiffPrivRequestImpl)
    requires IsByteSeq(data);
    ensures WellformedDiffPrivRequest(request);
    ensures RequestParsedCorrectly(data, DiffPrivRequestImplToSpec(request));

    requires public(data);
    ensures public(request);
{
    if |data| == 0 {
        request := InvalidRequestImpl_ctor();
        return;
    }
    if data[0] == 1 {
        request := ParseGetQuoteRequestPacket(data);
        return;
    }
    if data[0] == 2 {
        request := ParseInitializeDBRequestPacket(data);
        return;
    }
    if data[0] == 3 {
        request := ParseAddRowRequestPacket(data);
        return;
    }
    if data[0] == 4 {
        request := ParseQueryRequestPacket(data);
        return;
    }
    request := InvalidRequestImpl_ctor();
}

static method ParseGetQuoteRequestPacket (data:seq<int>) returns (request:DiffPrivRequestImpl)
    requires IsByteSeq(data);
    requires |data| > 0;
    requires data[0] == 1;
    ensures WellformedDiffPrivRequest(request);
    ensures GetQuoteRequestParsedCorrectly(data, DiffPrivRequestImplToSpec(request));

    requires public(data);
    ensures public(request);
{
    if |data| < 21 {
        request := InvalidRequestImpl_ctor();
        return;
    }
    var nonce_external := data[1..21];
    return GetQuoteRequestImpl_ctor(nonce_external);
}

static method ParseInitializeDBRequestPacket (data:seq<int>) returns (request:DiffPrivRequestImpl)
    requires IsByteSeq(data);
    requires |data| > 0;
    requires data[0] == 2;
    ensures WellformedDiffPrivRequest(request);
    ensures InitializeDBRequestParsedCorrectly(data, DiffPrivRequestImplToSpec(request));

    requires public(data);
    ensures public(request);
{
    if |data| < 9 {
        request := InvalidRequestImpl_ctor();
        return;
    }
    var budget_num := BEFourBytesToWord_impl(data[1..5]);
    var budget_den := BEFourBytesToWord_impl(data[5..9]);
    if (budget_den == 0) {
        request := InvalidRequestImpl_ctor();
        return;
    }
    request := InitializeDBRequestImpl_ctor(budget_num, budget_den);
    Lemma_InitializeDBWellformedDiffPrivRequest(request);
}

method ParseAddRowRequestPacket (data:seq<int>) returns (request:DiffPrivRequestImpl)
    requires IsByteSeq(data);
    requires |data| > 0;
    requires data[0] == 3;
    ensures WellformedDiffPrivRequest(request);
    ensures AddRowRequestParsedCorrectly(data, DiffPrivRequestImplToSpec(request));

    requires public(data);
    ensures public(request);
{
    if |data| == 1 {
        request := InvalidRequestImpl_ctor();
        return;
    }
    return AddRowRequestImpl_ctor(data[1..]);
}

static method ParseQueryRequestFields (data:seq<int>, ghost fields:seq<seq<int>>, program_size:int) returns
    (row_min:int, row_max:int, answer_units:int, answer_min:int, answer_max:int, alpha_num:int, alpha_den:int, beta_num:int, beta_den:int,
     program_encoding_words:seq<int>)
    requires 0 <= program_size <= |data| - 41;
    requires program_size % 4 == 0;
    requires IsByteSeq(data);
    requires fields == data[5:4:4:4:4:4:4:4:4:4:program_size];
    ensures  IsByteSeq(fields[1]);
    ensures  IsByteSeq(fields[2]);
    ensures  IsByteSeq(fields[3]);
    ensures  IsByteSeq(fields[4]);
    ensures  IsByteSeq(fields[5]);
    ensures  IsByteSeq(fields[6]);
    ensures  IsByteSeq(fields[7]);
    ensures  IsByteSeq(fields[8]);
    ensures  IsByteSeq(fields[9]);
    ensures  row_min == BEByteSeqToInt(fields[1]);
    ensures  row_max == BEByteSeqToInt(fields[2]);
    ensures  answer_units == BEByteSeqToInt(fields[3]);
    ensures  answer_min == BEByteSeqToInt(fields[4]);
    ensures  answer_max == BEByteSeqToInt(fields[5]);
    ensures  alpha_num == BEByteSeqToInt(fields[6]);
    ensures  alpha_den == BEByteSeqToInt(fields[7]);
    ensures  beta_num == BEByteSeqToInt(fields[8]);
    ensures  beta_den == BEByteSeqToInt(fields[9]);
    ensures  program_encoding_words == BEIntToDigitSeq(power2(32), |fields[10]|/4, BEDigitSeqToInt(power2(8), fields[10]));
    ensures  Word32(row_min);
    ensures  Word32(row_max);
    ensures  Word32(answer_units);
    ensures  Word32(answer_min);
    ensures  Word32(answer_max);
    ensures  Word32(alpha_num);
    ensures  Word32(alpha_den);
    ensures  Word32(beta_num);
    ensures  Word32(beta_den);
    ensures  forall i :: 0 <= i < |program_encoding_words| ==> Word32(program_encoding_words[i]);
{
    row_min := BEFourBytesToWord_impl(data[5..9]);
    row_max := BEFourBytesToWord_impl(data[9..13]);
    answer_units := BEFourBytesToWord_impl(data[13..17]);
    answer_min := BEFourBytesToWord_impl(data[17..21]);
    answer_max := BEFourBytesToWord_impl(data[21..25]);
    alpha_num := BEFourBytesToWord_impl(data[25..29]);
    alpha_den := BEFourBytesToWord_impl(data[29..33]);
    beta_num := BEFourBytesToWord_impl(data[33..37]);
    beta_den := BEFourBytesToWord_impl(data[37..41]);

    var program_encoding := data[41..41+program_size];
    ghost var padbytes:seq<int>;
    program_encoding_words, padbytes := BEByteSeqToWordSeq_impl(program_encoding);
    assert program_encoding_words == BEByteSeqToWordSeq(program_encoding);
}

static method ParseQueryRequestPacket (data:seq<int>) returns (request:DiffPrivRequestImpl)
    requires IsByteSeq(data);
    requires |data| > 0;
    requires data[0] == 4;
    ensures WellformedDiffPrivRequest(request);
    ensures QueryRequestParsedCorrectly(data, DiffPrivRequestImplToSpec(request));

    requires public(data);
    ensures public(request);
{
    if |data| < 41 {
        request := InvalidRequestImpl_ctor();
        return;
    }
    var program_size := BEFourBytesToWord_impl(data[1..5]);
    if |data| < 41 + program_size || program_size % 4 != 0 {
        request := InvalidRequestImpl_ctor();
        return;
    }
    assert program_size >= 0 && |data| >= 41 + program_size && program_size % 4 == 0;

    ghost var fields := data[5:4:4:4:4:4:4:4:4:4:program_size];
    var row_min, row_max, answer_units, answer_min, answer_max, alpha_num, alpha_den, beta_num, beta_den, program_encoding_words :=
        ParseQueryRequestFields(data, fields, program_size);

    if alpha_den == 0 || beta_den == 0 {
        request := InvalidRequestImpl_ctor();
        return;
    }

    var q := QueryParametersImpl_ctor(program_encoding_words, row_min, row_max, answer_units, answer_min, answer_max, alpha_num, alpha_den,
                                      beta_num, beta_den);
    request := QueryRequestImpl_ctor(q);
    Lemma_QueryWellformedDiffPrivRequest(request);
}

//-//////////////////////////
//- Response forming
//-//////////////////////////

static predicate WellformedResponse (response:DiffPrivResponse)
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

        case InitializeDBResponse_ctor(error_code) => Word32(error_code)
        case AddRowResponse_ctor => true
        case QueryResponse_ctor(error_code, response_value) => Word32(error_code) && Word32(response_value)
}

static method FormResponsePacket (response:DiffPrivResponse) returns (data:seq<int>)
    requires WellformedResponse(response);
    ensures IsByteSeq(data);
    ensures ResponseFormedCorrectly(response, data);

    requires public(response);
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

        case InitializeDBResponse_ctor(error_code) =>
            var error_code_encoded := BEWordToFourBytes_impl(error_code);
            data := [2] + error_code_encoded;

        case AddRowResponse_ctor =>
            data := [3];

        case QueryResponse_ctor(error_code, response_value) =>
            var error_code_encoded := BEWordToFourBytes_impl(error_code);
            var response_value_encoded := BEWordToFourBytes_impl(response_value);
            data := [4] + error_code_encoded + response_value_encoded;
    }
}
