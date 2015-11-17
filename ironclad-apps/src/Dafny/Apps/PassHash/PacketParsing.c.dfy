include "PassHash.s.dfy"

//-///////////////////////////
//- Request parsing
//-///////////////////////////

datatype PassHashRequest = InvalidRequest_ctor()
                         | PerformHashRequest_ctor(message:seq<int>, salt:seq<int>)

static predicate RequestParsedCorrectly(data:seq<int>, request:PassHashRequest)
    requires IsByteSeq(data);
{
    if |data| == 0 then
        request.InvalidRequest_ctor?
    else if data[0] == 1 then
        PerformHashRequestParsedCorrectly(data, request)
    else
        request.InvalidRequest_ctor?
}

static predicate PerformHashRequestParsedCorrectly(data:seq<int>, request:PassHashRequest)
    requires IsByteSeq(data);
    requires |data| > 0;
    requires data[0] == 1;
{
    if |data| < 9 then
        request.InvalidRequest_ctor?
    else
    (
        var message_len := BEByteSeqToInt(data[1..5]);
        var salt_len := BEByteSeqToInt(data[5..9]);
        if message_len < 0 || salt_len < 0 || |data| < 9 + message_len + salt_len then
            request.InvalidRequest_ctor?
        else
            request.PerformHashRequest_ctor?
            && request.message == data[9..9+message_len]
            && request.salt == data[9+message_len..9+message_len+salt_len]
    )
}

//-///////////////////////////
//- Response parsing
//-///////////////////////////

datatype PassHashResponse = NullResponse_ctor()
                          | PerformHashResponse_ctor(hash_error_code:int, passhash_hash:seq<int>);

static predicate ResponseFormedCorrectly(response:PassHashResponse, data:seq<int>)
{
    match response
        case NullResponse_ctor =>
            |data| >= 1 && data[0] == 0

        case PerformHashResponse_ctor(hash_error_code, passhash_hash) =>
            Word32(hash_error_code) &&
            IsByteSeqOfLen(passhash_hash, 32) &&
            |data| >= 37 &&
            data[0] == 1 &&
            data[1..5] == BEWordToFourBytes(hash_error_code) &&
            data[5..37] == passhash_hash
}
