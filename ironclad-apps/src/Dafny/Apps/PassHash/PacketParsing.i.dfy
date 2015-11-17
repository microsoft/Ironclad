//-<NuBuild BasmEnableSymdiff true />
include "PacketParsing.c.dfy"
include "../../Libraries/Crypto/RSA/RSA.i.dfy"
include "../../Libraries/Util/Halter.i.dfy"

//-//////////////////////////
//- Request parsing
//-//////////////////////////

static predicate RequestValid (request:PassHashRequest)
{
    match request
        case InvalidRequest_ctor => true
        case PerformHashRequest_ctor(message, salt) => IsByteSeq(message) && IsByteSeq(salt)
}

static lemma Lemma_PerformHashRequestPacketParsedCorrectly (data:seq<int>, request:PassHashRequest)
    requires IsByteSeq(data);
    requires request.PerformHashRequest_ctor?;
    requires |data| >= 9 + |request.message| + |request.salt|;
    requires data[0] == 1;
    requires |request.message| == BEByteSeqToInt(data[1..5]);
    requires |request.salt| == BEByteSeqToInt(data[5..9]);
    requires request.message == data[9..9+|request.message|];
    requires request.salt == data[9+|request.message|..9+|request.message|+|request.salt|];
    ensures PerformHashRequestParsedCorrectly(data, request);
{
}

static method ParseRequestPacket (data:seq<int>) returns (request:PassHashRequest)
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
        request := ParsePerformHashRequestPacket(data);
        return;
    }
    request := InvalidRequest_ctor();
}

static method ParsePerformHashRequestPacket (data:seq<int>) returns (request:PassHashRequest)
    requires IsByteSeq(data);
    requires |data| > 0;
    requires data[0] == 1;
    requires public(data);

    ensures PerformHashRequestParsedCorrectly(data, request);
    ensures RequestValid(request);
    ensures public(request);
{
    if |data| < 9 {
        request := InvalidRequest_ctor();
        return;
    }
    var message_len := BEFourBytesToWord_impl(data[1..5]);
    assert message_len == BEByteSeqToInt(data[1..5]);
    var salt_len := BEFourBytesToWord_impl(data[5..9]);
    assert salt_len == BEByteSeqToInt(data[5..9]);

    if message_len < 0 || salt_len < 0 || |data| < 9 + message_len + salt_len {
        request := InvalidRequest_ctor();
        return;
    }

    var message := data[9..9+message_len];
    var salt := data[9+message_len..9+message_len+salt_len];
    request := PerformHashRequest_ctor(message, salt);
    Lemma_PerformHashRequestPacketParsedCorrectly(data, request);
}

//-//////////////////////////
//- Response forming
//-//////////////////////////

static predicate WellformedResponse (response:PassHashResponse)
{
    match response
        case NullResponse_ctor => true

        case PerformHashResponse_ctor(hash_error_code, passhash_hash) =>
            Word32(hash_error_code)
            && IsByteSeqOfLen(passhash_hash, 32)
}

static method FormResponsePacket (response:PassHashResponse) returns (data:seq<int>)
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

        case PerformHashResponse_ctor(hash_error_code, passhash_hash) =>
            var hash_error_code_encoded := BEWordToFourBytes_impl(hash_error_code);
            data := [1] + hash_error_code_encoded + passhash_hash;
            assert data[0] == 1;
            assert data[1..5] == hash_error_code_encoded == BEWordToFourBytes(hash_error_code);
            assert data[5..37] == passhash_hash;
    }
}
