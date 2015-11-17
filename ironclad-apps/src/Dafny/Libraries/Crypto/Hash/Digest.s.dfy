include "../../Util/integer_sequences.s.dfy"
include "../Hash/sha256.s.dfy"

static function {:autoReq} SHA256_Bytes(msg_bytes:seq<int>) : seq<int>
{
    BEWordSeqToByteSeq(SHA256(BEByteSeqToBitSeq(msg_bytes)))
}

//- http://www.ietf.org/rfc/rfc3447.txt
//- (Note that https://tools.ietf.org/html/rfc5754 is a different
//- thing, for SMIMECapability.)
static function method {:autoReq} SHA256_DigestInfo() : seq<int>
{
    [ 0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01,
        0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0x04, 0x20 ]
}

static function {:autoReq} SHA256Digest(msg:seq<int>) : seq<int>
{
    SHA256_DigestInfo() + SHA256_Bytes(msg)
}
