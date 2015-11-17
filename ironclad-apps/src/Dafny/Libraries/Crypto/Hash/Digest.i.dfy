include "Digest.s.dfy"
include "sha256.i.dfy"

static function method{:CompiledSpec} CompiledSpec_SHA256_DigestInfo() : seq<int>

static lemma lemma_SHA256_DigestInfo_properties()
    ensures IsByteSeq(SHA256_DigestInfo());
    ensures |SHA256_DigestInfo()|==19;
{
    lemma_2toX();
}

static function SHA256_DigestInfo_premium() : seq<int>
    ensures IsByteSeq(SHA256_DigestInfo());
    ensures |SHA256_DigestInfo()|==19;
{
    lemma_2toX();
    SHA256_DigestInfo()
}

static lemma lemma_SHA256_preserves_type(msg:seq<int>)
    requires IsBitSeq(msg);
    requires |msg| < power2(64);
    ensures IsWordSeq(SHA256(msg));
{
//-    lemma_BitSeqToBoolSeq_ensures(msg);
}

static predicate SHA256_BytesRequires(msg_bytes:seq<int>)
{
    IsByteSeq(msg_bytes)
    && IsBitSeq(BEByteSeqToBitSeq(msg_bytes))
    && |BEByteSeqToBitSeq(msg_bytes)| < power2(64)
    && IsWordSeq(SHA256(BEByteSeqToBitSeq(msg_bytes)))
}

static lemma lemma_SHA256_Bytes_preserves_IsByteSeq(msg:seq<int>)
    requires IsByteSeq(msg);
    requires |msg| < power2(61);
    requires SHA256_BytesRequires(msg);
    ensures IsByteSeq(SHA256_Bytes(msg));
{
    lemma_BEByteSeqToBitSeq_ensures(msg);
    assert IsBitSeq(BEByteSeqToBitSeq(msg));
    calc {
        |BEByteSeqToBitSeq(msg)|;
        |msg|*8;
        < power2(61)*8;
            { lemma_2to64(); lemma_power2_add8(56); }
        power2(64);
    }
    lemma_SHA256_preserves_type(BEByteSeqToBitSeq(msg));
    lemma_BEWordSeqToByteSeq_ensures(SHA256(BEByteSeqToBitSeq(msg)));
}

//-static lemma lemma_SHA256Digest_properties(msg:seq<int>)
//-    requires IsByteSeq(msg);
//-    requires |msg| < power2(60);
//-    ensures SHA256_BytesRequires(msg);
//-    ensures IsByteSeq(SHA256Digest(msg));
//-    ensures |SHA256Digest(msg)|==32;
//-{
//-    lemma_2toX();
//-    lemma_SHA256_DigestInfo_properties();
//-    lemma_concat_preserves_IsByteSeq(SHA256_DigestInfo(), msg);
//-    calc {
//-        |SHA256_DigestInfo() + msg|;
//-        |SHA256_DigestInfo()|+|msg|;
//-        < 19+power2(60);
//-        <=    { lemma_2to64(); lemma_power2_add8(56); }
//-        power2(61);
//-    }
//-    assert IsBitSeq(BEByteSeqToBitSeq_premium(SHA256_DigestInfo() + msg));
//-    lemma_SHA256_Bytes_preserves_IsByteSeq(SHA256_DigestInfo() + msg);
//-
//-    calc {
//-        |SHA256Digest(msg)|;
//-        |SHA256_Bytes(SHA256_DigestInfo() + msg)|;
//-        |BEWordSeqToByteSeq(SHA256(BEByteSeqToBitSeq(SHA256_DigestInfo() + msg)))|;
//-    }
//-    assert |SHA256(BEByteSeqToBitSeq(SHA256_DigestInfo() + msg))| == 8;
//-    lemma_BEWordSeqToByteSeq_ensures(SHA256(BEByteSeqToBitSeq(SHA256_DigestInfo() + msg)));
//-    assert |BEWordSeqToByteSeq(SHA256(BEByteSeqToBitSeq(SHA256_DigestInfo() + msg)))| == 4*8;
//-}

static lemma lemma_SHA256Digest_premium(msg:seq<int>)
    requires IsByteSeq(msg);
    requires |msg|<power2(61);
    ensures IsBitSeq(BEByteSeqToBitSeq(msg));
    ensures |BEByteSeqToBitSeq(msg)| < power2(64);
    ensures IsByteSeq(SHA256Digest(msg));
    ensures |SHA256Digest(msg)| == 51;
{
    lemma_BEByteSeqToBitSeq_ensures(msg);
    calc {
        |BEByteSeqToBitSeq(msg)|;
        |msg|*8;
            { lemma_mul_is_mul_boogie(|msg|, 8); }
        mul(|msg|,8);
            { lemma_2toX32(); }
        |msg|*power2(3);
        <   { lemma_mul_strict_inequality(|msg|, power2(61), power2(3)); }
        power2(61)*power2(3);
            { lemma_power2_adds(61,3); }
        power2(64);
    }
    lemma_SHA256_DigestInfo_properties();
    lemma_SHA256_Bytes_preserves_IsByteSeq(msg);
    lemma_BEWordSeqToByteSeq_ensures(SHA256(BEByteSeqToBitSeq(msg)));
}

static function SHA256Digest_premium(msg:seq<int>) : seq<int>
    requires IsByteSeq(msg);
    requires |msg|<power2(61);
    ensures IsByteSeq(SHA256Digest_premium(msg));
    ensures |SHA256Digest_premium(msg)| == 51;
{
    lemma_SHA256Digest_premium(msg);
    SHA256Digest(msg)
}

static method SHA256DigestImpl(msg:seq<int>) returns (digest:seq<int>)
    requires IsByteSeq(msg);
    requires |msg| < power2(29);
    ensures IsByteSeq(digest);
    ensures |msg| < power2(61);
    ensures digest == SHA256Digest_premium(msg);
    ensures |digest| == 51;
{
    lemma_2toX32();
    lemma_power2_increases(29, 61);
    lemma_power2_increases(32, 64);
    
    var msg_digest_words := SHA256_impl_Bytes(msg);
    var msg_digest_bytes := BEWordSeqToByteSeq_impl(msg_digest_words);
    digest := SHA256_DigestInfo() + msg_digest_bytes;
}

