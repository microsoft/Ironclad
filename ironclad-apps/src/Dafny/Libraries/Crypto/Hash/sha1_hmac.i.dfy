include "sha_common.s.dfy"
include "hmac_common.s.dfy"
include "sha1.i.dfy"
include "hmac_common.i.dfy"
include "../../Util/arrays_and_seqs.i.dfy"

method HMAC_SHA1_inner_hash(key: array<int>, data: array<int>, len: int) returns (hash: array<int>)
    requires Word32(len);
    requires IsWordArray(key);
    requires key.Length == 16;
    requires len <= power2(32) - 1 - 512;
    requires IsWordArray(data);
    requires 0 <= data.Length;
    requires 0 <= len <= data.Length * 32;
    ensures fresh(hash);
    ensures key[..] == old(key[..]);
    ensures data[..] == old(data[..]);
    ensures IsWordArray(hash);
    ensures Mod32_const(512) == 0;
    ensures IsSHA1(SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Ipad_premium(512)) + BEWordSeqToBitSeq_premium(data[..])[..len], hash[..]);
{
    var input := HMAC_inner_input(key, data, len);
    assert data[..] == old(data[..]);
    assert key[..] == old(key[..]);
    lemma_2toX();
    ghost var old_input := BEWordSeqToBitSeq_premium(input[..])[..len+512];

    calc {
        old_input;
        BEWordSeqToBitSeq_premium(input[..])[..len+512];
        (SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Ipad_premium(512)) + BEWordSeqToBitSeq_premium(data[..]) +
            BEWordSeqToBitSeq_premium(input[16+data.Length..]))[..len+512];
        { assert |SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Ipad_premium(512))| == 512; }
        { assert |BEWordSeqToBitSeq_premium(data[..])| >= len; } //- == |data[..]|*32;
        SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Ipad_premium(512)) + BEWordSeqToBitSeq_premium(data[..])[..len];
    }

    var hash_seq := SHA1_impl_ArrayInPlace(input, len+512);
    hash := SeqToArray(hash_seq);
    lemma_Mod32_const(512);
}

method HMAC_SHA1_impl_Array(key: array<int>, data: array<int>, len: int) returns (hash: seq<int>)
    requires Word32(len);
    requires IsWordArray(key);
    requires key.Length == 16;
    requires len <= power2(32) - 1 - 512;
    requires data != null;
    requires 0 <= len <= data.Length * 32;
    requires IsWordArray(data);
    ensures IsWordSeqOfLen(hash, 5);
    ensures key[..] == old(key[..]);
    ensures data[..] == old(data[..]);
    ensures var k := BEWordSeqToBitSeq_premium(key[..]);
            var m := BEWordSeqToBitSeq_premium(data[..])[..len];
            IsBitSeqOfLen(k, 512) &&
            IsBitSeqOfLen(Ipad(512), 512) &&
            IsBitSeq(SeqXor(k, Ipad(512)) + m) &&
            |SeqXor(k, Ipad(512)) + m| < power2(64) &&
            IsBitSeqOfLen(Opad(512), 512) &&
            IsBitSeq(SeqXor(k, Opad(512)) + BEWordSeqToBitSeq(SHA1(SeqXor(k, Ipad(512)) + m))) &&
            |SeqXor(k, Opad(512)) + BEWordSeqToBitSeq(SHA1(SeqXor(k, Ipad(512)) + m))| < power2(64) &&
            hash == HMAC_SHA1(k, m);
{
    var inner_hash := HMAC_SHA1_inner_hash(key, data, len);
    assert key[..]  == old( key[..]);
    assert data[..] == old(data[..]);
    lemma_2toX();
    reveal_Mod32_const();
    lemma_SHA1IsAFunction(SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Ipad_premium(512)) + BEWordSeqToBitSeq_premium(data[..])[..len],
                            inner_hash[..]);
    assert inner_hash[..] == SHA1(SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Ipad_premium(512)) + BEWordSeqToBitSeq_premium(data[..])[..len]);
    ghost var old_inner_hash := inner_hash[..];

    var input := HMAC_outer_input(key, inner_hash);
    assert old_inner_hash == inner_hash[..];
    assert key[..]  == old( key[..]);
    assert data[..] == old(data[..]);
    ghost var original_input := input[..];

    var bit_len := 32*(key.Length + inner_hash.Length);
    assert old_inner_hash == inner_hash[..];
    assert key[..]  == old( key[..]);
    assert data[..] == old(data[..]);
    assert input[..] == original_input;
    ghost var old_input := BEWordSeqToBitSeq_premium(input[..])[..bit_len];

    calc <= { 16+8; {lemma_PaddedLength_properties(32*(16+inner_hash.Length));} input.Length; }

    calc {
        old_input;
        BEWordSeqToBitSeq_premium(input[..])[..bit_len];
        (SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Opad_premium(512)) +
            BEWordSeqToBitSeq_premium(inner_hash[..]) + BEWordSeqToBitSeq_premium(input[16+8..]))[..bit_len];
        (SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Opad_premium(512)) +
            BEWordSeqToBitSeq_premium(inner_hash[..]))[..bit_len];
        SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Opad_premium(512)) + BEWordSeqToBitSeq_premium(inner_hash[..]);
        SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Opad_premium(512)) +
            BEWordSeqToBitSeq_premium(SHA1(SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Ipad_premium(512)) +
                BEWordSeqToBitSeq_premium(data[..])[..len]));
    }

    hash := SHA1_impl_ArrayInPlace(input, bit_len);
    assert hash == SHA1(old_input);
    assert old_inner_hash == inner_hash[..];
    assert key[..]  == old( key[..]);
    assert data[..] == old(data[..]);

    ghost var k := BEWordSeqToBitSeq_premium(key[..]);
    ghost var m := BEWordSeqToBitSeq_premium(data[..])[..len];
    calc {
        hash;
        SHA1(old_input);
        SHA1(SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Opad_premium(512)) + BEWordSeqToBitSeq_premium(SHA1(SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Ipad_premium(512)) + BEWordSeqToBitSeq_premium(data[..])[..len])));
        { assert BEWordSeqToBitSeq_premium(key[..])[..key.Length*32] == BEWordSeqToBitSeq_premium(key[..]); }
        SHA1(SeqXor_premium(k, Opad_premium(|k|)) + BEWordSeqToBitSeq_premium(SHA1(SeqXor_premium(k, Ipad_premium(|k|)) + m)));
        HMAC_SHA1(k, m);
    }
}

method HMAC_SHA1_impl_Seqs(keyBytes: seq<int>, dataBytes: seq<int>) returns (hash: seq<int>)
    requires Word32(|dataBytes|*8);
    requires IsByteSeq(keyBytes);
    requires |keyBytes| <= 64;
    requires |dataBytes|*8 <= power2(32) - 1 - 512;
    requires IsByteSeq(dataBytes);
    ensures IsWordSeqOfLen(hash, 5);
    ensures var k := BEByteSeqToBitSeq_premium(keyBytes + RepeatDigit_premium(0, 64 - |keyBytes|));
            var m := BEByteSeqToBitSeq_premium(dataBytes);
            IsBitSeqOfLen(k, 512) &&
            IsBitSeqOfLen(Ipad(512), 512) &&
            IsBitSeq(SeqXor(k, Ipad(512)) + m) &&
            |SeqXor(k, Ipad(512)) + m| < power2(64) &&
            IsBitSeqOfLen(Opad(512), 512) &&
            IsBitSeq(SeqXor(k, Opad(512)) + BEWordSeqToBitSeq(SHA1(SeqXor(k, Ipad(512)) + m))) &&
            |SeqXor(k, Opad(512)) + BEWordSeqToBitSeq(SHA1(SeqXor(k, Ipad(512)) + m))| < power2(64) &&
            hash == HMAC_SHA1(k, m);
{
    var requiredKeyBytePadding := RepeatDigit_impl(0, 64 - |keyBytes|);
    var keyBytesPadded := keyBytes + requiredKeyBytePadding;
    var keyWords, padbytes := BEByteSeqToWordSeq_impl(keyBytesPadded);
    var keyArray := SeqToArray(keyWords);
    var dataWords := BEByteSeqToWordSeqTailPadding(dataBytes);
    var dataArray := SeqToArray(dataWords);
    var len := |dataBytes|*8;
    calc {
        len;
        |dataBytes|*8;
        <= |BEWordSeqToBitSeq_premium(dataWords)|;
        |dataWords| * 32;
        dataArray.Length * 32;
    }
    calc {
        keyArray.Length;
        |keyWords|;
        |keyBytesPadded| / 4;
        (|keyBytes| + 64 - |keyBytes|) / 4;
        64 / 4;
        16;
    }
    hash := HMAC_SHA1_impl_Array(keyArray, dataArray, len);

    lemma_2toX();
    ghost var k := BEByteSeqToBitSeq_premium(keyBytesPadded);
    ghost var m := BEByteSeqToBitSeq_premium(dataBytes);
    reveal_Mod32_const();
    assert IsBitSeqOfLen(k, 512);
    assert IsBitSeqOfLen(Ipad_premium(512), 512);
    assert IsBitSeq(SeqXor_premium(k, Ipad_premium(512)) + m);
    assert |SeqXor_premium(k, Ipad_premium(512)) + m| < power2(64);
    assert IsBitSeqOfLen(Opad_premium(512), 512);
    assert IsBitSeq(SeqXor_premium(k, Opad_premium(512)) + BEWordSeqToBitSeq_premium(SHA1(SeqXor_premium(k, Ipad_premium(512)) + m)));
    assert |SeqXor_premium(k, Opad_premium(512)) + BEWordSeqToBitSeq_premium(SHA1(SeqXor_premium(k, Ipad_premium(512)) + m))| < power2(64);
    calc {
        hash;
        HMAC_SHA1(BEWordSeqToBitSeq_premium(keyArray[..]), BEWordSeqToBitSeq_premium(dataArray[..])[..len]);
        { assert keyWords == keyArray[..]; }
        HMAC_SHA1(BEWordSeqToBitSeq_premium(keyWords), BEWordSeqToBitSeq_premium(dataArray[..])[..len]);
        HMAC_SHA1(k, BEWordSeqToBitSeq_premium(dataArray[..])[..len]);
        HMAC_SHA1(k, BEByteSeqToBitSeq_premium(dataBytes));
        HMAC_SHA1(k, m);
    }
}
