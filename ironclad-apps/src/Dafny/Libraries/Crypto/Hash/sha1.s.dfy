include "sha_common.s.dfy"
include "hmac_common.s.dfy"

//-///////////////////////////////////////////////////
//- Constants
//-///////////////////////////////////////////////////

static function method{:opaque} K_SHA1(n: int) : int
    requires 0 <= n <= 79;
    ensures Word32(K_SHA1(n));
{
    /*call_lemma:*/lemma_power2_32();
    if 0 <= n <= 19 then
        0x5a827999
    else if 20 <= n <= 39 then
        0x6ed9eba1
    else if 40 <= n <= 59 then
        0x8f1bbcdc
    else
        0xca62c1d6
}

static function method{:opaque} InitialH_SHA1(index: int) : int
    requires 0 <= index <= 4;
    ensures Word32(InitialH_SHA1(index));
{
    /*call_lemma:*/lemma_power2_32();
    [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0][index]
}

//-//////////////////////////////////
//- SHA-1 trace
//-//////////////////////////////////

//- The fields of a SHA1Trace have the following meanings:
//-
//-     M[blk][i]       = word #i of message block #blk
//-     W[blk][t]       = W_t during processing of message block #blk
//-     H[blk][j]       = H_j before processing message block #blk
//-     atoe[blk][t].a  = a before step t of processing of message block #blk
//-     ...
//-     atoe[blk][t].e  = e before step t of processing message block #blk

datatype atoe_Type = atoe_c(a:int, b:int, c:int, d:int, e:int);
datatype SHA1Trace = SHA1Trace_c(M:seq<seq<int>>, H:seq<seq<int>>, W:seq<seq<int>>, atoe:seq<seq<atoe_Type>>);

static predicate IsAtoEWordSeqOfLen(vs:seq<atoe_Type>, len:int)
{
    |vs| == len &&
    forall i :: 0 <= i < len ==> Word32(vs[i].a) && Word32(vs[i].b) && Word32(vs[i].c) && Word32(vs[i].d) && Word32(vs[i].e)
}

static function ConvertAtoEToSeq(v:atoe_Type) : seq<int>
{
    [v.a, v.b, v.c, v.d, v.e]
}

static predicate IsCompleteSHA1Trace(z:SHA1Trace)
{
    (forall i :: 0 <= i < |z.M| ==> IsWordSeqOfLen(z.M[i], 16)) &&
    |z.H| == |z.M| + 1 &&
    |z.W| == |z.atoe| == |z.M| &&
    (forall blk :: 0 <= blk < |z.M| ==> IsWordSeqOfLen(z.W[blk], 80)) &&
    (forall blk :: 0 <= blk < |z.M| ==> IsAtoEWordSeqOfLen(z.atoe[blk], 81)) &&
    (forall blk :: 0 <= blk <= |z.M| ==> IsWordSeqOfLen(z.H[blk], 5))
}

static predicate SHA1TraceHasCorrectHs(z:SHA1Trace)
    requires IsCompleteSHA1Trace(z);
{
    (forall j :: 0 <= j < 5 ==> z.H[0][j] == InitialH_SHA1(j)) &&
    (forall blk {:trigger TBlk(blk)} :: TBlk(blk) ==> forall j :: 0 <= blk < |z.M| && 0 <= j < 5 ==> z.H[blk+1][j] == Add32(ConvertAtoEToSeq(z.atoe[blk][80])[j], z.H[blk][j]))
}

static predicate SHA1TraceHasCorrectWs(z:SHA1Trace)
    requires IsCompleteSHA1Trace(z);
{
    forall blk ::
        0 <= blk < |z.M| ==>
        forall t {:trigger TStep(t)} :: TStep(t) ==>
            (0 <= t <= 15 ==> z.W[blk][t] == z.M[blk][t]) &&
            (16 <= t <= 79 ==> z.W[blk][t] ==
                RotateLeft(BitwiseXor(BitwiseXor(BitwiseXor(z.W[blk][t-3], z.W[blk][t-8]), z.W[blk][t-14]), z.W[blk][t-16]), 1))
}

static predicate SHA1TraceHasCorrectatoes(z:SHA1Trace)
    requires IsCompleteSHA1Trace(z);
{
    forall blk :: 0 <= blk < |z.M| ==>
        ConvertAtoEToSeq(z.atoe[blk][0]) == z.H[blk] &&
        forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t <= 79 ==>
            (var T := Add32(Add32(Add32(Add32(RotateLeft(z.atoe[blk][t].a, 5),
                                                     ft(t, z.atoe[blk][t].b, z.atoe[blk][t].c, z.atoe[blk][t].d)),
                                             z.atoe[blk][t].e),
                                     K_SHA1(t)),
                             z.W[blk][t]);
            z.atoe[blk][t+1].e == z.atoe[blk][t].d &&
            z.atoe[blk][t+1].d == z.atoe[blk][t].c &&
            z.atoe[blk][t+1].c == RotateLeft(z.atoe[blk][t].b, 30) &&
            z.atoe[blk][t+1].b == z.atoe[blk][t].a &&
            z.atoe[blk][t+1].a == T)
}

static predicate {:autoReq} SHA1TraceIsCorrect(z:SHA1Trace)
{
    SHA1TraceHasCorrectHs(z) && SHA1TraceHasCorrectWs(z) && SHA1TraceHasCorrectatoes(z)
}

static predicate {:autoReq} IsSHA1(messageBits:seq<int>, hash:seq<int>)
    requires IsBitSeq(messageBits);
{
    exists z:SHA1Trace ::
        IsCompleteSHA1Trace(z) &&
        z.M == BlockMessageForSHA(PadMessageForSHA(messageBits)) &&
        SHA1TraceIsCorrect(z) &&
        hash == z.H[|z.M|]
}

static function {:axiom} SHA1(messageBits:seq<int>) : seq<int>
    requires IsBitSeq(messageBits);
    requires |messageBits| < power2(64);
    ensures IsWordSeqOfLen(SHA1(messageBits), 5);

static lemma {:axiom} lemma_SHA1IsAFunction(messageBits:seq<int>, hash:seq<int>)
    requires IsBitSeq(messageBits);
    requires |messageBits| < power2(64);
    requires IsWordSeqOfLen(hash, 5);
    requires IsSHA1(messageBits, hash);
    ensures SHA1(messageBits) == hash;

//-///////////////////////////////////////////////////////////////////////////////
//- HMAC specification based on:
//- http://csrc.nist.gov/publications/fips/fips198-1/FIPS-198-1_final.pdf
//-///////////////////////////////////////////////////////////////////////////////

static function {:autoReq} HMAC_SHA1(k: seq<int>, m: seq<int>) : seq<int>
    requires |k|==512;
{
    SHA1(SeqXor(k, Opad(|k|)) + BEWordSeqToBitSeq(SHA1(SeqXor(k, Ipad(|k|)) + m)))
}
