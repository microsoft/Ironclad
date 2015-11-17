include "sha1.s.dfy"
include "../../Util/seq_blocking.i.dfy"
include "../../Util/arrays_and_seqs.i.dfy"
include "../../Util/integer_sequences_premium.i.dfy"
include "sha_padding.i.dfy"
include "sha_common.i.dfy"

static function method{:CompiledSpec} CompiledSpec_K_SHA1(n: int) : int
static function method{:CompiledSpec} CompiledSpec_InitialH_SHA1(index: int) : int

//-///////////////////////////////////////////////////
//- Utility functions for AtoE
//-///////////////////////////////////////////////////

static predicate Word32AtoE(v:atoe_Type)
{
    Word32(v.a) && Word32(v.b) && Word32(v.c) && Word32(v.d) && Word32(v.e)
}

static predicate IsAtoEWordSeq(vs:seq<atoe_Type>)
{
    forall i :: 0 <= i < |vs| ==> Word32AtoE(vs[i])
}

static function ConvertAtoEToSeq_premium(v:atoe_Type) : seq<int>
    requires Word32AtoE(v);
    ensures IsWordSeqOfLen(ConvertAtoEToSeq_premium(v), 5);
    ensures ConvertAtoEToSeq_premium(v) == ConvertAtoEToSeq(v);
{
    ConvertAtoEToSeq(v)
}

static predicate{:opaque} TheAtoEsAreOK(z:SHA1Trace, blk: int, t: int)
    requires 0 <= t <= 79;
    requires 0 <= blk;
    requires |z.atoe| > blk;
    requires |z.atoe[blk]| > t+1;
    requires Word32AtoE(z.atoe[blk][t]);
    requires |z.W| > blk;
    requires IsWordSeqOfLen(z.W[blk], 80);
{
    var T := Add32(Add32(Add32(Add32(Asm_RotateLeft(z.atoe[blk][t].a, 5),
                                             ft(t, z.atoe[blk][t].b, z.atoe[blk][t].c, z.atoe[blk][t].d)),
                                     z.atoe[blk][t].e),
                             K_SHA1(t)),
                     z.W[blk][t]);
    z.atoe[blk][t+1].e == z.atoe[blk][t].d &&
    z.atoe[blk][t+1].d == z.atoe[blk][t].c &&
    z.atoe[blk][t+1].c == Asm_RotateLeft(z.atoe[blk][t].b, 30) &&
    z.atoe[blk][t+1].b == z.atoe[blk][t].a &&
    z.atoe[blk][t+1].a == T
}

static lemma Lemma_TheAtoEsAreOKIsStable(z1:SHA1Trace, z2:SHA1Trace, blk: int, t: int)
    requires 0 <= t <= 79;
    requires 0 <= blk;
    requires |z1.atoe| == |z2.atoe| > blk;
    requires |z1.atoe[blk]| > t+1;
    requires |z2.atoe[blk]| > t+1;
    requires Word32AtoE(z1.atoe[blk][t]);
    requires z1.atoe[blk][t+1] == z2.atoe[blk][t+1];
    requires z1.atoe[blk][t] == z2.atoe[blk][t];
    requires |z1.W| > blk;
    requires z1.W == z2.W;
    requires IsWordSeqOfLen(z1.W[blk], 80);
    requires TheAtoEsAreOK(z1, blk, t);
    ensures TheAtoEsAreOK(z2, blk, t);
{
    reveal_TheAtoEsAreOK();
}

//-///////////////////////////////////////////////////
//- Initialization of data structures
//-///////////////////////////////////////////////////

static method InitH_SHA1(H:array<int>)
    requires H != null && H.Length == 5;
    ensures forall i :: 0 <= i < H.Length ==> H[i] == InitialH_SHA1(i);
    modifies H;
{
    reveal_InitialH_SHA1();
    H[0] := 0x67452301;
    H[1] := 0xefcdab89;
    H[2] := 0x98badcfe;
    H[3] := 0x10325476;
    H[4] := 0xc3d2e1f0;
}

static method InitK_SHA1(Ks: array<int>)
    requires Ks != null && Ks.Length == 80;
    ensures forall i :: 0 <= i < Ks.Length ==> Ks[i] == K_SHA1(i);
    modifies Ks;
{
    reveal_InitialH_SHA1();
    reveal_K_SHA1();
    var i := 0;
    while i < 80
        invariant 0 <= i <= 80;
        invariant forall j :: 0 <= j < i ==> Ks[j] == K_SHA1(j);
    {
        if 0 <= i <= 19 {
            Ks[i] := 0x5a827999;
        }
        else if 20 <= i <= 39 {
            Ks[i] := 0x6ed9eba1;
        }
        else if 40 <= i <= 59 {
            Ks[i] := 0x8f1bbcdc;
        }
        else {
            Ks[i] := 0xca62c1d6;
        }
        i := i + 1;
    }
}

//-///////////////////////////////////////////////////
//- Partial SHA1 traces
//-///////////////////////////////////////////////////

static predicate PartialSHA1TraceHasCorrectHs(z:SHA1Trace)
{
    |z.H| > 0 &&
    |z.H| <= |z.atoe|+1 &&
    (forall blk :: 0 <= blk < |z.H| ==> IsWordSeqOfLen(z.H[blk], 5)) &&
    (forall j :: 0 <= j < 5 ==> z.H[0][j] == InitialH_SHA1(j)) &&
    (forall blk {:trigger TBlk(blk)} :: TBlk(blk) && 0 <= blk < |z.H|-1 ==>
        IsAtoEWordSeqOfLen(z.atoe[blk], 81) &&
        forall j :: 0 <= j < 5 ==> z.H[blk+1][j] == Add32(ConvertAtoEToSeq(z.atoe[blk][80])[j], z.H[blk][j]))
}

static predicate PartialSHA1TraceHasCorrectWs(z:SHA1Trace)
{
    |z.W| <= |z.M| &&
    forall blk :: 0 <= blk < |z.W| ==>
        IsWordSeqOfLen(z.W[blk], 80) &&
        IsWordSeqOfLen(z.M[blk], 16) &&
        forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < 80 ==>
            (0 <= t <= 15 ==> z.W[blk][t] == z.M[blk][t]) &&
            (16 <= t <= 79 ==> z.W[blk][t] ==
                Asm_RotateLeft(Asm_BitwiseXor(Asm_BitwiseXor(Asm_BitwiseXor(z.W[blk][t-3], z.W[blk][t-8]), z.W[blk][t-14]), z.W[blk][t-16]),
                               1))
}

static predicate PartialSHA1TraceHasCorrectatoesWf(z:SHA1Trace)
{
    |z.atoe| <= |z.H| &&
    |z.atoe| <= |z.W| &&
    (forall blk :: 0 <= blk < |z.atoe|-1 ==> IsAtoEWordSeqOfLen(z.atoe[blk], 81)) &&
    forall blk :: 0 <= blk < |z.atoe| ==>
        |z.atoe[blk]| <= 81 &&
        IsWordSeqOfLen(z.W[blk], 80) &&
        IsAtoEWordSeq(z.atoe[blk]) &&
        (|z.atoe[blk]| > 0 ==> IsWordSeqOfLen(z.H[blk], 5) && ConvertAtoEToSeq(z.atoe[blk][0]) == z.H[blk])
}

static predicate{:opaque} PartialSHA1TraceHasCorrectatoesOpaque(z:SHA1Trace)
{
    |z.atoe| <= |z.H| &&
    |z.atoe| <= |z.W| &&
    (forall blk :: 0 <= blk < |z.atoe|-1 ==> IsAtoEWordSeqOfLen(z.atoe[blk], 81)) &&
    forall blk :: 0 <= blk < |z.atoe| ==>
        |z.atoe[blk]| <= 81 &&
        IsWordSeqOfLen(z.W[blk], 80) &&
        IsAtoEWordSeq(z.atoe[blk]) &&
        (|z.atoe[blk]| > 0 ==> IsWordSeqOfLen(z.H[blk], 5) && ConvertAtoEToSeq(z.atoe[blk][0]) == z.H[blk]) &&
        forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < |z.atoe[blk]|-1 ==>
            var T := Add32(Add32(Add32(Add32(Asm_RotateLeft(z.atoe[blk][t].a, 5),
                                                     ft(t, z.atoe[blk][t].b, z.atoe[blk][t].c, z.atoe[blk][t].d)),
                                             z.atoe[blk][t].e),
                                     K_SHA1(t)),
                             z.W[blk][t]);
            z.atoe[blk][t+1].e == z.atoe[blk][t].d &&
            z.atoe[blk][t+1].d == z.atoe[blk][t].c &&
            z.atoe[blk][t+1].c == Asm_RotateLeft(z.atoe[blk][t].b, 30) &&
            z.atoe[blk][t+1].b == z.atoe[blk][t].a &&
            z.atoe[blk][t+1].a == T
}

static predicate PartialSHA1TraceHasCorrectatoes(z:SHA1Trace)
{
    PartialSHA1TraceHasCorrectatoesWf(z) && PartialSHA1TraceHasCorrectatoesOpaque(z)
}

static predicate PartialSHA1TraceIsCorrect(z:SHA1Trace)
{
    PartialSHA1TraceHasCorrectWs(z) && PartialSHA1TraceHasCorrectHs(z) && PartialSHA1TraceHasCorrectatoes(z)
}

static lemma PartialSHA1TraceIsCorrectImpliesTraceIsCorrect(z:SHA1Trace)
    requires IsCompleteSHA1Trace(z);
    requires PartialSHA1TraceIsCorrect(z);
    ensures SHA1TraceIsCorrect(z);
{
    reveal_PartialSHA1TraceHasCorrectatoesOpaque();
}

//-///////////////////////////////////////////////////
//- Intermediate SHA1 state
//-///////////////////////////////////////////////////

datatype SHA1_state = SHA1_state_c(M:seq<int>, H:seq<int>, W:seq<int>, Ks:seq<int>, atoe:atoe_Type, num_blocks:int);

static function SHA1_vars_to_state(M:array<int>, words:int, H:array<int>, W:array<int>, Ks:array<int>, atoe:atoe_Type, num_blocks:int)
                                  : SHA1_state
    requires M != null && H != null && W != null && Ks != null;
    requires 0 <= words <= M.Length;
    reads M, H, W, Ks;
{
    SHA1_state_c(M[..words], H[..], W[..], Ks[..], atoe, num_blocks)
}

static predicate AreSHA1TraceAndStateOK(z:SHA1Trace, s:SHA1_state)
{
    PartialSHA1TraceIsCorrect(z) &&
    IsWordSeq(s.M) &&
    z.M == BreakIntoBlocks(s.M, 16) &&
    (forall i :: 0 <= i < |z.M| ==> IsWordSeqOfLen(z.M[i], 16)) &&
    Mul16(|z.M|) == |s.M| &&
    |z.M| == s.num_blocks &&
    |s.Ks| == 80 &&
    (forall t :: 0 <= t <= 79 ==> s.Ks[t] == K_SHA1(t))
}

static predicate IsSHA1ReadyForBlock(z:SHA1Trace, s:SHA1_state, nextBlock:int)
    requires 0 <= nextBlock;
{
    AreSHA1TraceAndStateOK(z, s) &&
    |z.H| == nextBlock + 1 &&
    |z.W| == nextBlock &&
    |z.atoe| == nextBlock &&
    (forall blk :: 0 <= blk < nextBlock ==> IsAtoEWordSeqOfLen(z.atoe[blk], 81)) &&
    s.H == z.H[nextBlock]
}

static predicate IsSHA1DoneComputingWs(z:SHA1Trace, s:SHA1_state, currentBlock:int)
    requires 0 <= currentBlock;
{
    AreSHA1TraceAndStateOK(z, s) &&
    |z.H| == currentBlock + 1 &&
    |z.W| == currentBlock + 1 &&
    |z.atoe| == currentBlock &&
    (forall blk :: 0 <= blk < currentBlock ==> IsAtoEWordSeqOfLen(z.atoe[blk], 81)) &&
    s.H == z.H[currentBlock] &&
    s.W == z.W[currentBlock]
}

static predicate IsSHA1ReadyForStep(z:SHA1Trace, s:SHA1_state, currentBlock:int, nextStep:int)
    requires 0 <= currentBlock;
    requires 0 <= nextStep <= 80;
{
    AreSHA1TraceAndStateOK(z, s) &&
    |z.H| == currentBlock + 1 &&
    |z.W| == currentBlock + 1 &&
    |z.atoe| == currentBlock + 1 &&
    (forall blk :: 0 <= blk < currentBlock ==> IsAtoEWordSeqOfLen(z.atoe[blk], 81)) &&
    IsAtoEWordSeqOfLen(z.atoe[currentBlock], nextStep+1) &&
    s.H == z.H[currentBlock] &&
    s.W == z.W[currentBlock] &&
    s.atoe == z.atoe[currentBlock][nextStep]
}

/////////////////////////////////////////////////////

/////////////////////////////////////////////////////

static lemma {:timeLimitMultiplier 3} lemma_SHA1TransitionOKAfterSettingHsStep1(z1:SHA1Trace, s1:SHA1_state, z2:SHA1Trace, s2:SHA1_state,
                                                                                currentBlock:int)
    requires 0 <= currentBlock;
    requires IsSHA1ReadyForStep(z1, s1, currentBlock, 80);
    requires s2.M == s1.M;
    requires IsWordSeqOfLen(s2.H, 5);
    requires forall j :: 0 <= j < 5 ==> s2.H[j] == Add32(ConvertAtoEToSeq_premium(s1.atoe)[j], s1.H[j]);
    requires s2.Ks == s1.Ks;
    requires s2.num_blocks == s1.num_blocks;
    requires z2 == SHA1Trace_c(z1.M, z1.H + [s2.H], z1.W, z1.atoe);
    ensures forall blk :: 0 <= blk < |z2.H| ==> IsWordSeqOfLen(z2.H[blk], 5);
    ensures forall blk {:trigger TBlk(blk)} :: TBlk(blk) && 0 <= blk < currentBlock + 1 ==>
        IsAtoEWordSeqOfLen(z2.atoe[blk], 81) &&
        forall j :: 0 <= j < 5 ==> z2.H[blk+1][j] == Add32(ConvertAtoEToSeq_premium(z2.atoe[blk][80])[j], z2.H[blk][j]);
{
    assert |z2.H| == currentBlock + 2;

    forall blk | 0 <= blk < |z2.H|
        ensures IsWordSeqOfLen(z2.H[blk], 5);
    {
        if (blk == |z2.H|-1) {
            assert z2.H[blk] == s2.H;
        }
        else {
            assert z2.H[blk] == z1.H[blk];
        }
    }

    assert forall blk {:trigger TBlk(blk)} :: TBlk(blk) && 0 <= blk < currentBlock + 1 ==> IsWordSeqOfLen(z2.H[blk+1], 5);

    forall blk {:trigger TBlk(blk)} | TBlk(blk) && 0 <= blk < currentBlock + 1
        ensures IsAtoEWordSeqOfLen(z2.atoe[blk], 81);
        ensures forall j :: 0 <= j < 5 ==> z2.H[blk+1][j] == Add32(ConvertAtoEToSeq_premium(z2.atoe[blk][80])[j], z2.H[blk][j]);
    {
        assert z2.atoe[blk] == z1.atoe[blk];
        if blk == currentBlock {
            assert IsSHA1ReadyForStep(z1, s1, currentBlock, 80);
            assert IsAtoEWordSeqOfLen(z1.atoe[currentBlock], 80+1);
            assert IsAtoEWordSeqOfLen(z1.atoe[blk], 81);
            calc {
                true
                ==> forall j :: 0 <= j < 5 ==> s2.H[j] == Add32(ConvertAtoEToSeq_premium(s1.atoe)[j], s1.H[j]);
                ==> { assert z2.H[blk+1] == s2.H; }
                    forall j :: 0 <= j < 5 ==> z2.H[blk+1][j] == Add32(ConvertAtoEToSeq_premium(s1.atoe)[j], s1.H[j]);
                ==> { assert z2.atoe[blk][80] == s1.atoe; }
                    forall j :: 0 <= j < 5 ==> z2.H[blk+1][j] == Add32(ConvertAtoEToSeq_premium(z2.atoe[blk][80])[j], s1.H[j]);
                ==> { assert z2.H[blk] == s1.H; }
                    forall j :: 0 <= j < 5 ==> z2.H[blk+1][j] == Add32(ConvertAtoEToSeq_premium(z2.atoe[blk][80])[j], z2.H[blk][j]);
            }
        }
    }
}

static lemma {:timeLimitMultiplier 3} lemma_SHA1TransitionOKAfterSettingHs(z1:SHA1Trace, s1:SHA1_state, z2:SHA1Trace, s2:SHA1_state,
                                                  currentBlock:int)
    requires 0 <= currentBlock;
    requires IsSHA1ReadyForStep(z1, s1, currentBlock, 80);
    requires s2.M == s1.M;
    requires IsWordSeqOfLen(s2.H, 5);
    requires forall j :: 0 <= j < 5 ==> s2.H[j] == Add32(ConvertAtoEToSeq_premium(s1.atoe)[j], s1.H[j]);
    requires s2.Ks == s1.Ks;
    requires s2.num_blocks == s1.num_blocks;
    requires z2 == SHA1Trace_c(z1.M, z1.H + [s2.H], z1.W, z1.atoe);
    ensures IsSHA1ReadyForBlock(z2, s2, currentBlock+1);
{
    lemma_SHA1TransitionOKAfterSettingHsStep1(z1, s1, z2, s2, currentBlock);
    reveal_PartialSHA1TraceHasCorrectatoesOpaque();
}

static lemma lemma_EarlierWsAreWords(W:seq<int>)
    requires IsWordSeqOfLen(W, 80);
    ensures forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < |W| ==>
        (16 <= t <= 79 ==> Word32(W[t-3]) && Word32(W[t-8]) && Word32(W[t-14]) && Word32(W[t-16]));
{
}

static lemma lemma_SHA1TransitionOKAfterSettingWs(z1:SHA1Trace, s1:SHA1_state, z2:SHA1Trace, s2:SHA1_state, currentBlock:int)
    requires 0 <= currentBlock < |z1.M|;
    requires IsSHA1ReadyForBlock(z1, s1, currentBlock);
    requires IsWordSeqOfLen(s2.W, 80);
    requires forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t <= 15 ==> s2.W[t] == z1.M[currentBlock][t];
    requires forall t {:trigger TStep(t)} :: TStep(t) && 16 <= t <= 79 ==> s2.W[t] == Asm_RotateLeft(Asm_BitwiseXor(Asm_BitwiseXor(Asm_BitwiseXor(s2.W[t-3], s2.W[t-8]),
                                                                                                   s2.W[t-14]),
                                                                                    s2.W[t-16]),
                                                                     1);
    requires z2 == SHA1Trace_c(z1.M, z1.H, z1.W + [s2.W], z1.atoe);
    requires s2.M == s1.M;
    requires s2.H == s1.H;
    requires s2.Ks == s1.Ks;
    requires s2.num_blocks == s1.num_blocks;
    ensures IsSHA1DoneComputingWs(z2, s2, currentBlock);
{
    assert z2.M == z1.M;
    assert z2.H == z1.H;
    assert |z2.W| == |z1.W| + 1;
    assert forall blk :: 0 <= blk < |z1.W| ==> z2.W[blk] == z1.W[blk];
    assert z2.W[|z1.W|] == s2.W;
    assert z2.atoe == z1.atoe;

    forall blk | 0 <= blk < |z2.W|
        ensures IsWordSeqOfLen(z2.W[blk], 80);
        ensures forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < |z2.W[blk]| ==>
                (16 <= t <= 79 ==> Word32(z2.W[blk][t-3]) && Word32(z2.W[blk][t-8]) && Word32(z2.W[blk][t-14]) && Word32(z2.W[blk][t-16]));
        ensures forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < |z2.W[blk]| ==>
                (0 <= t <= 15 ==> z2.W[blk][t] == z2.M[blk][t]) &&
                (16 <= t <= 79 ==> z2.W[blk][t] == Asm_RotateLeft(Asm_BitwiseXor(Asm_BitwiseXor(Asm_BitwiseXor(z2.W[blk][t-3],
                                                                                                               z2.W[blk][t-8]),
                                                                                                z2.W[blk][t-14]),
                                                                                 z2.W[blk][t-16]),
                                                                  1));
    {
        if blk < |z2.W|-1 {
            assert IsWordSeqOfLen(z2.W[blk], 80);
            lemma_EarlierWsAreWords(z2.W[blk]);
            assert forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < |z2.W[blk]| ==>
                (0 <= t <= 15 ==> z2.W[blk][t] == z2.M[blk][t]) &&
                (16 <= t <= 79 ==> z2.W[blk][t] == Asm_RotateLeft(Asm_BitwiseXor(Asm_BitwiseXor(Asm_BitwiseXor(z2.W[blk][t-3],
                                                                                                               z2.W[blk][t-8]),
                                                                                                z2.W[blk][t-14]),
                                                                                 z2.W[blk][t-16]),
                                                                  1));
        }
        else {
            assert blk == |z2.W|-1;
            assert z2.W[blk] == s2.W;
            lemma_EarlierWsAreWords(z2.W[blk]);
            assert forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < |z2.W[blk]| ==>
                (0 <= t <= 15 ==> z2.W[blk][t] == z2.M[blk][t]) &&
                (16 <= t <= 79 ==> z2.W[blk][t] == Asm_RotateLeft(Asm_BitwiseXor(Asm_BitwiseXor(Asm_BitwiseXor(z2.W[blk][t-3],
                                                                                                               z2.W[blk][t-8]),
                                                                                                z2.W[blk][t-14]),
                                                                                 z2.W[blk][t-16]),
                                                                  1));
        }
    }
    reveal_PartialSHA1TraceHasCorrectatoesOpaque();
}

static lemma lemma_SHA1TransitionOKAfterSettingAtoEStep1Helper1(z:SHA1Trace, blk:int, t:int)
    requires 0 <= t <= 79;
    requires 0 <= blk;
    requires |z.atoe| > blk;
    requires |z.atoe[blk]| > t+1;
    requires Word32AtoE(z.atoe[blk][t]);
    requires |z.W| > blk;
    requires IsWordSeqOfLen(z.W[blk], 80);
    requires PartialSHA1TraceHasCorrectatoes(z);
    ensures TheAtoEsAreOK(z, blk, t);
{
    assert TBlk(blk) && TStep(t);
    reveal_TheAtoEsAreOK();
    reveal_PartialSHA1TraceHasCorrectatoesOpaque();
}

static lemma lemma_SHA1TransitionOKAfterSettingAtoEStep1(z1:SHA1Trace, s1:SHA1_state, z2:SHA1Trace, s2:SHA1_state,
                                                         currentBlock:int, currentStep:int)
    requires TBlk(currentBlock) && TBlk(currentBlock + 1) && TStep(currentStep) && TStep(currentStep + 1);
    requires 0 <= currentBlock < |z1.M|;
    requires 0 <= currentStep <= 79;
    requires IsSHA1ReadyForStep(z1, s1, currentBlock, currentStep);
    requires var T := Add32(Add32(Add32(Add32(Asm_RotateLeft(s1.atoe.a, 5),
                                                      ft(currentStep, s1.atoe.b, s1.atoe.c, s1.atoe.d)),
                                              s1.atoe.e),
                                      s1.Ks[currentStep]),
                              s1.W[currentStep]);
             s2.atoe.e == s1.atoe.d &&
             s2.atoe.d == s1.atoe.c &&
             s2.atoe.c == Asm_RotateLeft(s1.atoe.b, 30) &&
             s2.atoe.b == s1.atoe.a &&
             s2.atoe.a == T;
    requires s2.M == s1.M;
    requires s2.H == s1.H;
    requires s2.W == s1.W;
    requires s2.Ks == s1.Ks;
    requires s2.num_blocks == s1.num_blocks;
    requires z2.M == z1.M && z2.H == z1.H && z2.W == z1.W;
    requires z2.atoe == z1.atoe[..currentBlock] + [z1.atoe[currentBlock] + [s2.atoe]];
    requires |z2.atoe| == |z1.atoe|;
    requires forall blk :: 0 <= blk < currentBlock ==> z2.atoe[blk] == z1.atoe[blk];
    requires forall t :: 0 <= t < |z1.atoe[currentBlock]| ==> z2.atoe[currentBlock][t] == z1.atoe[currentBlock][t];
    requires z2.atoe[currentBlock][|z1.atoe[currentBlock]|] == s2.atoe;
    ensures forall blk :: 0 <= blk < |z2.atoe| ==>
        |z2.atoe[blk]| <= |z2.W[blk]| + 1 &&
        |z2.atoe[blk]| <= 81 &&
        IsWordSeq(z2.W[blk]) &&
        IsAtoEWordSeq(z2.atoe[blk]) &&
        (|z2.atoe[blk]| > 0 ==> IsWordSeqOfLen(z2.H[blk], 5) && ConvertAtoEToSeq(z2.atoe[blk][0]) == z2.H[blk]) &&
        (forall t :: 0 <= t < |z2.atoe[blk]|-1 ==> TheAtoEsAreOK(z2, blk, t));
{
    forall blk {:trigger TBlk(blk)} | TBlk(blk) && 0 <= blk < |z2.atoe|
        ensures |z2.atoe[blk]| <= |z2.W[blk]| + 1;
        ensures |z2.atoe[blk]| <= 81;
        ensures IsWordSeq(z2.W[blk]);
        ensures IsAtoEWordSeq(z2.atoe[blk]);
        ensures (|z2.atoe[blk]| > 0 ==> IsWordSeqOfLen(z2.H[blk], 5) && ConvertAtoEToSeq(z2.atoe[blk][0]) == z2.H[blk]);
        ensures forall t :: 0 <= t < |z2.atoe[blk]|-1 ==> TheAtoEsAreOK(z2, blk, t);
    {
        assert |z2.atoe[blk]| <= |z2.W[blk]| + 1;
        assert |z2.atoe[blk]| <= 81;
        assert IsWordSeq(z2.W[blk]);
        assert IsAtoEWordSeq(z2.atoe[blk]);

        if blk < |z2.atoe|-1 {
            assert blk < currentBlock;
            assert z2.atoe[blk] == z1.atoe[blk];
            assert (|z2.atoe[blk]| > 0 ==> IsWordSeqOfLen(z2.H[blk], 5) && ConvertAtoEToSeq(z2.atoe[blk][0]) == z2.H[blk]);
            forall t | 0 <= t < |z1.atoe[blk]|-1
                ensures TheAtoEsAreOK(z2, blk, t);
            {
                lemma_SHA1TransitionOKAfterSettingAtoEStep1Helper1(z1, blk, t);
                Lemma_TheAtoEsAreOKIsStable(z1, z2, blk, t);
            }
            assert forall t :: 0 <= t < |z2.atoe[blk]|-1 ==> TheAtoEsAreOK(z2, blk, t);
        }
        else {
            assert blk == currentBlock;
            assert (|z2.atoe[blk]| > 0 ==> IsWordSeqOfLen(z2.H[blk], 5) && ConvertAtoEToSeq(z2.atoe[blk][0]) == z2.H[blk]);
            forall t | 0 <= t < |z2.atoe[blk]|-1
                ensures TheAtoEsAreOK(z2, blk, t);
            {
                if t < |z2.atoe[blk]|-2 {
                    assert t < currentStep;
                    lemma_SHA1TransitionOKAfterSettingAtoEStep1Helper1(z1, blk, t);
                    Lemma_TheAtoEsAreOKIsStable(z1, z2, blk, t);
                }
                else {
                    assert t == currentStep;
                    calc { true; { reveal_TheAtoEsAreOK(); } TheAtoEsAreOK(z2, blk, t); }
                }
            }
        }
    }
}

static lemma lemma_SHA1TransitionOKAfterSettingAtoE(z1:SHA1Trace, s1:SHA1_state, z2:SHA1Trace, s2:SHA1_state,
                                                    currentBlock:int, currentStep:int)
    requires TBlk(currentBlock) && TBlk(currentBlock + 1) && TStep(currentStep) && TStep(currentStep + 1);
    requires 0 <= currentBlock < |z1.M|;
    requires 0 <= currentStep <= 79;
    requires IsSHA1ReadyForStep(z1, s1, currentBlock, currentStep);
    requires var T := Add32(Add32(Add32(Add32(Asm_RotateLeft(s1.atoe.a, 5),
                                                      ft(currentStep, s1.atoe.b, s1.atoe.c, s1.atoe.d)),
                                              s1.atoe.e),
                                      s1.Ks[currentStep]),
                              s1.W[currentStep]);
             s2.atoe.e == s1.atoe.d &&
             s2.atoe.d == s1.atoe.c &&
             s2.atoe.c == Asm_RotateLeft(s1.atoe.b, 30) &&
             s2.atoe.b == s1.atoe.a &&
             s2.atoe.a == T;
    requires s2.M == s1.M;
    requires s2.H == s1.H;
    requires s2.W == s1.W;
    requires s2.Ks == s1.Ks;
    requires s2.num_blocks == s1.num_blocks;
    requires z2 == SHA1Trace_c(z1.M, z1.H, z1.W, z1.atoe[..currentBlock] + [z1.atoe[currentBlock] + [s2.atoe]]);
    ensures IsSHA1ReadyForStep(z2, s2, currentBlock, currentStep+1);
{
    lemma_SHA1TransitionOKAfterSettingAtoEStep1(z1, s1, z2, s2, currentBlock, currentStep);

    assert forall blk :: 0 <= blk < |z2.atoe| ==>
        |z2.atoe[blk]| <= |z2.W[blk]| + 1 &&
        |z2.atoe[blk]| <= 81 &&
        IsWordSeq(z2.W[blk]) &&
        IsAtoEWordSeq(z2.atoe[blk]) &&
        (|z2.atoe[blk]| > 0 ==> IsWordSeqOfLen(z2.H[blk], 5) && ConvertAtoEToSeq(z2.atoe[blk][0]) == z2.H[blk]) &&
        (forall t :: 0 <= t < |z2.atoe[blk]|-1 ==> TheAtoEsAreOK(z2, blk, t));

    forall blk | 0 <= blk < |z2.atoe|
        ensures IsAtoEWordSeq(z2.atoe[blk]);
        ensures forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < |z2.atoe[blk]|-1 ==>
            Word32AtoE(z2.atoe[blk][t]) &&
            var T := Add32(Add32(Add32(Add32(Asm_RotateLeft(z2.atoe[blk][t].a, 5),
                                                     ft(t, z2.atoe[blk][t].b, z2.atoe[blk][t].c, z2.atoe[blk][t].d)),
                                             z2.atoe[blk][t].e),
                                     K_SHA1(t)),
                             z2.W[blk][t]);
            z2.atoe[blk][t+1].e == z2.atoe[blk][t].d &&
            z2.atoe[blk][t+1].d == z2.atoe[blk][t].c &&
            z2.atoe[blk][t+1].c == Asm_RotateLeft(z2.atoe[blk][t].b, 30) &&
            z2.atoe[blk][t+1].b == z2.atoe[blk][t].a &&
            z2.atoe[blk][t+1].a == T;
    {
        forall t {:trigger TStep(t)} | TStep(t) && 0 <= t < |z2.atoe[blk]|-1
            ensures Word32AtoE(z2.atoe[blk][t]);
            ensures var T := Add32(Add32(Add32(Add32(Asm_RotateLeft(z2.atoe[blk][t].a, 5),
                                                             ft(t, z2.atoe[blk][t].b, z2.atoe[blk][t].c, z2.atoe[blk][t].d)),
                                                     z2.atoe[blk][t].e),
                                             K_SHA1(t)),
                                     z2.W[blk][t]);
            z2.atoe[blk][t+1].e == z2.atoe[blk][t].d &&
            z2.atoe[blk][t+1].d == z2.atoe[blk][t].c &&
            z2.atoe[blk][t+1].c == Asm_RotateLeft(z2.atoe[blk][t].b, 30) &&
            z2.atoe[blk][t+1].b == z2.atoe[blk][t].a &&
            z2.atoe[blk][t+1].a == T;
        {
            reveal_TheAtoEsAreOK();
            assert TheAtoEsAreOK(z2, blk, t);
        }
    }
    reveal_PartialSHA1TraceHasCorrectatoesOpaque();
}

/////////////////////////////////////////////////////

/////////////////////////////////////////////////////

static method InitializeVars_SHA1(M:array<int>, words:int, H:array<int>, W:array<int>, Ks:array<int>)
                                  returns (atoe:atoe_Type, num_blocks:int, ghost z:SHA1Trace)
    requires H != null && H.Length == 5;
    requires W != null;
    requires Ks != null && Ks.Length == 80;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires Mod16(words) == 0;
    requires forall i :: 0 <= i < words ==> Word32(M[i]);
    ensures IsSHA1ReadyForBlock(z, SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks), 0);
    ensures |z.M| == num_blocks;
    requires H != Ks && H != M && H != W && Ks != M && Ks != W;
    modifies H;
    modifies Ks;
    ensures M[..] == old(M[..]);
    ensures W[..] == old(W[..]);
{
    reveal_Mul16();
    reveal_Mod16();
    reveal_PartialSHA1TraceHasCorrectatoesOpaque();
    InitH_SHA1(H);
    InitK_SHA1(Ks);
    Lemma_AllBlocksAreOfEqualSize(M[..words], 16);
    Lemma_AllBlocksAreWordSeqs(M[..words], 16);
    z := SHA1Trace_c(BreakIntoBlocks(M[..words], 16), [H[..]], [], []);
    num_blocks := words / 16;
    atoe := atoe_c(0, 0, 0, 0, 0);
}

static method ComputeWsForBlockStep1_SHA1(M:array<int>, words:int, H:array<int>, W:array<int>, Ks:array<int>,
                                          atoe:atoe_Type, num_blocks:int, ghost z:SHA1Trace, currentBlock:int)
    requires H != null;
    requires W != null && W.Length == 80;
    requires Ks != null;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires IsSHA1ReadyForBlock(z, SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks), currentBlock);
    requires W != H && W != Ks && W != M;
    modifies W;
    ensures Ks[..] == old(Ks[..]);
    ensures H[..] == old(H[..]);
    ensures M[..] == old(M[..]);
    ensures forall t :: 0 <= t < 16 ==> Word32(W[t]);
    ensures forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < 16 ==> W[t] == z.M[currentBlock][t];
    ensures IsSHA1ReadyForBlock(z, SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks), currentBlock);
{
    ghost var s := SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks);

    var t:int := 0;
    while t < 16
        invariant 0 <= t <= 16;
        invariant s.M == M[..words];
        invariant forall step :: 0 <= step < t ==> Word32(W[step]);
        invariant forall step {:trigger TStep(step)} :: TStep(step) && 0 <= step < t ==> W[step] == z.M[currentBlock][step];
    {
        reveal_Mul16();
        calc {
            0;
            <= { lemma_mul_nonnegative(currentBlock, 16); }
               currentBlock * 16;
            <= currentBlock * 16 + t;
        }
        calc {
            currentBlock * 16 + t;
            16 * currentBlock + t;
            16 * (currentBlock+1) - 16 + t;
            <= 16*|z.M| - 16 + t;
            < 16*|z.M|;
            == Mul16(|z.M|);
            == words;
        }
        W[t] := M[currentBlock * 16 + t];
        calc {
            W[t];
            { lemma_mul_is_mul_boogie(currentBlock, 16);
              Lemma_BlockedSequencePrefixContainsElement(M[..], words, 16, currentBlock, t); }
            BreakIntoBlocks(M[..words], 16)[currentBlock][t];
            BreakIntoBlocks(s.M, 16)[currentBlock][t];
            z.M[currentBlock][t];
        }
        t := t + 1;
    }
}

static method ComputeWsForBlockStep2_SHA1(M:array<int>, words:int, H:array<int>, W:array<int>, Ks:array<int>,
                                          atoe:atoe_Type, num_blocks:int, ghost z:SHA1Trace, currentBlock:int)
    requires H != null;
    requires W != null && W.Length == 80;
    requires Ks != null;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires IsSHA1ReadyForBlock(z, SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks), currentBlock);
    requires forall t :: 0 <= t < 16 ==> Word32(W[t]);
    requires forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < 16 ==> W[t] == z.M[currentBlock][t];
    requires W != H && W != Ks && W != M;
    modifies W;
    ensures Ks[..] == old(Ks[..]);
    ensures H[..] == old(H[..]);
    ensures M[..] == old(M[..]);
    ensures forall t :: 0 <= t <= 79 ==> Word32(W[t]);
    ensures forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < 16 ==> W[t] == z.M[currentBlock][t];
    ensures forall t {:trigger TStep(t)} :: TStep(t) && 16 <= t <= 79 ==> W[t] == Asm_RotateLeft(Asm_BitwiseXor(Asm_BitwiseXor(Asm_BitwiseXor(W[t-3], W[t-8]), W[t-14]),
                                                                                W[t-16]),
                                                                 1);
{
    var t := 16;
    while t < 80
        invariant 16 <= t <= 80;
        invariant forall step :: 0 <= step < t ==> Word32(W[step]);
        invariant forall step {:trigger TStep(step)} :: TStep(step) && 0 <= step < 16 ==> W[step] == z.M[currentBlock][step];
        invariant forall step {:trigger TStep(step)} :: TStep(step) && 16 <= step < t ==>
            W[step] == Asm_RotateLeft(Asm_BitwiseXor(Asm_BitwiseXor(Asm_BitwiseXor(W[step-3], W[step-8]), W[step-14]), W[step-16]), 1);
    {
        W[t] := Asm_RotateLeft(Asm_BitwiseXor(Asm_BitwiseXor(Asm_BitwiseXor(W[t-3], W[t-8]), W[t-14]), W[t-16]), 1);
        t := t + 1;
    }
}

static method ComputeWsForBlock_SHA1(M:array<int>, words:int, H:array<int>, W:array<int>, Ks:array<int>, atoe:atoe_Type,
                                     num_blocks:int, ghost z:SHA1Trace, currentBlock:int)
                                     returns (ghost next_z:SHA1Trace)
    requires H != null;
    requires W != null && W.Length == 80;
    requires Ks != null;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires IsSHA1ReadyForBlock(z, SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks), currentBlock);
    requires W != H && W != Ks && W != M;
    modifies W;
    ensures Ks[..] == old(Ks[..]);
    ensures H[..] == old(H[..]);
    ensures M[..] == old(M[..]);
    ensures IsSHA1DoneComputingWs(next_z, SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks), currentBlock);
{
    ghost var s := SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks);

    ComputeWsForBlockStep1_SHA1(M, words, H, W, Ks, atoe, num_blocks, z, currentBlock);
    ComputeWsForBlockStep2_SHA1(M, words, H, W, Ks, atoe, num_blocks, z, currentBlock);

    next_z := SHA1Trace_c(z.M, z.H, z.W + [W[..]], z.atoe);
    ghost var next_s := SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks);

    lemma_SHA1TransitionOKAfterSettingWs(z, s, next_z, next_s, currentBlock);
}

static method ComputeInitialAtoEForBlock_SHA1(M:array<int>, words:int, H:array<int>, W:array<int>, Ks:array<int>,
                                              atoe:atoe_Type, num_blocks:int,
                                              ghost z:SHA1Trace, currentBlock:int)
                                              returns (next_atoe:atoe_Type, ghost next_z:SHA1Trace)
    requires H != null;
    requires W != null;
    requires Ks != null;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires IsSHA1DoneComputingWs(z, SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks), currentBlock);
    ensures IsSHA1ReadyForStep(next_z, SHA1_vars_to_state(M, words, H, W, Ks, next_atoe, num_blocks), currentBlock, 0);
{
    reveal_PartialSHA1TraceHasCorrectatoesOpaque();
    next_atoe := atoe_c(H[0], H[1], H[2], H[3], H[4]);
    next_z := SHA1Trace_c(z.M, z.H, z.W, z.atoe + [[next_atoe]]);
}

static method ComputeOneStep_SHA1(M:array<int>, words:int, H:array<int>, W:array<int>, Ks:array<int>, atoe:atoe_Type, num_blocks:int,
                                  ghost z:SHA1Trace, currentBlock:int, currentStep:int)
                                  returns (next_atoe:atoe_Type, ghost next_z:SHA1Trace)
    requires H != null;
    requires W != null;
    requires Ks != null;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires 0 <= currentStep <= 79;
    requires IsSHA1ReadyForStep(z, SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks), currentBlock, currentStep);
    ensures IsSHA1ReadyForStep(next_z, SHA1_vars_to_state(M, words, H, W, Ks, next_atoe, num_blocks), currentBlock, currentStep+1);

    ensures Ks[..] == old(Ks[..]);
    ensures H[..] == old(H[..]);
    ensures M[..] == old(M[..]);
    ensures W[..] == old(W[..]);
{
    assert TBlk(currentBlock) && TBlk(currentBlock + 1) && TStep(currentStep) && TStep(currentStep + 1);
    ghost var s := SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks);

    var T := Asm_Add(Asm_Add(Asm_Add(Asm_Add(Asm_RotateLeft(atoe.a, 5),
                                             ft_impl(currentStep, atoe.b, atoe.c, atoe.d)),
                                     atoe.e),
                             Ks[currentStep]),
                     W[currentStep]);
    next_atoe := atoe_c(T, atoe.a, Asm_RotateLeft(atoe.b, 30), atoe.c, atoe.d);
    next_z := SHA1Trace_c(z.M, z.H, z.W, z.atoe[..currentBlock] + [z.atoe[currentBlock] + [next_atoe]]);
    ghost var next_s := SHA1_vars_to_state(M, words, H, W, Ks, next_atoe, num_blocks);

    lemma_SHA1TransitionOKAfterSettingAtoE(z, s, next_z, next_s, currentBlock, currentStep);
}

static method ComputeHsForBlockStep1_SHA1(M:array<int>, words:int, H:array<int>, W:array<int>, Ks:array<int>,
                                          atoe:atoe_Type, num_blocks:int, ghost z:SHA1Trace, currentBlock:int)
    requires H != null && H.Length == 5;
    requires W != null;
    requires Ks != null;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires IsSHA1ReadyForStep(z, SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks), currentBlock, 80);
    requires H != W && H != Ks && H != M;
    modifies H;
    ensures Ks[..] == old(Ks[..]);
    ensures W[..] == old(W[..]);
    ensures M[..] == old(M[..]);
    ensures forall j :: 0 <= j < 5 ==> Word32(H[j]) && H[j] == Add32(ConvertAtoEToSeq_premium(atoe)[j], old(H[j]));
{
    ghost var s := SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks);
    ghost var atoe_seq := ConvertAtoEToSeq_premium(atoe);

    H[0], H[1], H[2], H[3], H[4] := Asm_Add(atoe.a, H[0]), Asm_Add(atoe.b, H[1]), Asm_Add(atoe.c, H[2]),
                                    Asm_Add(atoe.d, H[3]), Asm_Add(atoe.e, H[4]);

    forall j | 0 <= j < 5
        ensures Word32(H[j]);
        ensures H[j] == Add32(ConvertAtoEToSeq_premium(atoe)[j], s.H[j]);
        ensures M[..] == old(M[..]);
        ensures W[..] == old(W[..]);
    {
        ghost var atoe_seq := ConvertAtoEToSeq_premium(atoe);
        if j == 0 { assert H[0] == Add32(atoe_seq[0], s.H[0]); }
        else if j == 1 { assert H[1] == Add32(atoe_seq[1], s.H[1]); }
        else if j == 2 { assert H[2] == Add32(atoe_seq[2], s.H[2]); }
        else if j == 3 { assert H[3] == Add32(atoe_seq[3], s.H[3]); }
        else if j == 4 { assert H[4] == Add32(atoe_seq[4], s.H[4]); }
    }
}

static method ComputeHsForBlock_SHA1(M:array<int>, words:int, H:array<int>, W:array<int>, Ks:array<int>, atoe:atoe_Type,
                                     num_blocks:int, ghost z:SHA1Trace, currentBlock:int)
                                     returns (ghost next_z:SHA1Trace)
    requires H != null && H.Length == 5;
    requires W != null;
    requires Ks != null;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires IsSHA1ReadyForStep(z, SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks), currentBlock, 80);
    requires H != W && H != Ks && H != M;
    modifies H;
    ensures Ks[..] == old(Ks[..]);
    ensures W[..] == old(W[..]);
    ensures M[..] == old(M[..]);
    ensures IsSHA1ReadyForBlock(next_z, SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks), currentBlock+1);
{
    ghost var s := SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks);

    ComputeHsForBlockStep1_SHA1(M, words, H, W, Ks, atoe, num_blocks, z, currentBlock);

    next_z := SHA1Trace_c(z.M, z.H + [H[..]], z.W, z.atoe);
    ghost var next_s := SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks);

    lemma_SHA1TransitionOKAfterSettingHs(z, s, next_z, next_s, currentBlock);
}

static method PerformOneBlockOfSHA1Computation(M:array<int>, words:int, H:array<int>, W:array<int>, Ks:array<int>,
                                               atoe:atoe_Type, num_blocks:int, ghost z:SHA1Trace, currentBlock:int)
                                               returns (next_atoe:atoe_Type, ghost next_z:SHA1Trace)
    requires H != null && H.Length == 5;
    requires W != null && W.Length == 80;
    requires Ks != null;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires IsSHA1ReadyForBlock(z, SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks), currentBlock);
    requires W != H && W != Ks && W != M && H != Ks && H != M;
    modifies H;
    modifies W;
    ensures M[..] == old(M[..]);
    ensures Ks[..] == old(Ks[..]);
    ensures IsSHA1ReadyForBlock(next_z, SHA1_vars_to_state(M, words, H, W, Ks, next_atoe, num_blocks), currentBlock+1);
{
    var current_z := ComputeWsForBlock_SHA1(M, words, H, W, Ks, atoe, num_blocks, z, currentBlock);
    var current_atoe:atoe_Type;
    current_atoe, current_z := ComputeInitialAtoEForBlock_SHA1(M, words, H, W, Ks, atoe, num_blocks, current_z, currentBlock);

    var t := 0;
    while t < 80
        invariant 0 <= t <= 80;
        invariant M[..] == old(M[..]);
        invariant Ks[..] == old(Ks[..]);
        invariant IsSHA1ReadyForStep(current_z, SHA1_vars_to_state(M, words, H, W, Ks, current_atoe, num_blocks), currentBlock, t);
    {
        current_atoe, current_z := ComputeOneStep_SHA1(M, words, H, W, Ks, current_atoe, num_blocks, current_z, currentBlock, t);
        t := t + 1;
    }

    current_z := ComputeHsForBlock_SHA1(M, words, H, W, Ks, current_atoe, num_blocks, current_z, currentBlock);

    next_atoe := current_atoe;
    next_z := current_z;
}

static lemma Lemma_IsSHA1ReadyForLastBlockImpliesTraceIsCorrect(messageBits:seq<int>, z:SHA1Trace, s:SHA1_state)
    requires 0 <= s.num_blocks;
    requires IsSHA1ReadyForBlock(z, s, s.num_blocks);
    ensures SHA1TraceIsCorrect(z);
{
    reveal_PartialSHA1TraceHasCorrectatoesOpaque();
}

static lemma Lemma_IsSHA1Demonstration(messageBits:seq<int>, hash:seq<int>, z:SHA1Trace)
    requires IsBitSeq(messageBits);
    requires |messageBits| < power2(64);
    requires IsCompleteSHA1Trace(z);
    requires z.M == BlockMessageForSHA(PadMessageForSHA_premium(messageBits));
    requires SHA1TraceIsCorrect(z);
    requires hash == z.H[|z.M|];
    ensures IsSHA1(messageBits, hash);
{
}

static lemma Lemma_MessageInSHA1TraceCorrespondsToMessageInArray(M:array<int>, words:int, messageBits:seq<int>, z:SHA1Trace)
    requires M != null;
    requires 0 <= words <= M.Length;
    requires Mod16(words) == 0;
    requires forall i :: 0 <= i < words ==> Word32(M[i]);
    requires IsBitSeq(messageBits);
    requires |messageBits| < power2(64);
    requires BEWordSeqToBitSeq(M[..words]) == PadMessageForSHA(messageBits);
    requires z.M == BreakIntoBlocks(M[..words], 16);
    ensures z.M == BlockMessageForSHA(PadMessageForSHA_premium(messageBits));
{
    assert |BEWordSeqToBitSeq_premium(M[..words])| == words * 32;
    calc {
        z.M;
        BreakIntoBlocks(M[..words], 16);
        { reveal_power2();
          lemma_BEDigitSeqToInt_invertibility(power2(32), BEDigitSeqToInt_premium(power2(32), M[..words]), M[..words]); }
        BreakIntoBlocks(BEIntToDigitSeq(power2(32), words, BEWordSeqToInt_premium(M[..words])), 16);
        { lemma_BEBitSeqToInt_BEWordSeqToBitSeq(M[..words]); }
        BreakIntoBlocks(BEIntToDigitSeq(power2(32), words, BEBitSeqToInt(BEWordSeqToBitSeq(M[..words]))), 16);
        BreakIntoBlocks(BEIntToDigitSeq(power2(32), words, BEBitSeqToInt(PadMessageForSHA(messageBits))), 16);
        { lemma_mul_is_mul_boogie(words, 32); lemma_div_by_multiple(words, 32); assert (words*32)/32 == words; }
        BreakIntoBlocks(BEIntToDigitSeq(power2(32), (words*32)/32, BEBitSeqToInt(PadMessageForSHA(messageBits))), 16);
        BreakIntoBlocks(BEIntToDigitSeq(power2(32), |BEWordSeqToBitSeq_premium(M[..words])|/32, BEBitSeqToInt(PadMessageForSHA(messageBits))), 16);
        BreakIntoBlocks(BEIntToDigitSeq(power2(32), |PadMessageForSHA(messageBits)|/32, BEBitSeqToInt(PadMessageForSHA(messageBits))), 16);
        { reveal_BlockMessageForSHA(); lemma_PadMessageForSHA_properties(messageBits); }
        BlockMessageForSHA(PadMessageForSHA(messageBits));
    }
}

static method{:dafnycc_conservative_seq_triggers} ComputeSHA1AfterPadding_arrays(M:array<int>, words:int, ghost messageBits:seq<int>) returns (hash:array<int>)
    requires M != null;
    requires 0 <= words <= M.Length;
    requires Mod16(words) == 0;
    requires forall i :: 0 <= i < words ==> Word32(M[i]);
    requires IsBitSeq(messageBits);
    requires |messageBits| < power2(64);
    requires BEWordSeqToBitSeq(M[..words]) == PadMessageForSHA(messageBits);
    ensures hash!=null;
    ensures IsSHA1(messageBits, hash[..]);
{
    

    var H := new int[5];
    var W := new int[80];
    var Ks := new int[80];

    

    var atoe:atoe_Type;
    var num_blocks:int;
    ghost var z:SHA1Trace;
    atoe, num_blocks, z := InitializeVars_SHA1(M, words, H, W, Ks);

    

    var currentBlock:int := 0;
    while currentBlock < num_blocks
        invariant 0 <= currentBlock <= num_blocks;
        invariant M[..] == old(M[..]);
        invariant BEWordSeqToBitSeq(M[..words]) == PadMessageForSHA(messageBits);
        invariant IsSHA1ReadyForBlock(z, SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks), currentBlock);
    {
        atoe, z := PerformOneBlockOfSHA1Computation(M, words, H, W, Ks, atoe, num_blocks, z, currentBlock);
        currentBlock := currentBlock + 1;
    }

    

    hash := H;

    

    Lemma_MessageInSHA1TraceCorrespondsToMessageInArray(M, words, messageBits, z);
    Lemma_IsSHA1ReadyForLastBlockImpliesTraceIsCorrect(messageBits, z, SHA1_vars_to_state(M, words, H, W, Ks, atoe, num_blocks));
    Lemma_IsSHA1Demonstration(messageBits, H[..], z);
}

static method{:dafnycc_conservative_seq_triggers} ComputeSHA1AfterPadding(M:array<int>, words:int, ghost messageBits:seq<int>) returns (hash:seq<int>)
    requires M != null;
    requires 0 <= words <= M.Length;
    requires Mod16(words) == 0;
    requires forall i :: 0 <= i < words ==> Word32(M[i]);
    requires IsBitSeq(messageBits);
    requires |messageBits| < power2(64);
    requires BEWordSeqToBitSeq(M[..words]) == PadMessageForSHA(messageBits);
    ensures IsSHA1(messageBits, hash[..]);
{
    var H := ComputeSHA1AfterPadding_arrays(M, words, messageBits);
    hash := H[..];
}

static lemma lemma_PaddedLength_words(message_len:int, padded_len:int, words:int)
    requires padded_len == PaddedLength(message_len);
    requires words == padded_len / 32;
    ensures  padded_len == words * 32;
{
    lemma_PaddedLength_properties(message_len);
}

static method{:dafnycc_conservative_seq_triggers} SHA1_impl_ArrayInPlace(M:array<int>, bits:int) returns (hash:seq<int>)
    requires IsWordArray(M);
    requires Word32(bits);
    requires 0 <= bits < power2(64);
    requires 0 <= PaddedLength(bits) <= M.Length * 32;
    ensures bits <= M.Length * 32;
    ensures IsWordSeqOfLen(hash, 5);
    ensures IsSHA1(old(BEWordSeqToBitSeq_premium(M[..])[..bits]), hash);
    ensures hash == SHA1(old(BEWordSeqToBitSeq_premium(M[..])[..bits]));
    modifies M;
{
    calc <= { bits; { lemma_PaddedLength_properties(bits); } |BEWordSeqToBitSeq_premium(M[..])|; }

    ghost var messageBits := BEWordSeqToBitSeq_premium(M[..])[..bits];
    PadMessageArray(M, bits);
    var words := PaddedLength(bits)/32;

    calc {
        PadMessageForSHA(messageBits);
        BEWordSeqToBitSeq_premium(M[..])[..PaddedLength(bits)];
        { lemma_PaddedLength_properties(bits); }
        BEWordSeqToBitSeq_premium(M[..])[..words*32];
        { lemma_WordSeqToBitSeqChop(M[..], M[..words], M[words..]); }
        (BEWordSeqToBitSeq_premium(M[..words]) + BEWordSeqToBitSeq_premium(M[words..]))[..words*32];
        BEWordSeqToBitSeq_premium(M[..words])[..words*32];
        BEWordSeqToBitSeq_premium(M[..words]);
    }

    lemma_mod_words(bits, words);

    hash := ComputeSHA1AfterPadding(M, words, messageBits);
    lemma_SHA1IsAFunction(old(BEWordSeqToBitSeq_premium(M[..])[..bits]), hash);
}

static method SHA1_impl_Bytes(messageBytes:seq<int>) returns (hash:seq<int>)
    requires Word32(|messageBytes|*8);
    requires |messageBytes|*8 < power2(64);
    requires IsByteSeq(messageBytes);
    ensures IsWordSeqOfLen(hash, 5);
    ensures IsSHA1(BEByteSeqToBitSeq_premium(messageBytes), hash);
    ensures hash == SHA1(BEByteSeqToBitSeq_premium(messageBytes));
{
    var M, bits := CreateArrayForSHA(messageBytes);
    hash := SHA1_impl_ArrayInPlace(M, bits);
    lemma_SHA1IsAFunction(BEByteSeqToBitSeq_premium(messageBytes), hash);
}

static method SHA1_impl_Bytes_arrays(messageBytes:array<int>) returns (hash:array<int>)
    requires messageBytes != null;
    requires Word32(messageBytes.Length*8);
    requires messageBytes.Length*8 < power2(64);
    requires IsByteSeq(messageBytes[..]);
    ensures hash != null;
    ensures IsWordSeqOfLen(hash[..], 5);
    ensures IsSHA1(BEByteSeqToBitSeq_premium(messageBytes[..]), hash[..]);
    ensures hash[..] == SHA1(BEByteSeqToBitSeq_premium(messageBytes[..]));
{
    
    var M, bits := CreateArrayForSHA_arrays(messageBytes);
    ghost var Minput_seq := M[..];
    assert BEByteSeqToBitSeq_premium(messageBytes[..]) == BEWordSeqToBitSeq(Minput_seq)[..bits];
    ghost var oldMessageBytes_seq := old(messageBytes)[..];
    
    

    ghost var messageBits := BEWordSeqToBitSeq_premium(M[..])[..bits];
    PadMessageArray(M, bits);
    var words := PaddedLength(bits)/32;
    
    calc {
        PadMessageForSHA(messageBits);
        BEWordSeqToBitSeq_premium(M[..])[..PaddedLength(bits)];
        { lemma_PaddedLength_words(bits, PaddedLength(bits), words); }
        BEWordSeqToBitSeq_premium(M[..])[..words*32];
        { lemma_WordSeqToBitSeqChop(M[..], M[..words], M[words..]); }
        (BEWordSeqToBitSeq_premium(M[..words]) + BEWordSeqToBitSeq_premium(M[words..]))[..words*32];
        BEWordSeqToBitSeq_premium(M[..words])[..words*32];
        BEWordSeqToBitSeq_premium(M[..words]);
    }

    lemma_mod_words(bits, words);

    hash := ComputeSHA1AfterPadding_arrays(M, words, messageBits);


    ghost var hash_seq := hash[..];

    ghost var messageBytes_seq := old(messageBytes)[..];
    assert IsSHA1(messageBits, hash_seq);
 
    assert old(messageBytes)[..] == oldMessageBytes_seq;

    lemma_SHA_impl_Bytes_arrays_bitmangle(old(messageBytes), messageBytes_seq, messageBits, Minput_seq, bits);
    assert IsSHA1(BEByteSeqToBitSeq_premium(messageBytes_seq), hash_seq);
    lemma_SHA1IsAFunction(BEByteSeqToBitSeq_premium(messageBytes_seq), hash_seq);
}
    
