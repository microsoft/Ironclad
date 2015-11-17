//- Stuff shared by sha256.i.dfy and sha256opt.i.dfy

include "sha256.s.dfy"
include "../../Util/seq_blocking.i.dfy"
include "../../Util/arrays_and_seqs.i.dfy"
include "../../Util/integer_sequences_premium.i.dfy"
include "sha_padding.i.dfy"
include "sha_common.i.dfy"
include "../../../Drivers/CPU/assembly_premium.i.dfy"

static predicate Word32AtoH(v:atoh_Type)
{
    Word32(v.a) && Word32(v.b) && Word32(v.c) && Word32(v.d) && Word32(v.e) && Word32(v.f) && Word32(v.g) && Word32(v.h)
}

static predicate IsAToHWordSeq(vs:seq<atoh_Type>)
{
    forall i :: 0 <= i < |vs| ==> Word32AtoH(vs[i])
}

//-///////////////////////////////////////////////////
//- Intermediate SHA256 state
//-///////////////////////////////////////////////////

datatype SHA256_state = SHA256_state_c(M:seq<int>, H:seq<int>, W:seq<int>, atoh:atoh_Type, num_blocks:int);

static function SHA256_vars_to_state(M:array<int>, words:int, H:array<int>, W:array<int>, atoh:atoh_Type, num_blocks:int)
                                    : SHA256_state
    requires M != null && H != null && W != null;
    requires 0 <= words <= M.Length;
    reads M, H, W;
{
    SHA256_state_c(M[..words], H[..], W[..], atoh, num_blocks)
}

static predicate PartialSHA256TraceHasCorrectHs(z:SHA256Trace)
{
    |z.H| > 0 &&
    |z.H| <= |z.atoh|+1 &&
    (forall blk :: 0 <= blk < |z.H| ==> IsWordSeqOfLen(z.H[blk], 8)) &&
    (forall j :: 0 <= j < 8 ==> z.H[0][j] == InitialH_SHA256(j)) &&
    (forall blk {:trigger TBlk(blk)} :: TBlk(blk) && 0 <= blk < |z.H|-1 ==>
        IsAToHWordSeqOfLen(z.atoh[blk], 65) &&
        forall j :: 0 <= j < 8 ==> z.H[blk+1][j] == Add32(ConvertAtoHToSeq(z.atoh[blk][64])[j], z.H[blk][j]))
}

static predicate PartialSHA256TraceHasCorrectWs(z:SHA256Trace)
{
    |z.W| <= |z.M| &&
    forall blk :: 0 <= blk < |z.W| ==>
        IsWordSeqOfLen(z.W[blk], 64) &&
        IsWordSeqOfLen(z.M[blk], 16) &&
        forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < 64 ==>
            (0 <= t <= 15 ==> z.W[blk][t] == z.M[blk][t]) &&
            (16 <= t <= 63 ==> z.W[blk][t] == Add32(Add32(Add32(SSIG1(z.W[blk][t-2]), z.W[blk][t-7]), SSIG0(z.W[blk][t-15])),
                                                      z.W[blk][t-16]))
}

static predicate PartialSHA256TraceHasCorrectatohsWf(z:SHA256Trace)
{
    |z.atoh| <= |z.H| &&
    |z.atoh| <= |z.W| &&
    (forall blk :: 0 <= blk < |z.atoh|-1 ==> IsAToHWordSeqOfLen(z.atoh[blk], 65)) &&
    forall blk :: 0 <= blk < |z.atoh| ==>
        |z.atoh[blk]| <= 65 &&
        IsWordSeqOfLen(z.W[blk], 64) &&
        IsAToHWordSeq(z.atoh[blk]) &&
        (|z.atoh[blk]| > 0 ==> IsWordSeqOfLen(z.H[blk], 8) && ConvertAtoHToSeq(z.atoh[blk][0]) == z.H[blk])
}

static predicate{:opaque} PartialSHA256TraceHasCorrectatohsOpaque(z:SHA256Trace)
{
    |z.atoh| <= |z.H| &&
    |z.atoh| <= |z.W| &&
    (forall blk :: 0 <= blk < |z.atoh|-1 ==> IsAToHWordSeqOfLen(z.atoh[blk], 65)) &&
    forall blk :: 0 <= blk < |z.atoh| ==>
        |z.atoh[blk]| <= 65 &&
        IsWordSeqOfLen(z.W[blk], 64) &&
        IsAToHWordSeq(z.atoh[blk]) &&
        (|z.atoh[blk]| > 0 ==> IsWordSeqOfLen(z.H[blk], 8) && ConvertAtoHToSeq(z.atoh[blk][0]) == z.H[blk]) &&
        forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < |z.atoh[blk]|-1 ==>
            var T1 := Add32(Add32(Add32(Add32(z.atoh[blk][t].h, BSIG1(z.atoh[blk][t].e)),
                                              Ch(z.atoh[blk][t].e, z.atoh[blk][t].f, z.atoh[blk][t].g)),
                                      K_SHA256(t)),
                              z.W[blk][t]);
            var T2 := Add32(BSIG0(z.atoh[blk][t].a), Maj(z.atoh[blk][t].a, z.atoh[blk][t].b, z.atoh[blk][t].c));
            z.atoh[blk][t+1].h == z.atoh[blk][t].g &&
            z.atoh[blk][t+1].g == z.atoh[blk][t].f &&
            z.atoh[blk][t+1].f == z.atoh[blk][t].e &&
            z.atoh[blk][t+1].e == Add32(z.atoh[blk][t].d, T1) &&
            z.atoh[blk][t+1].d == z.atoh[blk][t].c &&
            z.atoh[blk][t+1].c == z.atoh[blk][t].b &&
            z.atoh[blk][t+1].b == z.atoh[blk][t].a &&
            z.atoh[blk][t+1].a == Add32(T1, T2)
}

static predicate PartialSHA256TraceHasCorrectatohs(z:SHA256Trace)
{
    PartialSHA256TraceHasCorrectatohsWf(z) && PartialSHA256TraceHasCorrectatohsOpaque(z)
}

static predicate PartialSHA256TraceIsCorrect(z:SHA256Trace)
{
    PartialSHA256TraceHasCorrectWs(z) && PartialSHA256TraceHasCorrectHs(z) && PartialSHA256TraceHasCorrectatohs(z)
}

static predicate AreSHA256TraceAndStateOK(z:SHA256Trace, s:SHA256_state)
{
    PartialSHA256TraceIsCorrect(z) &&
    IsWordSeq(s.M) &&
    z.M == BreakIntoBlocks(s.M, 16) &&
    (forall i :: 0 <= i < |z.M| ==> IsWordSeqOfLen(z.M[i], 16)) &&
    Mul16(|z.M|) == |s.M| &&
    |z.M| == s.num_blocks
}


static predicate IsSHA256ReadyForBlock(z:SHA256Trace, s:SHA256_state, nextBlock:int)
    requires 0 <= nextBlock;
{
    AreSHA256TraceAndStateOK(z, s) &&
    |z.H| == nextBlock + 1 &&
    |z.W| == nextBlock &&
    |z.atoh| == nextBlock &&
    (forall blk :: 0 <= blk < nextBlock ==> IsAToHWordSeqOfLen(z.atoh[blk], 65)) &&
    s.H == z.H[nextBlock]
}

static predicate{:opaque} TheAToHsAreOK(z:SHA256Trace, blk: int, t: int)
    requires 0 <= t <= 63;
    requires 0 <= blk;
    requires |z.atoh| > blk;
    requires |z.atoh[blk]| > t+1;
    requires Word32AtoH(z.atoh[blk][t]);
    requires |z.W| > blk;
    requires IsWordSeqOfLen(z.W[blk], 64);
{
    var T1 := Add32(Add32(Add32(Add32(z.atoh[blk][t].h, BSIG1(z.atoh[blk][t].e)),
                                      Ch(z.atoh[blk][t].e, z.atoh[blk][t].f, z.atoh[blk][t].g)),
                              K_SHA256(t)),
                      z.W[blk][t]);
    var T2 := Add32(BSIG0(z.atoh[blk][t].a), Maj(z.atoh[blk][t].a, z.atoh[blk][t].b, z.atoh[blk][t].c));
    z.atoh[blk][t+1].h == z.atoh[blk][t].g &&
    z.atoh[blk][t+1].g == z.atoh[blk][t].f &&
    z.atoh[blk][t+1].f == z.atoh[blk][t].e &&
    z.atoh[blk][t+1].e == Add32(z.atoh[blk][t].d, T1) &&
    z.atoh[blk][t+1].d == z.atoh[blk][t].c &&
    z.atoh[blk][t+1].c == z.atoh[blk][t].b &&
    z.atoh[blk][t+1].b == z.atoh[blk][t].a &&
    z.atoh[blk][t+1].a == Add32(T1, T2)
}

static predicate IsSHA256ReadyForStep(z:SHA256Trace, s:SHA256_state, currentBlock:int, nextStep:int)
    requires 0 <= currentBlock;
    requires 0 <= nextStep <= 64;
{
    AreSHA256TraceAndStateOK(z, s) &&
    |z.H| == currentBlock + 1 &&
    |z.W| == currentBlock + 1 &&
    |z.atoh| == currentBlock + 1 &&
    (forall blk :: 0 <= blk < currentBlock ==> IsAToHWordSeqOfLen(z.atoh[blk], 65)) &&
    IsAToHWordSeqOfLen(z.atoh[currentBlock], nextStep+1) &&
    s.H == z.H[currentBlock] &&
    s.W == z.W[currentBlock] &&
    s.atoh == z.atoh[currentBlock][nextStep]
}

static lemma lemma_SHA256TransitionOKAfterSettingAtoHStep1Helper1(z:SHA256Trace, blk:int, t:int)
    requires 0 <= t <= 63;
    requires 0 <= blk;
    requires |z.atoh| > blk;
    requires |z.atoh[blk]| > t+1;
    requires Word32AtoH(z.atoh[blk][t]);
    requires |z.W| > blk;
    requires IsWordSeqOfLen(z.W[blk], 64);
    requires PartialSHA256TraceHasCorrectatohs(z);
    ensures TheAToHsAreOK(z, blk, t);
{
    assert TBlk(blk) && TStep(t);
    reveal_TheAToHsAreOK();
    reveal_PartialSHA256TraceHasCorrectatohsOpaque();
}

static lemma Lemma_TheAToHsAreOKIsStable(z1:SHA256Trace, z2:SHA256Trace, blk: int, t: int)
    requires 0 <= t <= 63;
    requires 0 <= blk;
    requires |z1.atoh| == |z2.atoh| > blk;
    requires |z1.atoh[blk]| > t+1;
    requires |z2.atoh[blk]| > t+1;
    requires Word32AtoH(z1.atoh[blk][t]);
    requires z1.atoh[blk][t+1] == z2.atoh[blk][t+1];
    requires z1.atoh[blk][t] == z2.atoh[blk][t];
    requires |z1.W| > blk;
    requires z1.W == z2.W;
    requires IsWordSeqOfLen(z1.W[blk], 64);
    requires TheAToHsAreOK(z1, blk, t);
    ensures TheAToHsAreOK(z2, blk, t);
{
    reveal_TheAToHsAreOK();
}

static lemma {:timeLimitMultiplier 2} lemma_SHA256TransitionOKAfterSettingAtoHStep1(z1:SHA256Trace, s1:SHA256_state, z2:SHA256Trace, s2:SHA256_state,
                                                                                    currentBlock:int, currentStep:int)
    requires TBlk(currentBlock) && TBlk(currentBlock + 1) && TStep(currentStep) && TStep(currentStep + 1);
    requires 0 <= currentBlock < |z1.M|;
    requires 0 <= currentStep <= 63;
    requires IsSHA256ReadyForStep(z1, s1, currentBlock, currentStep);
    requires var T1 := Asm_Add(Asm_Add(Asm_Add(Asm_Add(s1.atoh.h, BSIG1(s1.atoh.e)), Ch(s1.atoh.e, s1.atoh.f, s1.atoh.g)),
                                       K_SHA256(currentStep)),
                               s1.W[currentStep]);
             var T2 := Asm_Add(BSIG0(s1.atoh.a), Maj(s1.atoh.a, s1.atoh.b, s1.atoh.c));
             s2.atoh.h == s1.atoh.g &&
             s2.atoh.g == s1.atoh.f &&
             s2.atoh.f == s1.atoh.e &&
             s2.atoh.e == Asm_Add(s1.atoh.d, T1) &&
             s2.atoh.d == s1.atoh.c &&
             s2.atoh.c == s1.atoh.b &&
             s2.atoh.b == s1.atoh.a &&
             s2.atoh.a == Asm_Add(T1, T2);
    requires s2.M == s1.M;
    requires s2.H == s1.H;
    requires s2.W == s1.W;
    requires s2.num_blocks == s1.num_blocks;
    requires z2.M == z1.M && z2.H == z1.H && z2.W == z1.W;
    requires z2.atoh == z1.atoh[..currentBlock] + [z1.atoh[currentBlock] + [s2.atoh]];
    requires |z2.atoh| == |z1.atoh|;
    requires forall blk :: 0 <= blk < currentBlock ==> z2.atoh[blk] == z1.atoh[blk];
    requires forall t :: 0 <= t < |z1.atoh[currentBlock]| ==> z2.atoh[currentBlock][t] == z1.atoh[currentBlock][t];
    requires z2.atoh[currentBlock][|z1.atoh[currentBlock]|] == s2.atoh;
    ensures forall blk :: 0 <= blk < |z2.atoh| ==>
        |z2.atoh[blk]| <= |z2.W[blk]| + 1 &&
        |z2.atoh[blk]| <= 65 &&
        IsWordSeq(z2.W[blk]) &&
        IsAToHWordSeq(z2.atoh[blk]) &&
        (|z2.atoh[blk]| > 0 ==> IsWordSeqOfLen(z2.H[blk], 8) && ConvertAtoHToSeq(z2.atoh[blk][0]) == z2.H[blk]) &&
        (forall t :: 0 <= t < |z2.atoh[blk]|-1 ==> TheAToHsAreOK(z2, blk, t));
{
    forall blk | TBlk(blk) && 0 <= blk < |z2.atoh|
        ensures |z2.atoh[blk]| <= |z2.W[blk]| + 1;
        ensures |z2.atoh[blk]| <= 65;
        ensures IsWordSeq(z2.W[blk]);
        ensures IsAToHWordSeq(z2.atoh[blk]);
        ensures (|z2.atoh[blk]| > 0 ==> IsWordSeqOfLen(z2.H[blk], 8) && ConvertAtoHToSeq(z2.atoh[blk][0]) == z2.H[blk]);
        ensures forall t :: 0 <= t < |z2.atoh[blk]|-1 ==> TheAToHsAreOK(z2, blk, t);
    {
        assert |z2.atoh[blk]| <= |z2.W[blk]| + 1;
        assert |z2.atoh[blk]| <= 65;
        assert IsWordSeq(z2.W[blk]);

        if blk < |z2.atoh|-1 {
            assert blk < currentBlock;
            assert z2.atoh[blk] == z1.atoh[blk];
            assert IsAToHWordSeq(z2.atoh[blk]);
            assert (|z2.atoh[blk]| > 0 ==> IsWordSeqOfLen(z2.H[blk], 8) && ConvertAtoHToSeq(z2.atoh[blk][0]) == z2.H[blk]);
            forall t | 0 <= t < |z1.atoh[blk]|-1
                ensures TheAToHsAreOK(z2, blk, t);
            {
                lemma_SHA256TransitionOKAfterSettingAtoHStep1Helper1(z1, blk, t);
                Lemma_TheAToHsAreOKIsStable(z1, z2, blk, t);
            }
            assert forall t :: 0 <= t < |z2.atoh[blk]|-1 ==> TheAToHsAreOK(z2, blk, t);
        }
        else {
            assert blk == currentBlock;
            assert IsAToHWordSeq(z2.atoh[blk]);
            assert (|z2.atoh[blk]| > 0 ==> IsWordSeqOfLen(z2.H[blk], 8) && ConvertAtoHToSeq(z2.atoh[blk][0]) == z2.H[blk]);
            forall t | 0 <= t < |z2.atoh[blk]|-1
                ensures TheAToHsAreOK(z2, blk, t);
            {
                if t < |z2.atoh[blk]|-2 {
                    assert t < currentStep;
                    lemma_SHA256TransitionOKAfterSettingAtoHStep1Helper1(z1, blk, t);
                    Lemma_TheAToHsAreOKIsStable(z1, z2, blk, t);
                    assert TheAToHsAreOK(z2, blk, t);
                }
                else {
                    assert t == currentStep;
                    calc { true; { reveal_TheAToHsAreOK(); } TheAToHsAreOK(z2, blk, t); }
                }
            }
        }
    }
}

static lemma{:dafnycc_conservative_seq_triggers} lemma_SHA256TransitionOKAfterSettingAtoH(z1:SHA256Trace, s1:SHA256_state, z2:SHA256Trace, s2:SHA256_state,
                                                      currentBlock:int, currentStep:int)
    requires TBlk(currentBlock) && TBlk(currentBlock + 1) && TStep(currentStep) && TStep(currentStep + 1);
    requires 0 <= currentBlock < |z1.M|;
    requires 0 <= currentStep <= 63;
    requires IsSHA256ReadyForStep(z1, s1, currentBlock, currentStep);
    requires var T1 := Asm_Add(Asm_Add(Asm_Add(Asm_Add(s1.atoh.h, BSIG1(s1.atoh.e)), Ch(s1.atoh.e, s1.atoh.f, s1.atoh.g)),
                                       K_SHA256(currentStep)),
                               s1.W[currentStep]);
             var T2 := Asm_Add(BSIG0(s1.atoh.a), Maj(s1.atoh.a, s1.atoh.b, s1.atoh.c));
             s2.atoh.h == s1.atoh.g &&
             s2.atoh.g == s1.atoh.f &&
             s2.atoh.f == s1.atoh.e &&
             s2.atoh.e == Asm_Add(s1.atoh.d, T1) &&
             s2.atoh.d == s1.atoh.c &&
             s2.atoh.c == s1.atoh.b &&
             s2.atoh.b == s1.atoh.a &&
             s2.atoh.a == Asm_Add(T1, T2);
    requires s2.M == s1.M;
    requires s2.H == s1.H;
    requires s2.W == s1.W;
    requires s2.num_blocks == s1.num_blocks;
    requires z2 == SHA256Trace_c(z1.M, z1.H, z1.W, z1.atoh[..currentBlock] + [z1.atoh[currentBlock] + [s2.atoh]]);
    ensures IsSHA256ReadyForStep(z2, s2, currentBlock, currentStep+1);
{
    lemma_SHA256TransitionOKAfterSettingAtoHStep1(z1, s1, z2, s2, currentBlock, currentStep);

    assert forall blk :: 0 <= blk < |z2.atoh| ==>
        |z2.atoh[blk]| <= |z2.W[blk]| + 1 &&
        |z2.atoh[blk]| <= 65 &&
        IsWordSeq(z2.W[blk]) &&
        IsAToHWordSeq(z2.atoh[blk]) &&
        (|z2.atoh[blk]| > 0 ==> IsWordSeqOfLen(z2.H[blk], 8) && ConvertAtoHToSeq(z2.atoh[blk][0]) == z2.H[blk]) &&
        (forall t :: 0 <= t < |z2.atoh[blk]|-1 ==> TheAToHsAreOK(z2, blk, t));

    forall blk | 0 <= blk < |z2.atoh|
        ensures IsAToHWordSeq(z2.atoh[blk]);
        ensures forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < |z2.atoh[blk]|-1 ==>
            Word32AtoH(z2.atoh[blk][t]) &&
            var T1 := Asm_Add(Asm_Add(Asm_Add(Asm_Add(z2.atoh[blk][t].h, BSIG1(z2.atoh[blk][t].e)),
                                              Ch(z2.atoh[blk][t].e, z2.atoh[blk][t].f, z2.atoh[blk][t].g)),
                                      K_SHA256(t)),
                              z2.W[blk][t]);
            var T2 := Asm_Add(BSIG0(z2.atoh[blk][t].a), Maj(z2.atoh[blk][t].a, z2.atoh[blk][t].b, z2.atoh[blk][t].c));
            z2.atoh[blk][t+1].h == z2.atoh[blk][t].g &&
            z2.atoh[blk][t+1].g == z2.atoh[blk][t].f &&
            z2.atoh[blk][t+1].f == z2.atoh[blk][t].e &&
            z2.atoh[blk][t+1].e == Asm_Add(z2.atoh[blk][t].d, T1) &&
            z2.atoh[blk][t+1].d == z2.atoh[blk][t].c &&
            z2.atoh[blk][t+1].c == z2.atoh[blk][t].b &&
            z2.atoh[blk][t+1].b == z2.atoh[blk][t].a &&
            z2.atoh[blk][t+1].a == Asm_Add(T1, T2);
    {
        forall t {:trigger TStep(t)} | TStep(t) && 0 <= t < |z2.atoh[blk]|-1
            ensures Word32AtoH(z2.atoh[blk][t]);
            ensures var T1 := Asm_Add(Asm_Add(Asm_Add(Asm_Add(z2.atoh[blk][t].h, BSIG1(z2.atoh[blk][t].e)),
                                                      Ch(z2.atoh[blk][t].e, z2.atoh[blk][t].f, z2.atoh[blk][t].g)),
                                              K_SHA256(t)),
                                      z2.W[blk][t]);
                    var T2 := Asm_Add(BSIG0(z2.atoh[blk][t].a), Maj(z2.atoh[blk][t].a, z2.atoh[blk][t].b, z2.atoh[blk][t].c));
                    z2.atoh[blk][t+1].h == z2.atoh[blk][t].g &&
                    z2.atoh[blk][t+1].g == z2.atoh[blk][t].f &&
                    z2.atoh[blk][t+1].f == z2.atoh[blk][t].e &&
                    z2.atoh[blk][t+1].e == Asm_Add(z2.atoh[blk][t].d, T1) &&
                    z2.atoh[blk][t+1].d == z2.atoh[blk][t].c &&
                    z2.atoh[blk][t+1].c == z2.atoh[blk][t].b &&
                    z2.atoh[blk][t+1].b == z2.atoh[blk][t].a &&
                    z2.atoh[blk][t+1].a == Asm_Add(T1, T2);
        {
            assert TheAToHsAreOK(z2, blk, t);
            reveal_TheAToHsAreOK();
        }
    }
    reveal_PartialSHA256TraceHasCorrectatohsOpaque();
}

