

include "sha256.s.dfy"
include "../../Util/seq_blocking.i.dfy"
include "../../Util/arrays_and_seqs.i.dfy"
include "../../Util/integer_sequences_premium.i.dfy"
include "sha_padding.i.dfy"
include "sha_common.i.dfy"
include "sha256opt.i.dfy"
include "sha256opt2.i.dfy"
include "sha256common.i.dfy"
include "../../../Drivers/CPU/assembly_premium.i.dfy"

static function method{:CompiledSpec} CompiledSpec_K_SHA256(t: int) : int
static function method{:CompiledSpec} CompiledSpec_InitialH_SHA256(j: int) : int

//-///////////////////////////////////////////////////
//- Utility functions for AtoH
//-///////////////////////////////////////////////////

static function ConvertAtoHToSeq_premium(v:atoh_Type) : seq<int>
    requires Word32AtoH(v);
    ensures IsWordSeqOfLen(ConvertAtoHToSeq_premium(v), 8);
    ensures ConvertAtoHToSeq_premium(v) == ConvertAtoHToSeq(v);
{
    ConvertAtoHToSeq(v)
}


//-///////////////////////////////////////////////////
//- Initialization of data structures
//-///////////////////////////////////////////////////

static method InitH_SHA256(H:array<int>)
    requires H != null && H.Length ==  8;
    ensures forall i :: 0 <= i < H.Length ==> H[i] == InitialH_SHA256(i);
    modifies H;
{
    H[0] := 1779033703;
    H[1] := 3144134277;
    H[2] := 1013904242;
    H[3] := 2773480762;
    H[4] := 1359893119;
    H[5] := 2600822924;
    H[6] :=  528734635;
    H[7] := 1541459225;
    reveal_InitialH_SHA256();
}

//-///////////////////////////////////////////////////
//- Partial SHA256 traces
//-///////////////////////////////////////////////////

static lemma PartialSHA256TraceIsCorrectImpliesTraceIsCorrect(z:SHA256Trace)
    requires IsCompleteSHA256Trace(z);
    requires PartialSHA256TraceIsCorrect(z);
    ensures SHA256TraceIsCorrect(z);
{
    reveal_PartialSHA256TraceHasCorrectatohsOpaque();
}

//-///////////////////////////////////////////////////
//- Intermediate SHA256 state
//-///////////////////////////////////////////////////


static predicate IsSHA256DoneComputingWs(z:SHA256Trace, s:SHA256_state, currentBlock:int)
    requires 0 <= currentBlock;
{
    AreSHA256TraceAndStateOK(z, s) &&
    |z.H| == currentBlock + 1 &&
    |z.W| == currentBlock + 1 &&
    |z.atoh| == currentBlock &&
    (forall blk :: 0 <= blk < currentBlock ==> IsAToHWordSeqOfLen(z.atoh[blk], 65)) &&
    s.H == z.H[currentBlock] &&
    s.W == z.W[currentBlock]
}

//-///////////////////////////////////////////////////
//- Proofs that transitions between states are OK
//-///////////////////////////////////////////////////

static lemma{:dafnycc_conservative_seq_triggers} lemma_SHA256TransitionOKAfterSettingHsStep1(z1:SHA256Trace, s1:SHA256_state, z2:SHA256Trace, s2:SHA256_state,
                                                         currentBlock:int)
    requires 0 <= currentBlock;
    requires IsSHA256ReadyForStep(z1, s1, currentBlock, 64);
    requires s2.M == s1.M;
    requires IsWordSeqOfLen(s2.H, 8);
    requires forall j :: 0 <= j < 8 ==> s2.H[j] == Asm_Add(ConvertAtoHToSeq_premium(s1.atoh)[j], s1.H[j]);
    requires s2.num_blocks == s1.num_blocks;
    requires z2 == SHA256Trace_c(z1.M, z1.H + [s2.H], z1.W, z1.atoh);
    ensures forall blk :: 0 <= blk < |z2.H| ==> IsWordSeqOfLen(z2.H[blk], 8);
    ensures forall blk {:trigger TBlk(blk)} :: TBlk(blk) && 0 <= blk < currentBlock + 1 ==>
        IsAToHWordSeqOfLen(z2.atoh[blk], 65) &&
        forall j :: 0 <= j < 8 ==> z2.H[blk+1][j] == Asm_Add(ConvertAtoHToSeq_premium(z2.atoh[blk][64])[j], z2.H[blk][j]);
{
    assert |z2.H| == currentBlock + 2;

    forall blk | 0 <= blk < |z2.H|
        ensures IsWordSeqOfLen(z2.H[blk], 8);
    {
        if (blk == |z2.H|-1) {
            assert z2.H[blk] == s2.H;
        }
        else {
            assert z2.H[blk] == z1.H[blk];
        }
    }

    assert forall blk {:trigger TBlk(blk)} :: TBlk(blk) && 0 <= blk < currentBlock + 1 ==> IsWordSeqOfLen(z2.H[blk+1], 8);

    forall blk | TBlk(blk) && 0 <= blk < currentBlock + 1
        ensures IsAToHWordSeqOfLen(z2.atoh[blk], 65);
        ensures forall j :: 0 <= j < 8 ==> z2.H[blk+1][j] == Asm_Add(ConvertAtoHToSeq_premium(z2.atoh[blk][64])[j], z2.H[blk][j]);
    {
        assert z2.atoh[blk] == z1.atoh[blk];
        if blk == currentBlock {
            assert IsSHA256ReadyForStep(z1, s1, currentBlock, 64);
            assert IsAToHWordSeqOfLen(z1.atoh[currentBlock], 64+1);
            assert IsAToHWordSeqOfLen(z1.atoh[blk], 65);
            calc {
                true
                ==> forall j :: 0 <= j < 8 ==> s2.H[j] == Asm_Add(ConvertAtoHToSeq_premium(s1.atoh)[j], s1.H[j]);
                ==> { assert z2.H[blk+1] == s2.H; }
                    forall j :: 0 <= j < 8 ==> z2.H[blk+1][j] == Asm_Add(ConvertAtoHToSeq_premium(s1.atoh)[j], s1.H[j]);
                ==> { assert z2.atoh[blk][64] == s1.atoh; }
                    forall j :: 0 <= j < 8 ==> z2.H[blk+1][j] == Asm_Add(ConvertAtoHToSeq_premium(z2.atoh[blk][64])[j], s1.H[j]);
                ==> { assert z2.H[blk] == s1.H; }
                    forall j :: 0 <= j < 8 ==> z2.H[blk+1][j] == Asm_Add(ConvertAtoHToSeq_premium(z2.atoh[blk][64])[j], z2.H[blk][j]);
            }
        }
    }
}

static lemma {:timeLimitMultiplier 3} {:dafnycc_conservative_seq_triggers} lemma_SHA256TransitionOKAfterSettingHs(z1:SHA256Trace, s1:SHA256_state, z2:SHA256Trace, s2:SHA256_state,
                                                    currentBlock:int)
    requires 0 <= currentBlock;
    requires IsSHA256ReadyForStep(z1, s1, currentBlock, 64);
    requires s2.M == s1.M;
    requires IsWordSeqOfLen(s2.H, 8);
    requires forall j :: 0 <= j < 8 ==> s2.H[j] == Asm_Add(ConvertAtoHToSeq_premium(s1.atoh)[j], s1.H[j]);
    requires s2.num_blocks == s1.num_blocks;
    requires z2 == SHA256Trace_c(z1.M, z1.H + [s2.H], z1.W, z1.atoh);
    ensures IsSHA256ReadyForBlock(z2, s2, currentBlock+1);
{
    lemma_SHA256TransitionOKAfterSettingHsStep1(z1, s1, z2, s2, currentBlock);
    reveal_PartialSHA256TraceHasCorrectatohsOpaque();
}

static lemma lemma_Earlier256WsAreWords(W:seq<int>)
    requires IsWordSeqOfLen(W, 64);
    ensures forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < |W| ==>
        (16 <= t <= 63 ==> Word32(W[t-2]) && Word32(W[t-7]) && Word32(W[t-15]) && Word32(W[t-16]));
{
}

static lemma lemma_SHA256TransitionOKAfterSettingWs(z1:SHA256Trace, s1:SHA256_state, z2:SHA256Trace, s2:SHA256_state, currentBlock:int)
    requires 0 <= currentBlock < |z1.M|;
    requires IsSHA256ReadyForBlock(z1, s1, currentBlock);
    requires IsWordSeqOfLen(s2.W, 64);
    requires forall t :: TStep(t) && 0 <= t <= 15 ==> s2.W[t] == z1.M[currentBlock][t];
    requires forall t :: TStep(t) && 16 <= t <= 63 ==> s2.W[t] == Asm_Add(Asm_Add(Asm_Add(SSIG1(s2.W[t-2]), s2.W[t-7]), SSIG0(s2.W[t-15])),
                                                              s2.W[t-16]);
    requires z2 == SHA256Trace_c(z1.M, z1.H, z1.W + [s2.W], z1.atoh);
    requires s2.M == s1.M;
    requires s2.H == s1.H;
    requires s2.num_blocks == s1.num_blocks;
    ensures IsSHA256DoneComputingWs(z2, s2, currentBlock);
{
    assert z2.M == z1.M;
    assert z2.H == z1.H;
    assert |z2.W| == |z1.W| + 1;
    assert forall blk :: 0 <= blk < |z1.W| ==> z2.W[blk] == z1.W[blk];
    assert z2.W[|z1.W|] == s2.W;
    assert z2.atoh == z1.atoh;

    forall blk | 0 <= blk < |z2.W|
        ensures IsWordSeqOfLen(z2.W[blk], 64);
        ensures forall t :: 0 <= t < |z2.W[blk]| ==> (16 <= t <= 63 ==> Word32(z2.W[blk][t-2]) && Word32(z2.W[blk][t-7]) && Word32(z2.W[blk][t-15]) && Word32(z2.W[blk][t-16]));
//-        ensures forall t :: t < |z2.W[blk]| ==> 16 <= t <= 63 ==> Word32(z2.W[blk][t-16]);
//-        ensures forall t :: t < |z2.W[blk]| ==> 16 <= t <= 63 ==> Word32(z2.W[blk][t-15]);
//-        ensures forall t :: t < |z2.W[blk]| ==> 16 <= t <= 63 ==> Word32(z2.W[blk][t-7]);
//-        ensures forall t :: t < |z2.W[blk]| ==> 16 <= t <= 63 ==> Word32(z2.W[blk][t-2]);
        ensures forall t {:trigger TStep(t)} :: TStep(t) && t < |z2.W[blk]| ==>
                (0 <= t <= 15 ==> z2.W[blk][t] == z2.M[blk][t]) &&
                (16 <= t <= 63 ==> z2.W[blk][t] == Asm_Add(Asm_Add(Asm_Add(SSIG1(z2.W[blk][t-2]), z2.W[blk][t-7]), SSIG0(z2.W[blk][t-15])),
                                                      z2.W[blk][t-16]));
    {
        if blk < |z2.W|-1 {
            assert IsWordSeqOfLen(z2.W[blk], 64);
            lemma_Earlier256WsAreWords(z2.W[blk]);
            assert forall t {:trigger TStep(t)} :: TStep(t) && t < |z2.W[blk]| ==>
                (0 <= t <= 15 ==> z2.W[blk][t] == z2.M[blk][t]) &&
                (16 <= t <= 63 ==> z2.W[blk][t] == Asm_Add(Asm_Add(Asm_Add(SSIG1(z2.W[blk][t-2]), z2.W[blk][t-7]), SSIG0(z2.W[blk][t-15])),
                                                      z2.W[blk][t-16]));
        }
        else {
            assert blk == |z2.W|-1;
            assert z2.W[blk] == s2.W;
            lemma_Earlier256WsAreWords(z2.W[blk]);
            assert forall t {:trigger TStep(t)} :: TStep(t) && t < |z2.W[blk]| ==>
                (0 <= t <= 15 ==> z2.W[blk][t] == z2.M[blk][t]) &&
                (16 <= t <= 63 ==> z2.W[blk][t] == Asm_Add(Asm_Add(Asm_Add(SSIG1(z2.W[blk][t-2]), z2.W[blk][t-7]), SSIG0(z2.W[blk][t-15])),
                                                      z2.W[blk][t-16]));
        }
    }
    reveal_PartialSHA256TraceHasCorrectatohsOpaque();
}

//-///////////////////////////////////////////////////
//- Methods for performing SHA-256 calculations
//-///////////////////////////////////////////////////

static method InitializeVars_SHA256(M:array<int>, words:int, H:array<int>, W:array<int>)
                                    returns (a_next:int, b_next:int, c_next:int, d_next:int, e_next:int, f_next:int, g_next:int, h_next:int,ghost atoh:atoh_Type, num_blocks:int, ghost z:SHA256Trace)
    requires H != null && H.Length == 8;
    requires W != null;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires Mod16(words) == 0;
    requires forall i :: 0 <= i < words ==> Word32(M[i]);
    ensures IsSHA256ReadyForBlock(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), 0);
    ensures |z.M| == num_blocks;
    requires H != M && H != W; 
    modifies H;
    ensures M[..] == old(M[..]);
    ensures W[..] == old(W[..]);
    ensures atoh == atoh_c(a_next, b_next, c_next, d_next, e_next, f_next, g_next, h_next);
{
    reveal_Mul16();
    reveal_Mod16();
    reveal_PartialSHA256TraceHasCorrectatohsOpaque();
    InitH_SHA256(H);
    Lemma_AllBlocksAreOfEqualSize(M[..words], 16);
    Lemma_AllBlocksAreWordSeqs(M[..words], 16);
    z := SHA256Trace_c(BreakIntoBlocks(M[..words], 16), [H[..]], [], []);
    num_blocks := words / 16;
    atoh := atoh_c(0, 0, 0, 0, 0, 0, 0, 0);
    a_next, b_next, c_next, d_next, e_next, f_next, g_next, h_next := 0, 0, 0, 0, 0, 0, 0, 0;
}

static method ComputeWsForBlockStep1_SHA256(M:array<int>, words:int, H:array<int>, W:array<int>,
                                            ghost atoh:atoh_Type, num_blocks:int, ghost z:SHA256Trace, currentBlock:int)
    requires H != null;
    requires W != null && W.Length == 64;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires IsSHA256ReadyForBlock(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock);
    requires W != H && W != M;
    modifies W;
    ensures H[..] == old(H[..]);
    ensures M[..] == old(M[..]);
    ensures forall t :: 0 <= t < 16 ==> Word32(W[t]);
    ensures forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < 16 ==> W[t] == z.M[currentBlock][t];
    ensures IsSHA256ReadyForBlock(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock);
{
    ghost var s := SHA256_vars_to_state(M, words, H, W, atoh, num_blocks);

    var t:int := 0;
    var m_index := currentBlock * 16;
    while t < 16
        invariant 0 <= t <= 16;
        invariant m_index == currentBlock * 16 + t;
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
        W[t] := M[m_index];
        calc {
            W[t];
            { lemma_mul_is_mul_boogie(currentBlock, 16);
              Lemma_BlockedSequencePrefixContainsElement(M[..], words, 16, currentBlock, t); }
            BreakIntoBlocks(M[..words], 16)[currentBlock][t];
            BreakIntoBlocks(s.M, 16)[currentBlock][t];
            z.M[currentBlock][t];
        }
        t := t + 1;
        m_index := m_index + 1;
    }
}

static method ComputeWsForBlock_SHA256_original(M:array<int>, words:int, H:array<int>, W:array<int>, ghost atoh:atoh_Type,
                                       num_blocks:int, ghost z:SHA256Trace, currentBlock:int)
                                       returns (ghost next_z:SHA256Trace)
    requires H != null;
    requires W != null && W.Length == 64;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires IsSHA256ReadyForBlock(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock);
    requires W != H && W != M;
    modifies W;
    ensures H[..] == old(H[..]);
    ensures M[..] == old(M[..]);
    ensures IsSHA256DoneComputingWs(next_z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock);
{
    ghost var s := SHA256_vars_to_state(M, words, H, W, atoh, num_blocks);

    ComputeWsForBlockStep1_SHA256(M, words, H, W, atoh, num_blocks, z, currentBlock);
    ComputeWsForBlockStep2_SHA256(M, words, H, W, atoh, num_blocks, z, currentBlock);

    next_z := SHA256Trace_c(z.M, z.H, z.W + [W[..]], z.atoh);
    ghost var next_s := SHA256_vars_to_state(M, words, H, W, atoh, num_blocks);

    lemma_SHA256TransitionOKAfterSettingWs(z, s, next_z, next_s, currentBlock);
}

static method ComputeWsForBlock_SHA256_optimized(M:array<int>, words:int, H:array<int>, W:array<int>, ghost atoh:atoh_Type,
                                       num_blocks:int, ghost z:SHA256Trace, currentBlock:int)
                                       returns (ghost next_z:SHA256Trace)
    requires H != null;
    requires W != null && W.Length == 64;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires IsSHA256ReadyForBlock(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock);
    requires W != H && W != M;
    modifies W;
    ensures H[..] == old(H[..]);
    ensures M[..] == old(M[..]);
    ensures IsSHA256DoneComputingWs(next_z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock);
{
    ghost var s := SHA256_vars_to_state(M, words, H, W, atoh, num_blocks);

    ComputeWsForBlockStep1_SHA256_optimized(M, words, H, W, atoh, num_blocks, z, currentBlock);
    ComputeWsForBlockStep2_SHA256(M, words, H, W, atoh, num_blocks, z, currentBlock);

    next_z := SHA256Trace_c(z.M, z.H, z.W + [W[..]], z.atoh);
    ghost var next_s := SHA256_vars_to_state(M, words, H, W, atoh, num_blocks);

    lemma_SHA256TransitionOKAfterSettingWs(z, s, next_z, next_s, currentBlock);
}

static method ComputeInitialAtoHForBlock_SHA256(M:array<int>, words:int, H:array<int>, W:array<int>,
                                                ghost atoh:atoh_Type, num_blocks:int,
                                                ghost z:SHA256Trace, currentBlock:int)
                                                returns (a_next:int, b_next:int, c_next:int, d_next:int, e_next:int, f_next:int, g_next:int, h_next:int, ghost next_atoh:atoh_Type, ghost next_z:SHA256Trace)
    requires H != null;
    requires W != null;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires IsSHA256DoneComputingWs(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock);
    ensures IsSHA256ReadyForStep(next_z, SHA256_vars_to_state(M, words, H, W, next_atoh, num_blocks), currentBlock, 0);
    ensures next_atoh == atoh_c(a_next, b_next, c_next, d_next, e_next, f_next, g_next, h_next);
{
    reveal_PartialSHA256TraceHasCorrectatohsOpaque();
    a_next, b_next, c_next, d_next, e_next, f_next, g_next, h_next := H[0], H[1], H[2], H[3], H[4], H[5], H[6], H[7];
    next_atoh := atoh_c(H[0], H[1], H[2], H[3], H[4], H[5], H[6], H[7]);
    next_z := SHA256Trace_c(z.M, z.H, z.W, z.atoh + [[next_atoh]]);
}

static method{:dafnycc_conservative_seq_triggers} ComputeOneStep_SHA256(M:array<int>, words:int, H:array<int>, W:array<int>, ghost atoh:atoh_Type, num_blocks:int, a:int, b:int, c:int, d:int, e:int, f:int, g:int, h:int,
                                    ghost z:SHA256Trace, currentBlock:int, currentStep:int)
                                    returns (a_next:int, b_next:int, c_next:int, d_next:int, e_next:int, f_next:int, g_next:int, h_next:int, ghost next_atoh:atoh_Type, ghost next_z:SHA256Trace)
    requires H != null;
    requires W != null;
    requires M != null;
    requires atoh == atoh_c(a, b, c, d, e, f, g, h);
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires 0 <= currentStep <= 63;
    requires IsSHA256ReadyForStep(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock, currentStep);
    ensures IsSHA256ReadyForStep(next_z, SHA256_vars_to_state(M, words, H, W, next_atoh, num_blocks), currentBlock, currentStep+1);

    ensures H[..] == old(H[..]);
    ensures M[..] == old(M[..]);
    ensures W[..] == old(W[..]);
    ensures next_atoh == atoh_c(a_next, b_next, c_next, d_next, e_next, f_next, g_next, h_next);
{
    assert TBlk(currentBlock) && TBlk(currentBlock + 1) && TStep(currentStep) && TStep(currentStep + 1);
    ghost var s := SHA256_vars_to_state(M, words, H, W, atoh, num_blocks);

    var bsig0 := Asm_BitwiseXor(Asm_BitwiseXor(Asm_RotateRight(a, 2), Asm_RotateRight(a, 13)), Asm_RotateRight(a, 22));
    calc {
        bsig0;
        { reveal_BSIG0(); }
        BSIG0(a);
    }
    var bsig1 := Asm_BitwiseXor(Asm_BitwiseXor(Asm_RotateRight(e, 6), Asm_RotateRight(e, 11)), Asm_RotateRight(e, 25));
    calc {
        bsig1;
        { reveal_BSIG1(); }
        BSIG1(e);
    }
    var my_ch := Asm_BitwiseXor(Asm_BitwiseAnd(e, f), Asm_BitwiseAnd(Asm_BitwiseNot(e), g));
    calc {
        my_ch;
        { reveal_Ch(); }
        Ch(e, f, g);
    }
    var my_maj := Asm_BitwiseXor(Asm_BitwiseXor(Asm_BitwiseAnd(a, b), Asm_BitwiseAnd(a, c)), Asm_BitwiseAnd(b, c));
    calc {
        my_maj;
        { reveal_Maj(); }
        Maj(a, b, c);
    }

    var K := K_SHA256(currentStep);
    var T1 := Asm_Add(Asm_Add(Asm_Add(Asm_Add(h, bsig1), my_ch), K), W[currentStep]);
    var T2 := Asm_Add(bsig0, my_maj);
    a_next, b_next, c_next, d_next, e_next, f_next, g_next, h_next := Asm_Add(T1, T2), a, b, c, Asm_Add(d, T1), e, f, g;
    next_atoh := atoh_c(Asm_Add(T1, T2), atoh.a, atoh.b, atoh.c, Asm_Add(atoh.d, T1), atoh.e, atoh.f, atoh.g);
    next_z := SHA256Trace_c(z.M, z.H, z.W, z.atoh[..currentBlock] + [z.atoh[currentBlock] + [next_atoh]]);
    ghost var next_s := SHA256_vars_to_state(M, words, H, W, next_atoh, num_blocks);

    lemma_SHA256TransitionOKAfterSettingAtoH(z, s, next_z, next_s, currentBlock, currentStep);
}

static method{:dafnycc_conservative_seq_triggers} ComputeHsForBlockStep1_SHA256(a:int, b:int, c:int, d:int, e:int, f:int, g:int, h:int, M:array<int>, words:int, H:array<int>, W:array<int>,
                                            ghost atoh:atoh_Type, num_blocks:int, ghost z:SHA256Trace, currentBlock:int)
    requires atoh == atoh_c(a, b, c, d, e, f, g, h);
    requires H != null && H.Length == 8;
    requires W != null;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires IsSHA256ReadyForStep(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock, 64);
    requires H != W && H != M;
    modifies H;
    ensures W[..] == old(W[..]);
    ensures M[..] == old(M[..]);
    ensures forall j :: 0 <= j < 8 ==> Word32(H[j]) && H[j] == Asm_Add(ConvertAtoHToSeq_premium(atoh)[j], old(H[j]));
{
    ghost var s := SHA256_vars_to_state(M, words, H, W, atoh, num_blocks);
    ghost var atoh_seq := ConvertAtoHToSeq_premium(atoh);

    H[0], H[1], H[2], H[3], H[4], H[5], H[6], H[7] := Asm_Add(a, H[0]), Asm_Add(b, H[1]), Asm_Add(c, H[2]),
                                                      Asm_Add(d, H[3]), Asm_Add(e, H[4]), Asm_Add(f, H[5]),
                                                      Asm_Add(g, H[6]), Asm_Add(h, H[7]);

    forall j | 0 <= j < 8
        ensures Word32(H[j]);
        ensures H[j] == Asm_Add(ConvertAtoHToSeq_premium(atoh)[j], s.H[j]);
        ensures M[..] == old(M[..]);
        ensures W[..] == old(W[..]);
    {
        ghost var atoh_seq := ConvertAtoHToSeq_premium(atoh);
        if j == 0 { assert H[0] == Asm_Add(a, s.H[0]); }
        else if j == 1 { assert H[1] == Asm_Add(b, s.H[1]); }
        else if j == 2 { assert H[2] == Asm_Add(c, s.H[2]); }
        else if j == 3 { assert H[3] == Asm_Add(d, s.H[3]); }
        else if j == 4 { assert H[4] == Asm_Add(e, s.H[4]); }
        else if j == 5 { assert H[5] == Asm_Add(f, s.H[5]); }
        else if j == 6 { assert H[6] == Asm_Add(g, s.H[6]); }
        else if j == 7 { assert H[7] == Asm_Add(h, s.H[7]); }
    }
}

static method{:dafnycc_conservative_seq_triggers} ComputeHsForBlock_SHA256(M:array<int>, words:int, H:array<int>, W:array<int>, ghost atoh:atoh_Type,
                                       num_blocks:int, ghost z:SHA256Trace, currentBlock:int,
                                       a:int, b:int, c:int, d:int, e:int, f:int, g:int, h:int)
                                       returns (ghost next_z:SHA256Trace)
    requires atoh == atoh_c(a, b, c, d, e, f, g, h);
    requires H != null && H.Length == 8;
    requires W != null;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires IsSHA256ReadyForStep(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock, 64);
    requires H != W && H != M;
    modifies H;
    ensures W[..] == old(W[..]);
    ensures M[..] == old(M[..]);
    ensures IsSHA256ReadyForBlock(next_z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock+1);
{
    ghost var s := SHA256_vars_to_state(M, words, H, W, atoh, num_blocks);

    ComputeHsForBlockStep1_SHA256(a, b, c, d, e, f, g, h, M, words, H, W, atoh, num_blocks, z, currentBlock);

    next_z := SHA256Trace_c(z.M, z.H + [H[..]], z.W, z.atoh);
    ghost var next_s := SHA256_vars_to_state(M, words, H, W, atoh, num_blocks);

    lemma_SHA256TransitionOKAfterSettingHs(z, s, next_z, next_s, currentBlock);
}

static method{:dafnycc_conservative_seq_triggers} PerformOneBlockOfSHA256Computation(M:array<int>, words:int, H:array<int>, W:array<int>,
                                                 ghost atoh:atoh_Type, num_blocks:int, ghost z:SHA256Trace, currentBlock:int)
                                                 returns (ghost next_atoh:atoh_Type, ghost next_z:SHA256Trace)
    requires H != null && H.Length == 8;
    requires W != null && W.Length == 64;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires IsSHA256ReadyForBlock(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock);
    requires W != H && W != M && H != M;
    modifies H;
    modifies W;
    ensures M[..] == old(M[..]);
    ensures IsSHA256ReadyForBlock(next_z, SHA256_vars_to_state(M, words, H, W, next_atoh, num_blocks), currentBlock+1);
{
    var current_z := ComputeWsForBlock_SHA256_original(M, words, H, W, atoh, num_blocks, z, currentBlock);
    ghost var current_atoh:atoh_Type;
    var local_a, local_b, local_c, local_d, local_e, local_f, local_g, local_h;
    local_a, local_b, local_c, local_d, local_e, local_f, local_g, local_h, current_atoh, current_z := ComputeInitialAtoHForBlock_SHA256(M, words, H, W, atoh, num_blocks, current_z, currentBlock);
    var t := 0;
    while t < 64
        invariant 0 <= t <= 64;
        invariant M[..] == old(M[..]);
        invariant current_atoh == atoh_c(local_a, local_b, local_c, local_d, local_e, local_f, local_g, local_h);
        invariant IsSHA256ReadyForStep(current_z, SHA256_vars_to_state(M, words, H, W, current_atoh, num_blocks), currentBlock, t);
    {
        local_a, local_b, local_c, local_d, local_e, local_f, local_g, local_h, current_atoh, current_z := ComputeOneStep_SHA256(M, words, H, W, current_atoh, num_blocks, local_a, local_b, local_c, local_d, local_e, local_f, local_g, local_h, current_z, currentBlock, t);
        t := t + 1;
    }

    current_z := ComputeHsForBlock_SHA256(M, words, H, W, current_atoh, num_blocks, current_z, currentBlock, local_a, local_b, local_c, local_d, local_e, local_f, local_g, local_h);

    next_atoh := current_atoh;
    next_z := current_z;
}


static method{:dafnycc_conservative_seq_triggers} PerformOneBlockOfSHA256Computation_optimized(M:array<int>, words:int, H:array<int>, W:array<int>,
                                                 ghost atoh:atoh_Type, num_blocks:int, ghost z:SHA256Trace, currentBlock:int)
                                                 returns (ghost next_atoh:atoh_Type, ghost next_z:SHA256Trace)
    requires H != null && H.Length == 8;
    requires W != null && W.Length == 64;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires IsSHA256ReadyForBlock(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock);
    requires W != H && W != M && H != M;
    modifies H;
    modifies W;
    ensures M[..] == old(M[..]);
    ensures IsSHA256ReadyForBlock(next_z, SHA256_vars_to_state(M, words, H, W, next_atoh, num_blocks), currentBlock+1);
{
    var current_z := ComputeWsForBlock_SHA256_optimized(M, words, H, W, atoh, num_blocks, z, currentBlock);
    ghost var current_atoh:atoh_Type;
    var local_a, local_b, local_c, local_d, local_e, local_f, local_g, local_h;
    local_a, local_b, local_c, local_d, local_e, local_f, local_g, local_h, current_atoh, current_z := ComputeInitialAtoHForBlock_SHA256(M, words, H, W, atoh, num_blocks, current_z, currentBlock);

    local_a, local_b, local_c, local_d, local_e, local_f, local_g, local_h, current_atoh, current_z := ComputeSHA256_optimized_loop(M, words, H, W, current_atoh, num_blocks, local_a, local_b, local_c, local_d, local_e, local_f, local_g, local_h, current_z, currentBlock);

    current_z := ComputeHsForBlock_SHA256(M, words, H, W, current_atoh, num_blocks, current_z, currentBlock, local_a, local_b, local_c, local_d, local_e, local_f, local_g, local_h);
    
    next_atoh := current_atoh;
    next_z := current_z;
}

static lemma Lemma_IsSHA256ReadyForLastBlockImpliesTraceIsCorrect(messageBits:seq<int>, z:SHA256Trace, s:SHA256_state)
    requires 0 <= s.num_blocks;
    requires IsSHA256ReadyForBlock(z, s, s.num_blocks);
    ensures SHA256TraceIsCorrect(z);
{
    reveal_PartialSHA256TraceHasCorrectatohsOpaque();
}

static lemma Lemma_IsSHA256Demonstration(messageBits:seq<int>, hash:seq<int>, z:SHA256Trace)
    requires IsBitSeq(messageBits);
    requires |messageBits| < power2(64);
    requires IsCompleteSHA256Trace(z);
    requires z.M == BlockMessageForSHA(PadMessageForSHA_premium(messageBits));
    requires SHA256TraceIsCorrect(z);
    requires hash == z.H[|z.M|];
    ensures IsSHA256(messageBits, hash);
{
}

static lemma Lemma_MessageInSHA256TraceCorrespondsToMessageInArray(M:array<int>, words:int, messageBits:seq<int>, z:SHA256Trace)
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

static lemma Lemma_ComputeSHA256AfterPadding(M:array<int>, words:int, ghost messageBits:seq<int>, z:SHA256Trace, s:SHA256_state, hash:seq<int>)
    requires M != null;
    requires 0 <= words <= M.Length;
    requires Mod16(words) == 0;
    requires forall i :: 0 <= i < words ==> Word32(M[i]);
    requires IsBitSeq(messageBits);
    requires |messageBits| < power2(64);
    requires BEWordSeqToBitSeq(M[..words]) == PadMessageForSHA(messageBits);
    requires s.M == M[..words];
    requires s.H == hash;
    requires 0 <= s.num_blocks;
    requires IsSHA256ReadyForBlock(z, s, s.num_blocks);
    ensures IsSHA256(messageBits, hash);
{
    Lemma_MessageInSHA256TraceCorrespondsToMessageInArray(M, words, messageBits, z);
    Lemma_IsSHA256ReadyForLastBlockImpliesTraceIsCorrect(messageBits, z, s);
    Lemma_IsSHA256Demonstration(messageBits, hash, z);
}

static method{:dafnycc_conservative_seq_triggers} ComputeSHA256AfterPadding_arrays_original(M:array<int>, words:int, ghost messageBits:seq<int>) returns (hash:array<int>)
    requires M != null;
    requires 0 <= words <= M.Length;
    requires Mod16(words) == 0;
    requires forall i :: 0 <= i < words ==> Word32(M[i]);
    requires IsBitSeq(messageBits);
    requires |messageBits| < power2(64);
    requires BEWordSeqToBitSeq(M[..words]) == PadMessageForSHA(messageBits);
    ensures hash!=null;
    ensures IsSHA256(messageBits, hash[..]);
{
    //- Initialize arrays for use in computing SHA.

    var H := new int[8];
    var W := new int[64];

    //- Initialize state to get ready for first block.

    ghost var atoh:atoh_Type;
    var local_a, local_b, local_c, local_d, local_e, local_f, local_g, local_h;
    var num_blocks:int;
    ghost var z:SHA256Trace;
    local_a, local_b, local_c, local_d, local_e, local_f, local_g, local_h, atoh, num_blocks, z := InitializeVars_SHA256(M, words, H, W);

    //- Loop through the blocks one at a time.

    var currentBlock:int := 0;
    while currentBlock < num_blocks
        invariant 0 <= currentBlock <= num_blocks;
        invariant M[..] == old(M[..]);
        invariant BEWordSeqToBitSeq(M[..words]) == PadMessageForSHA(messageBits);
        invariant IsSHA256ReadyForBlock(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock);
    {
        atoh, z := PerformOneBlockOfSHA256Computation(M, words, H, W, atoh, num_blocks, z, currentBlock);
        currentBlock := currentBlock + 1;
    }

    //- The final value of H is the desired hash.

    hash := H;

    //- The following is a proof that the hash is correct.

    Lemma_ComputeSHA256AfterPadding(M, words, messageBits, z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), hash[..]);
}


static method{:dafnycc_conservative_seq_triggers} ComputeSHA256AfterPadding_arrays_optimized(M:array<int>, words:int, ghost messageBits:seq<int>) returns (hash:array<int>)
    requires M != null;
    requires 0 <= words <= M.Length;
    requires Mod16(words) == 0;
    requires forall i :: 0 <= i < words ==> Word32(M[i]);
    requires IsBitSeq(messageBits);
    requires |messageBits| < power2(64);
    requires BEWordSeqToBitSeq(M[..words]) == PadMessageForSHA(messageBits);
    ensures hash!=null;
    ensures IsSHA256(messageBits, hash[..]);
{
    //- Initialize arrays for use in computing SHA.

    var H := new int[8];
    var W := new int[64];

    //- Initialize state to get ready for first block.

    ghost var atoh:atoh_Type;
    var local_a, local_b, local_c, local_d, local_e, local_f, local_g, local_h;
    var num_blocks:int;
    ghost var z:SHA256Trace;
    local_a, local_b, local_c, local_d, local_e, local_f, local_g, local_h, atoh, num_blocks, z := InitializeVars_SHA256(M, words, H, W);

    //- Loop through the blocks one at a time.

    var currentBlock:int := 0;
    while currentBlock < num_blocks
        invariant 0 <= currentBlock <= num_blocks;
        invariant M[..] == old(M[..]);
        invariant BEWordSeqToBitSeq(M[..words]) == PadMessageForSHA(messageBits);
        invariant IsSHA256ReadyForBlock(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock);
    {
        atoh, z := PerformOneBlockOfSHA256Computation_optimized(M, words, H, W, atoh, num_blocks, z, currentBlock);
        currentBlock := currentBlock + 1;
    }

    //- The final value of H is the desired hash.

    hash := H;

    //- The following is a proof that the hash is correct.

    Lemma_ComputeSHA256AfterPadding(M, words, messageBits, z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), hash[..]);
}

static method{:dafnycc_conservative_seq_triggers} ComputeSHA256AfterPadding_original(M:array<int>, words:int, ghost messageBits:seq<int>) returns (hash:seq<int>)
    requires M != null;
    requires 0 <= words <= M.Length;
    requires Mod16(words) == 0;
    requires forall i :: 0 <= i < words ==> Word32(M[i]);
    requires IsBitSeq(messageBits);
    requires |messageBits| < power2(64);
    requires BEWordSeqToBitSeq(M[..words]) == PadMessageForSHA(messageBits);
    ensures IsSHA256(messageBits, hash);
{
    var H := ComputeSHA256AfterPadding_arrays_original(M, words, messageBits);
    hash := H[..];
}

static method{:dafnycc_conservative_seq_triggers} ComputeSHA256AfterPadding_optimized(M:array<int>, words:int, ghost messageBits:seq<int>) returns (hash:seq<int>)
    requires M != null;
    requires 0 <= words <= M.Length;
    requires Mod16(words) == 0;
    requires forall i :: 0 <= i < words ==> Word32(M[i]);
    requires IsBitSeq(messageBits);
    requires |messageBits| < power2(64);
    requires BEWordSeqToBitSeq(M[..words]) == PadMessageForSHA(messageBits);
    ensures IsSHA256(messageBits, hash);
{
    var H := ComputeSHA256AfterPadding_arrays_optimized(M, words, messageBits);
    hash := H[..];
}

static method {:timeLimitMultiplier 5} {:dafnycc_conservative_seq_triggers} SHA256_impl_ArrayInPlace(M:array<int>, bits:int) returns (hash:seq<int>)
    requires IsWordArray(M);
    requires Word32(bits);
    requires 0 <= bits < power2(64);
    requires 0 <= PaddedLength(bits) <= M.Length * 32;
    ensures bits <= M.Length * 32;
    ensures IsWordSeqOfLen(hash, 8);
    ensures IsSHA256(old(BEWordSeqToBitSeq_premium(M[..])[..bits]), hash);
    ensures hash == SHA256(old(BEWordSeqToBitSeq_premium(M[..])[..bits]));
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

    hash := ComputeSHA256AfterPadding_optimized(M, words, messageBits);
    lemma_SHA256IsAFunction(old(BEWordSeqToBitSeq_premium(M[..])[..bits]), hash);
}


static method SHA256_impl_Bytes(messageBytes:seq<int>) returns (hash:seq<int>)
    requires Word32(|messageBytes|*8);
    requires |messageBytes|*8 < power2(64);
    requires IsByteSeq(messageBytes);
    ensures IsWordSeqOfLen(hash, 8);
    ensures IsSHA256(BEByteSeqToBitSeq_premium(messageBytes), hash);
    ensures hash == SHA256(BEByteSeqToBitSeq_premium(messageBytes));
{
    var M, bits := CreateArrayForSHA(messageBytes);
    hash := SHA256_impl_ArrayInPlace(M, bits);
    lemma_SHA256IsAFunction(BEByteSeqToBitSeq_premium(messageBytes), hash);
}

static method SHA256_impl_Bytes_arrays_original(messageBytes:array<int>) returns (hash:array<int>)
    requires messageBytes != null;
    requires Word32(messageBytes.Length*8);
    requires messageBytes.Length*8 < power2(64);
    requires IsByteSeq(messageBytes[..]);
    ensures hash != null;
    ensures IsWordSeqOfLen(hash[..], 8);
    ensures IsSHA256(BEByteSeqToBitSeq_premium(messageBytes[..]), hash[..]);
    ensures hash[..] == SHA256(BEByteSeqToBitSeq_premium(messageBytes[..]));
    ensures messageBytes[..] == old(messageBytes[..]);
{
    var M, bits := CreateArrayForSHA_arrays(messageBytes);
    ghost var Minput_seq := M[..];
    assert BEByteSeqToBitSeq_premium(messageBytes[..]) == BEWordSeqToBitSeq(Minput_seq)[..bits];

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

    hash := ComputeSHA256AfterPadding_arrays_original(M, words, messageBits);
    ghost var hash_seq := hash[..];
    ghost var messageBytes_seq := old(messageBytes)[..];
    assert IsSHA256(messageBits, hash_seq);
    lemma_SHA_impl_Bytes_arrays_bitmangle(old(messageBytes), messageBytes_seq, messageBits, Minput_seq, bits);
    assert IsSHA256(BEByteSeqToBitSeq_premium(messageBytes_seq), hash_seq);
    lemma_SHA256IsAFunction(BEByteSeqToBitSeq_premium(messageBytes_seq), hash_seq);
}


static method SHA256_impl_Words_arrays_original(messageWords:array<int>) returns (hash:array<int>)
    requires messageWords != null;
    requires Word32(messageWords.Length*32);
    requires messageWords.Length*32 < power2(64);
    requires IsWordSeq(messageWords[..]);
    ensures hash != null;
    ensures IsWordSeqOfLen(hash[..], 8);
    ensures IsSHA256(BEWordSeqToBitSeq_premium(messageWords[..]), hash[..]);
    ensures hash[..] == SHA256(BEWordSeqToBitSeq_premium(messageWords[..]));
    ensures messageWords[..] == old(messageWords[..]);
{
    var M, bits := CreateArrayForSHA_arrays_words(messageWords);
    ghost var Minput_seq := M[..];
    assert BEWordSeqToBitSeq_premium(messageWords[..]) == BEWordSeqToBitSeq(Minput_seq)[..bits];

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

    hash := ComputeSHA256AfterPadding_arrays_original(M, words, messageBits);
    ghost var hash_seq := hash[..];
    ghost var messageWords_seq := old(messageWords)[..];
    assert IsSHA256(messageBits, hash_seq);
    lemma_SHA_impl_Words_arrays_bitmangle(old(messageWords), messageWords_seq, messageBits, Minput_seq, bits);
    assert IsSHA256(BEWordSeqToBitSeq_premium(messageWords_seq), hash_seq);
    lemma_SHA256IsAFunction(BEWordSeqToBitSeq_premium(messageWords_seq), hash_seq);
}


static method SHA256_impl_Bytes_arrays(messageBytes:array<int>) returns (hash:array<int>)
    requires messageBytes != null;
    requires Word32(messageBytes.Length*8);
    requires messageBytes.Length*8 < power2(64);
    requires IsByteSeq(messageBytes[..]);
    ensures hash != null;
    ensures IsWordSeqOfLen(hash[..], 8);
    ensures IsSHA256(BEByteSeqToBitSeq_premium(messageBytes[..]), hash[..]);
    ensures hash[..] == SHA256(BEByteSeqToBitSeq_premium(messageBytes[..]));
    ensures messageBytes[..] == old(messageBytes[..]);
{
    var M, bits := CreateArrayForSHA_arrays(messageBytes);
    ghost var Minput_seq := M[..];
    assert BEByteSeqToBitSeq_premium(messageBytes[..]) == BEWordSeqToBitSeq(Minput_seq)[..bits];

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

    hash := ComputeSHA256AfterPadding_arrays_optimized(M, words, messageBits);
    ghost var hash_seq := hash[..];
    ghost var messageBytes_seq := old(messageBytes)[..];
    assert IsSHA256(messageBits, hash_seq);
    lemma_SHA_impl_Bytes_arrays_bitmangle(old(messageBytes), messageBytes_seq, messageBits, Minput_seq, bits);
    assert IsSHA256(BEByteSeqToBitSeq_premium(messageBytes_seq), hash_seq);
    lemma_SHA256IsAFunction(BEByteSeqToBitSeq_premium(messageBytes_seq), hash_seq);
}


static method SHA256_impl_Words_arrays(messageWords:array<int>) returns (hash:array<int>)
    requires messageWords != null;
    requires Word32(messageWords.Length*32);
    requires messageWords.Length*32 < power2(64);
    requires IsWordSeq(messageWords[..]);
    ensures hash != null;
    ensures IsWordSeqOfLen(hash[..], 8);
    ensures IsSHA256(BEWordSeqToBitSeq_premium(messageWords[..]), hash[..]);
    ensures hash[..] == SHA256(BEWordSeqToBitSeq_premium(messageWords[..]));
    ensures messageWords[..] == old(messageWords[..]);
{
    var M, bits := CreateArrayForSHA_arrays_words(messageWords);
    ghost var Minput_seq := M[..];
    assert BEWordSeqToBitSeq_premium(messageWords[..]) == BEWordSeqToBitSeq(Minput_seq)[..bits];

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

    hash := ComputeSHA256AfterPadding_arrays_optimized(M, words, messageBits);
    ghost var hash_seq := hash[..];
    ghost var messageWords_seq := old(messageWords)[..];
    assert IsSHA256(messageBits, hash_seq);
    lemma_SHA_impl_Words_arrays_bitmangle(old(messageWords), messageWords_seq, messageBits, Minput_seq, bits);
    assert IsSHA256(BEWordSeqToBitSeq_premium(messageWords_seq), hash_seq);
    lemma_SHA256IsAFunction(BEWordSeqToBitSeq_premium(messageWords_seq), hash_seq);
}
