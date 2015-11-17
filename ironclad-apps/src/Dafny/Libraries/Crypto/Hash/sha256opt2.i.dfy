//- OPTIMIZED VERSION
 
include "sha256.s.dfy"
include "../../Util/seq_blocking.i.dfy"
include "../../Util/arrays_and_seqs.i.dfy"
include "../../Util/integer_sequences_premium.i.dfy"
include "sha_padding.i.dfy"
include "sha_common.i.dfy"
include "sha256opt.i.dfy"
include "sha256common.i.dfy"
include "../../../Drivers/CPU/assembly_premium.i.dfy"

/*
static method{:dafnycc_conservative_seq_triggers} ComputeOneStep_SHA256_optimized(M:array<int>, words:int, H:array<int>, W:array<int>, ghost atoh:atoh_Type, num_blocks:int, a:int, b:int, c:int, d:int, e:int, f:int, g:int, h:int,
                                    ghost z:SHA256Trace, currentBlock:int, currentStep:int, K:int)
                                    returns (a_next:int, b_next:int, c_next:int, d_next:int, e_next:int, f_next:int, g_next:int, h_next:int, ghost next_atoh:atoh_Type, ghost next_z:SHA256Trace)
    requires H != null;
    requires W != null;
    requires M != null;
    requires atoh == atoh_c(a, b, c, d, e, f, g, h);
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires 0 <= currentStep <= 63;
    requires K == K_SHA256(currentStep); 
    requires IsSHA256ReadyForStep(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock, currentStep);
    ensures IsSHA256ReadyForStep(next_z, SHA256_vars_to_state(M, words, H, W, next_atoh, num_blocks), currentBlock, currentStep+1);

    ensures H[..] == old(H[..]);
    ensures M[..] == old(M[..]);
    ensures W[..] == old(W[..]);
    ensures next_atoh == atoh_c(a_next, b_next, c_next, d_next, e_next, f_next, g_next, h_next);
*/
/*
{
    assert TBlk(currentBlock) && TBlk(currentBlock + 1) && TStep(currentStep) && TStep(currentStep + 1);
    ghost var s := SHA256_vars_to_state(M, words, H, W, Ks, atoh, num_blocks);

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

    var T1 := Asm_Add(Asm_Add(Asm_Add(Asm_Add(h, bsig1), my_ch), Ks[currentStep]), W[currentStep]);
    var T2 := Asm_Add(bsig0, my_maj);
    a_next, b_next, c_next, d_next, e_next, f_next, g_next, h_next := Asm_Add(T1, T2), a, b, c, Asm_Add(d, T1), e, f, g;
    next_atoh := atoh_c(Asm_Add(T1, T2), atoh.a, atoh.b, atoh.c, Asm_Add(atoh.d, T1), atoh.e, atoh.f, atoh.g);
    next_z := SHA256Trace_c(z.M, z.H, z.W, z.atoh[..currentBlock] + [z.atoh[currentBlock] + [next_atoh]]);
    ghost var next_s := SHA256_vars_to_state(M, words, H, W, Ks, next_atoh, num_blocks);

    lemma_SHA256TransitionOKAfterSettingAtoH(z, s, next_z, next_s, currentBlock, currentStep);
}
*/

static method{:dafnycc_conservative_seq_triggers}{:decl} ComputeSHA256_optimized_loop(M:array<int>, words:int, H:array<int>, W:array<int>, ghost atoh:atoh_Type, num_blocks:int, 
                                                                               a:int, b:int, c:int, d:int, e:int, f:int, g:int, h:int,
                                                                               ghost z:SHA256Trace, currentBlock:int)
                                    returns (a_final:int, b_final:int, c_final:int, d_final:int, e_final:int, f_final:int, g_final:int, h_final:int, ghost final_atoh:atoh_Type, ghost final_z:SHA256Trace)
    requires H != null && H.Length == 8;
    requires W != null && W.Length == 64;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    //-requires IsSHA256ReadyForBlock(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock);
    requires IsSHA256ReadyForStep(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock, 0);
    requires W != H && W != M && H != M;
    requires atoh == atoh_c(a, b, c, d, e, f, g, h);
    ensures M[..] == old(M[..]);
    ensures H[..] == old(H[..]);
    ensures W[..] == old(W[..]);
    ensures IsSHA256ReadyForStep(final_z, SHA256_vars_to_state(M, words, H, W, final_atoh, num_blocks), currentBlock, 64);
    //-ensures IsSHA256ReadyForBlock(next_z, SHA256_vars_to_state(M, words, H, W, next_atoh, num_blocks), currentBlock+1);
    ensures final_atoh == atoh_c(a_final, b_final, c_final, d_final, e_final, f_final, g_final, h_final);


static method {:decl} ComputeWsForBlockStep1_SHA256_optimized(M:array<int>, words:int, H:array<int>, W:array<int>,
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
//-{
//-    ghost var s := SHA256_vars_to_state(M, words, H, W, atoh, num_blocks);
//-
//-    var t:int := 0;
//-    var m_index := currentBlock * 16;
//-    while t < 16
//-        invariant 0 <= t <= 16;
//-        invariant m_index == currentBlock * 16 + t;
//-        invariant s.M == M[..words];
//-        invariant forall step :: 0 <= step < t ==> Word32(W[step]);
//-        invariant forall step {:trigger TStep(step)} :: TStep(step) && 0 <= step < t ==> W[step] == z.M[currentBlock][step];
//-    {
//-        reveal_Mul16();
//-        calc {
//-            0;
//-            <= { lemma_mul_nonnegative(currentBlock, 16); }
//-               currentBlock * 16;
//-            <= currentBlock * 16 + t;
//-        }
//-        calc {
//-            currentBlock * 16 + t;
//-            16 * currentBlock + t;
//-            16 * (currentBlock+1) - 16 + t;
//-            <= 16*|z.M| - 16 + t;
//-            < 16*|z.M|;
//-            == Mul16(|z.M|);
//-            == words;
//-        }
//-        W[t] := M[m_index];
//-        calc {
//-            W[t];
//-            { lemma_mul_is_mul_boogie(currentBlock, 16);
//-              Lemma_BlockedSequencePrefixContainsElement(M[..], words, 16, currentBlock, t); }
//-            BreakIntoBlocks(M[..words], 16)[currentBlock][t];
//-            BreakIntoBlocks(s.M, 16)[currentBlock][t];
//-            z.M[currentBlock][t];
//-        }
//-        t := t + 1;
//-        m_index := m_index + 1;
//-    }
//-}
