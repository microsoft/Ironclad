//- HAND-OPTIMIZED PIECES of SHA 256

include "sha256.s.dfy"
include "../../Util/seq_blocking.i.dfy"
include "../../Util/arrays_and_seqs.i.dfy"
include "../../Util/integer_sequences_premium.i.dfy"
include "sha_padding.i.dfy"
include "sha_common.i.dfy"
include "sha256common.i.dfy"
include "../../../Drivers/CPU/assembly_premium.i.dfy"


static method InitK_SHA256(Ks: array<int>)
    requires Ks != null && Ks.Length ==  64;
    ensures forall i :: 0 <= i < Ks.Length ==> Ks[i] == K_SHA256(i);
    modifies Ks;
{
    InitK_SHA256_0_to_10(Ks);
}

static method {:decl} InitK_SHA256_0_to_10(Ks: array<int>)
    requires Ks != null && Ks.Length == 64;
    modifies Ks;
    ensures forall i :: 0 <= i < 64 ==> Ks[i] == K_SHA256(i);


static method {:decl} ComputeWsForBlockStep2_SHA256(M:array<int>, words:int, H:array<int>, W:array<int>,
                                                    ghost atoh:atoh_Type, num_blocks:int, ghost z:SHA256Trace, currentBlock:int)
    requires H != null;
    requires W != null && W.Length == 64;
    requires M != null;
    requires 0 <= words <= M.Length;
    requires 0 <= currentBlock < |z.M|;
    requires IsSHA256ReadyForBlock(z, SHA256_vars_to_state(M, words, H, W, atoh, num_blocks), currentBlock);
    requires forall t :: 0 <= t < 16 ==> Word32(W[t]);
    requires forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < 16 ==> W[t] == z.M[currentBlock][t];
    requires W != H && W != M;
    modifies W;
    ensures H[..] == old(H[..]);
    ensures M[..] == old(M[..]);
    ensures forall t :: 0 <= t <= 63 ==> Word32(W[t]);
    ensures forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < 16 ==> W[t] == z.M[currentBlock][t];
    ensures forall t {:trigger TStep(t)} :: TStep(t) && 16 <= t <= 63 ==> W[t] == Asm_Add(Asm_Add(Asm_Add(SSIG1(W[t-2]), W[t-7]), SSIG0(W[t-15])), W[t-16]);
//-{
//-    var t := 16;
//-    while t < 64
//-        invariant 16 <= t <= 64;
//-        invariant forall step :: 0 <= step < t ==> Word32(W[step]);
//-        invariant forall step {:trigger TStep(step)} :: TStep(step) && 0 <= step < 16 ==> W[step] == z.M[currentBlock][step];
//-        invariant forall step {:trigger TStep(step)} :: TStep(step) && 16 <= step < t ==>
//-            W[step] == Asm_Add(Asm_Add(Asm_Add(SSIG1(W[step-2]), W[step-7]), SSIG0(W[step-15])), W[step-16]);
//-    {
//-        W[t] := Asm_Add(Asm_Add(Asm_Add(SSIG1_impl(W[t-2]), W[t-7]), SSIG0_impl(W[t-15])), W[t-16]);
//-        t := t + 1;
//-    }
//-}
