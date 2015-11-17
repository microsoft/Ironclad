//-<NuBuild BasmEnableSymdiff true />
include "rfc4251impl.i.dfy"
include "KeybitsLength.i.dfy"
include "../../FatNat/FatNatDiv.i.dfy"
include "../../FatNat/FatNatReciprocal.i.dfy"

lemma lemma_1_is_small_enough(N:array<int>)
    requires WellformedFatNat(N);
    requires J(N) == 1;
    ensures J(N) < power2(power2(29));
{
    lemma_2toX32();
    calc {
        J(N);
        1;
        <
        power2(2);
        power2(power2(1));
        <= {
            lemma_power2_increases(1, 29);
            lemma_power2_increases(power2(1), power2(29)); }
        power2(power2(29));
    }
}

lemma lemma_prep_dummy_key(N:array<int>, k:nat)
    requires WellformedFatNat(N);
    requires J(N)==1;
    requires k==1;
//-    ensures 1 < Frump();
    ensures KeyModulusMatchesSizeInBytes(J(N), k);
{
    lemma_2toX32();
    calc {
        J(N);
        <
        16;
        power2(4);
        <= { lemma_power2_increases(4, power2(30)); }
        power2(power2(30));
    }
//-    assert FrumpyBigNat(N);
    ghost var n := 1;
    assert n == J(N);
    calc {
        power2(8*(k-1));
        power2(8*0);
        power2(0);
        1;
        <=
        n;
    }
    calc {
        n;
        <=
        256;
        power2(8);
        power2(8*1);
        power2(8*k);
    }
    assert power2(8*(k-1)) <= n;
    assert n < power2(8*k);
    
    assert KeyModulusMatchesSizeInBytes(J(N), k);
}

method {:timeLimitMultiplier 3} make_dummy_key() returns (pubkey:RSAPubKeyImpl_internal)
    ensures WellformedRSAPubKeyImpl_internal(pubkey);
    ensures public(pubkey.size);
    ensures public(J(pubkey.n));
    ensures public(J(pubkey.e));
{
    lemma_2toX32();
    var N := MakeBELiteralArray(1);
    assert WellformedFatNat(N);

    var E := MakeBELiteralArray(1);
    lemma_prep_dummy_key(N, 1);

//-    assert FrumpyBigNat(E);

    pubkey := RSAPubKeyImpl_c_internal(N, 1, E, FNDivUnknownReciprocal()); //- dafnycc
    assert N == pubkey.n;   //- OBSERVE

    assert KeyModulusMatchesSizeInBytes(J(pubkey.n), pubkey.size);
    lemma_1_is_small_enough(N);
    assert WellformedFatNat(N);
    assert J(N) < power2(power2(29));

//-    lemma_keybits_implies_length25(N);

    lemma_power2_increases(29, 30);
    lemma_power2_increases(power2(25), power2(30));

    assert N == pubkey.n;
//-    assert WellformedFatNat(N);
    assert WellformedRSAPubKeyImpl_internal(pubkey);
}

method rfc4251_decode_sshrsa_internal(msg:seq<int>) returns (success:bool, pubkey:RSAPubKeyImpl_internal)
    requires IsByteSeq(msg);
    requires Word32(|msg|);
    requires public(msg);
    ensures WellformedRSAPubKeyImpl_internal(pubkey);
    ensures success ==> PubKeyImplToSpec_internal(pubkey).e < power2(power2(34));
    ensures success ==> PubKeyImplToSpec_internal(pubkey).n < power2(power2(34));
    ensures success ==> (msg == rfc4251_sshrsa_pubkey_encoding_premium(PubKeyImplToSpec_internal(pubkey)));
    ensures public(success);
    ensures public(pubkey.size);
    ensures public(J(pubkey.n));
    ensures public(J(pubkey.e));
    
    
    
{
    success := false;

    var sub_rc,E,N := rfc4251_decode_sshrsa_inner(msg);
    if (!sub_rc)
    {
        pubkey := make_dummy_key();
        return;
    }

//-    lemma_frumpy_is_modest(N);
//-    lemma_modesty_word_value_equivalence(N);
    var size_bits := FatNatCountBits(N);
    var size_bytes := (size_bits+7)/8;

    lemma_power2_increases(8*(size_bytes-1), size_bits-1);
    lemma_power2_increases(size_bits, 8*size_bytes);
    //-assert power2(8*(size_bytes-1)) <= J(N);
    //-assert J(N) < power2(8*size_bytes);

    var nReciprocal := FatNatComputeReciprocal(N);
    var nReciprocal_ref := nReciprocal.TwoTo32wDividedByD; //- reference this array for DafnyCC's sake
    pubkey := RSAPubKeyImpl_c_internal(N, size_bytes, E, nReciprocal);
//-    lemma_keybits_implies_length25(N);
    //-assert J(E) < power2(power2(30));
    //-assert J(N) < power2(power2(30));
    //-assert WellformedRSAPubKeyImpl_internal(pubkey);
//-    calc {
//-        PubKeyImplToSpec_internal(pubkey).e;
//-        J(E);
//-        <
//-        power2(power2(34));
//-    }
    success := true;
}
