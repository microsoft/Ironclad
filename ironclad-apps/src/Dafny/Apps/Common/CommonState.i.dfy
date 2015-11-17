include "CommonState.s.dfy"
include "../../Drivers/TPM/tpm-wrapper.i.dfy"
include "../../Libraries/Util/Halter.i.dfy"
include "../../Libraries/Util/DebugPrint.i.dfy"

include "../../Libraries/Crypto/RSA/rfc4251impl.i.dfy"
include "../../Libraries/Crypto/RSA/RSAPublicWrapper.i.dfy"

datatype CommonStateImpl = CommonStateImplConstructor(sk:TPMSessionAndKey, key_pair:RSAKeyPairImpl, key_bits:nat)

function {:autoReq} CommonStateImplToSpec (s:CommonStateImpl) : CommonState
{
    CommonStateConstructor(KeyPairImplToSpec(s.key_pair), s.key_bits)
}

static lemma AModestKeyCanBeEncodedWithRFC4251(key_pair:RSAKeyPairSpec)
    requires key_pair.pub.e < power2(power2(31));
    requires key_pair.pub.n < power2(power2(31));
    ensures key_pair.pub.e < power2(power2(34));
    ensures key_pair.pub.n < power2(power2(34));
    ensures IsWordSeq([|STR_SSH_RSA()|]);
    ensures IsWordSeq([|rfc4251_positive_to_twoscomplement(BEIntToByteSeq(key_pair.pub.e))|]);
    ensures IsWordSeq([|rfc4251_positive_to_twoscomplement(BEIntToByteSeq(key_pair.pub.n))|]);
    ensures IsByteSeq(rfc4251_sshrsa_encoding(key_pair.pub.e,key_pair.pub.n));
{
    reveal_power2();
    lemma_power2_increases(31, 34);
    lemma_power2_increases(power2(31), power2(34));
    lemma_rfc4251_sshrsa_encoding_premium(key_pair.pub.e, key_pair.pub.n);
}

static predicate KeyCanBeEncodedWithRFC4251(key_pair:RSAKeyPairSpec)
    requires key_pair.pub.e < power2(power2(31));
    requires key_pair.pub.n < power2(power2(31));
    ensures key_pair.pub.e < power2(power2(34));
    ensures key_pair.pub.n < power2(power2(34));
    ensures IsWordSeq([|STR_SSH_RSA()|]);
    ensures IsWordSeq([|rfc4251_positive_to_twoscomplement(BEIntToByteSeq(key_pair.pub.e))|]);
    ensures IsWordSeq([|rfc4251_positive_to_twoscomplement(BEIntToByteSeq(key_pair.pub.n))|]);
    ensures IsByteSeq(rfc4251_sshrsa_encoding(key_pair.pub.e,key_pair.pub.n));
{
    AModestKeyCanBeEncodedWithRFC4251(key_pair);
    true
}

predicate CommonStateImplValid (s:CommonStateImpl)
{
    TPMSessionAndKeyValid(s.sk)
    && WellformedRSAKeyPairImpl(s.key_pair)
    && ModestKeyValue(s.key_pair.pub.e)
    && ModestKeyValue(s.key_pair.pub.n)
    && KeyCanBeEncodedWithRFC4251(KeyPairImplToSpec(s.key_pair))
}

method ExtendPCRRepeatedly (s:seq<seq<int>>) returns (success:bool)
    requires forall i :: 0 <= i < |s| ==> IsByteSeqOfLen(s[i], 20);

    requires TPM_ready();

    ensures success ==> TPM.PCR_19 == old(TPM.PCR_19) + s;
    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM)[PCR_19 := TPM.PCR_19]);
    modifies this`TPM;
    modifies this`IoMemPerm;
{
    success := true;

    ghost var old_PCR_19 := TPM.PCR_19;
    var i:int := 0;
    while i < |s|
        invariant 0 <= i <= |s|;
        invariant TPM_ready();
        invariant TPMs_match(TPM, old(TPM)[PCR_19 := old_PCR_19 + s[..i]]);
    {
        success := extend_PCR(s[i]);
        if !success {
            return;
        }
        i := i + 1;
    }
}

method GenerateKeyPair (key_bits:nat) returns (success:bool, key_pair:RSAKeyPairImpl)
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;

    ensures success ==> WellformedRSAKeyPairImpl(key_pair)
                        && RSAKeyGenerationValid(key_bits, KeyPairImplToSpec(key_pair), TPM_random_bytes(old(TPM).random_index, TPM.random_index))
                        && key_pair.pub.size >= key_bits / 8
                        && ModestKeyValue(key_pair.pub.e)
                        && ModestKeyValue(key_pair.pub.n);

    ensures TPM_ready();
    ensures TPMs_match_except_for_randoms(TPM, old(TPM));
{
    success := false;

    if (key_bits <= 20 || key_bits >= 0x10000000) {
        key_pair := GenDummyKey(); //- dafnycc: initialize variable
        return;
    }
    calc {
        key_bits;
        < 0x10000000;
        == { lemma_2toX(); lemma_power2_add8(24); }
        power2(28);
    }

    key_pair := RSAKeyGen(key_bits);
    var modest_e := IsModestKeyValue(key_pair.pub.e);
    var modest_n := IsModestKeyValue(key_pair.pub.n);

    if !modest_e || !modest_n {
        return;
    }

    success := true;
}

static predicate KeyCanBeExtendedIntoPCR(key_pair:RSAKeyPairSpec)
{
    key_pair.pub.e < power2(power2(31)) &&
    key_pair.pub.n < power2(power2(31)) &&
    KeyCanBeEncodedWithRFC4251(key_pair) &&
    var public_key_encoding := rfc4251_sshrsa_encoding(key_pair.pub.e, key_pair.pub.n);
    IsByteSeq(public_key_encoding) &&
    var public_key_encoding_bits := BEByteSeqToBitSeq(public_key_encoding);
    IsBitSeq(public_key_encoding_bits) &&
    |public_key_encoding_bits| < power2(64)
}

method ExtendCommonStateKeyIntoPCR19 (key_bits:nat, state:CommonStateImpl, ghost TPM_before_keygen:TPM_struct)
    requires TPM_ready();
    requires CommonStateImplValid(state);
    requires WellformedRSAKeyPairImpl(state.key_pair);
    requires state.key_bits == key_bits;
    requires RSAKeyGenerationValid(key_bits, KeyPairImplToSpec(state.key_pair),
                                   TPM_random_bytes(TPM_before_keygen.random_index, TPM.random_index));
    requires state.key_pair.pub.size >= key_bits / 8;
    requires ModestKeyValue(state.key_pair.pub.e);
    requires ModestKeyValue(state.key_pair.pub.n);
    requires TPMs_match(TPM, TPM_before_keygen[random_index := TPM.random_index]);

    ensures KeyCanBeExtendedIntoPCR(CommonStateImplToSpec(state).key_pair);
    ensures TPM_ready();
    ensures CommonStateGeneratedCorrectly(key_bits, CommonStateImplToSpec(state), TPM_before_keygen, TPM);
    ensures TPMs_match(TPM, TPM_before_keygen[random_index := TPM.random_index][PCR_19 := TPM.PCR_19]);

    modifies this`TPM;
    modifies this`IoMemPerm;
{
    var encoded_public_key := rfc4251_encode_sshrsa_pubkey(state.key_pair.pub);
    if |encoded_public_key| >= 0x20000000 {
        HaltMachine(0x31);
    }

    debug_print(0x90, 0x89280003);

    calc {
        |encoded_public_key|*8;
        < 0x20000000 * 8;
        == 0x100000000;
        == { lemma_2toX32(); } power2(32);
    }
    lemma_power2_strictly_increases(32, 64);

    var public_key_hash_words := SHA1_impl_Bytes(encoded_public_key);
    var public_key_hash_bytes := BEWordSeqToByteSeq_impl(public_key_hash_words);

    var success := extend_PCR(public_key_hash_bytes);
    if !success {
        HaltMachine(0x32);
    }
}

method GenerateCommonState (key_bits:nat) returns (state:CommonStateImpl)
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM_satisfies_integrity_policy(TPM);

    ensures TPM_ready() &&
            CommonStateImplValid(state) &&
            KeyCanBeExtendedIntoPCR(CommonStateImplToSpec(state).key_pair) &&
            CommonStateGeneratedCorrectly(key_bits, CommonStateImplToSpec(state), old(TPM), TPM);
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPMs_match_except_for_randoms(TPM, old(TPM)[PCR_19 := TPM.PCR_19]);
    ensures TPM_valid(TPM);
    ensures IoMemPerm.Null?;
{
    ghost var old_TPM := TPM;

    establish_locality();

    debug_print(0x90, 0x89280000);

    var success, sk := establish_TPM_session_and_key();
    if !success {
        HaltMachine(0x2F);
    }

    debug_print(0x90, 0x89280001);

//- swap comments to enable baked key
    var key_pair;
    success, key_pair := GenerateKeyPair(key_bits);
//-    key_pair := GetBakedKey(key_bits);
//-    success := true;

    debug_print(0x90, 0x89280002);

    if !success {
        HaltMachine(0x30);
    }

    assert WellformedRSAKeyPairImpl(key_pair);
    assert RSAKeyGenerationValid(key_bits, KeyPairImplToSpec(key_pair), TPM_random_bytes(old_TPM.random_index, TPM.random_index));

    state := CommonStateImplConstructor(sk, key_pair, key_bits);

    ExtendCommonStateKeyIntoPCR19(key_bits, state, old_TPM);
}

method HandleGetQuoteRequest (common_state_in:CommonStateImpl, nonce_external:seq<int>)
                              returns (common_state_out:CommonStateImpl, encoded_public_key:seq<int>, pcr_info_bytes:seq<int>,
                                       sig_bytes:seq<int>)
    requires IsByteSeqOfLen(nonce_external, 20);
    requires CommonStateImplValid(common_state_in);
    ensures HandleGetQuoteRequestValid(CommonStateImplToSpec(common_state_in), old(TPM), TPM, nonce_external,
                                       encoded_public_key, pcr_info_bytes, sig_bytes);

    requires TPM_ready();

    modifies this`TPM;
    modifies this`IoMemPerm;

    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM));

    ensures CommonStateImplValid(common_state_out);
    ensures common_state_out == common_state_in[sk := common_state_out.sk];
    ensures IsByteSeq(encoded_public_key);
    ensures IsByteSeq(pcr_info_bytes);
    ensures IsByteSeq(sig_bytes);
    ensures Word32(|encoded_public_key|);
    ensures Word32(|pcr_info_bytes|);
    ensures Word32(|sig_bytes|);
{
    ghost var old_TPM := TPM;

    lemma_2toX();
    reveal_power2();

    encoded_public_key := rfc4251_encode_sshrsa_pubkey(common_state_in.key_pair.pub);
    var success:bool;
    var new_sk:TPMSessionAndKey;
    success, new_sk, pcr_info_bytes, sig_bytes := quote(common_state_in.sk, nonce_external);
    if !success {
        HaltMachine(0x51);
    }
    if |encoded_public_key| > 0xFFFFFFFF {
        HaltMachine(0x52);
    }
    if |pcr_info_bytes| > 0xFFFFFFFF {
        HaltMachine(0x53);
    }
    if |sig_bytes| > 0xFFFFFFFF {
        HaltMachine(0x54);
    }
    common_state_out := common_state_in[sk := new_sk];
    assert 0xFFFFFFFF < power2(32);
}
