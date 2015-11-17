//-<NuBuild BasmEnableSymdiff true />
include "RSASpec.s.dfy"
include "KeyImpl.i.dfy"
include "RSA.i.dfy"
include "RSAOps.i.dfy"
include "RSADigestedSign.i.dfy"
include "RSA_Decrypt.i.dfy"
include "rfc4251impl.i.dfy"
include "rfc4251decode.i.dfy"
include "../../BigNum/BigNum.i.dfy"






datatype RSAPubKeyImpl = RSAPubKeyImpl_c(
    n:BigNat,    //- modulus
    size:nat,
    e:BigNat     //- public key exponent
    );

predicate WellformedRSAPubKeyImpl(pub:RSAPubKeyImpl)
{
    true
    && WellformedBigNat(pub.n)
    && WellformedBigNat(pub.e)
    && 0<I(pub.n)
    && KeyModulusMatchesSizeInBytes(I(pub.n), pub.size)
}

datatype RSAKeyPairImpl = RSAKeyPairImpl_c(
    pub:RSAPubKeyImpl,
    d:BigNat     //- private key exponent
    );

predicate WellformedRSAKeyPairImpl(p:RSAKeyPairImpl)
{
    WellformedRSAPubKeyImpl(p.pub)
    && WellformedBigNat(p.d)
}

function PubKeyImplToSpec(pubkey:RSAPubKeyImpl) : RSAPubKeySpec
    requires WellformedRSAPubKeyImpl(pubkey);
{
    RSAPublicKeySpec_c(I(pubkey.n), pubkey.size, I(pubkey.e))
}

function KeyPairImplToSpec(key:RSAKeyPairImpl) : RSAKeyPairSpec
    requires WellformedRSAKeyPairImpl(key);
{
    RSAKeyPairSpec_c(PubKeyImplToSpec(key.pub), I(key.d))
}

predicate ModestKeyValue(x:BigNat)
{
    ModestBigNatValue(x)
}

method IsModestKeyValue(x:BigNat) returns (rc:bool)
    requires WellformedBigNat(x);
    ensures ModestKeyValue(x)<==>rc;
{
    rc := IsModestBigNat(x);
}

//-////////////////////////////////////////////////////////////////////////////


method RSAPubKeyFromInternal(pi:RSAPubKeyImpl_internal) returns (pub:RSAPubKeyImpl)
    requires WellformedRSAPubKeyImpl_internal(pi);
    ensures WellformedRSAPubKeyImpl(pub);
    ensures pi.size == pub.size;
    ensures J(pi.n) == I(pub.n);
    ensures J(pi.e) == I(pub.e);
{
    var nref := pi.n; //- do something real to pi.n so dafnycc knows it's allocated
    var eref := pi.e; //- do something real to pi.e so dafnycc knows it's allocated
    var recip_ref := if pi.nReciprocal.FNDivKnownReciprocal? then pi.nReciprocal.TwoTo32wDividedByD else pi.n; //- do something real to reciprocal for dafnycc

    var fn := FatNatToBigNat(pi.n);
    var fe := FatNatToBigNat(pi.e);
    pub := RSAPubKeyImpl_c(fn, pi.size, fe);
}

method RSAKeyPairFromInternal(kpi:RSAKeyPairImpl_internal) returns (kp:RSAKeyPairImpl)
    requires WellformedRSAKeyPairImpl_internal(kpi);
    ensures WellformedRSAKeyPairImpl(kp);
    ensures kpi.pub.size == kp.pub.size;
    ensures J(kpi.pub.n) == I(kp.pub.n);
    ensures J(kpi.pub.e) == I(kp.pub.e);
    ensures J(kpi.d) == I(kp.d);
{
    var nref := kpi.pub.n; //- do something real to kpi.pub.n so dafnycc knows it's allocated
    var eref := kpi.pub.e; //- do something real to kpi.pub.e so dafnycc knows it's allocated
    var dref := kpi.d;     //- do something real to kpi.d so dafnycc knows it's allocated
    var recip_ref := if kpi.pub.nReciprocal.FNDivKnownReciprocal? then kpi.pub.nReciprocal.TwoTo32wDividedByD else kpi.pub.n; //- do something real to reciprocal for dafnycc

    var pub := RSAPubKeyFromInternal(kpi.pub);
    var fd := FatNatToBigNat(kpi.d);
    kp := RSAKeyPairImpl_c(pub, fd);
    assert I(kp.pub.n) == J(kpi.pub.n);     //- OBSERVE
}

method RSAInternalFromPubKey(pub:RSAPubKeyImpl) returns (pi:RSAPubKeyImpl_internal)
    requires WellformedRSAPubKeyImpl(pub);
    ensures WellformedRSAPubKeyImpl_internal(pi);
    ensures pi.size == pub.size;
    ensures J(pi.n) == I(pub.n);
    ensures J(pi.e) == I(pub.e);
    ensures PubKeyImplToSpec_internal(pi) == PubKeyImplToSpec(pub);
{
    var bn := BigNatToFatNat(pub.n);
    var be := BigNatToFatNat(pub.e);
    var nReciprocal := FatNatComputeReciprocal(bn);
    var nReciprocal_ref := nReciprocal.TwoTo32wDividedByD; //- reference this array for DafnyCC's sake
    pi := RSAPubKeyImpl_c_internal(bn, pub.size, be, nReciprocal);
}

method RSAInternalFromKeyPair(kp:RSAKeyPairImpl) returns (kpi:RSAKeyPairImpl_internal)
    requires WellformedRSAKeyPairImpl(kp);
    ensures WellformedRSAKeyPairImpl_internal(kpi);
    ensures kpi.pub.size == kp.pub.size;
    ensures J(kpi.pub.n) == I(kp.pub.n);
    ensures J(kpi.pub.e) == I(kp.pub.e);
    ensures J(kpi.d) == I(kp.d);
{
    var pi := RSAInternalFromPubKey(kp.pub);
    var nref := pi.n; //- do something real to pi.n so dafnycc knows it's allocated
    var eref := pi.e; //- do something real to pi.e so dafnycc knows it's allocated
    var recip_ref := if pi.nReciprocal.FNDivKnownReciprocal? then pi.nReciprocal.TwoTo32wDividedByD else pi.n; //- do something real to reciprocal for dafnycc

    var bd := BigNatToFatNat(kp.d);
    kpi := RSAKeyPairImpl_c_internal(pi, bd);
    assert J(pi.n) == I(kp.pub.n);
    assert J(pi.e) == I(kp.pub.e);
}

//-////////////////////////////////////////////////////////////////////////////

method GenDummyKey() returns (key_pair:RSAKeyPairImpl)
{
    var zilch := MakeSmallLiteralBigNat(0);
    key_pair := RSAKeyPairImpl_c(RSAPubKeyImpl_c(zilch, 0, zilch), zilch);
}

function KV(X:BigNat) : int
    requires WellformedBigNat(X);
{
    I(X)
}

method RSAKeyGen(keybits:nat) returns (key:RSAKeyPairImpl)
    requires 20<keybits;
    requires keybits<power2(28);

    requires TPM_ready();
    ensures TPM_ready();
    modifies this`TPM;   
    modifies this`IoMemPerm;
    ensures TPMs_match_except_for_randoms(old(TPM), TPM);
    ensures old(TPM).random_index <= TPM.random_index;

    //    ensures ValidKeyLength(key);    
    ensures WellformedRSAKeyPairImpl(key);
    ensures KV(key.pub.n) >= power2(keybits);
    ensures key.pub.size >= keybits / 8;
    ensures RSAKeyGenerationValid(keybits, KeyPairImplToSpec(key), TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index));
{
    var kpi := RSAKeyGen_internal(keybits);
    var nref := kpi.pub.n; //- do something real to kpi.pub.n so dafnycc knows it's allocated
    var eref := kpi.pub.e; //- do something real to kpi.pub.e so dafnycc knows it's allocated
    var dref := kpi.d;     //- do something real to kpi.d so dafnycc knows it's allocated
    var recip_ref := if kpi.pub.nReciprocal.FNDivKnownReciprocal? then kpi.pub.nReciprocal.TwoTo32wDividedByD else kpi.pub.n; //- do something real to reciprocal for dafnycc

    key := RSAKeyPairFromInternal(kpi);
    assert KeyPairImplToSpec(key)==KeyPairImplToSpec_internal(kpi);
    assert RSAKeyGenerationValid(keybits, KeyPairImplToSpec(key), TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index));
    calc {
        KV(key.pub.n);
        J(kpi.pub.n);
        >=
        power2(keybits);
    }
}

method rfc4251_encode_sshrsa_pubkey(pubkey:RSAPubKeyImpl) returns (msg:seq<int>)
    requires ModestKeyValue(pubkey.e);
    requires ModestKeyValue(pubkey.n);
    requires WellformedRSAPubKeyImpl(pubkey);
    ensures IsByteSeq(msg);
    ensures PubKeyImplToSpec(pubkey).e < power2(power2(34));
    ensures PubKeyImplToSpec(pubkey).n < power2(power2(34));
    ensures msg == rfc4251_sshrsa_pubkey_encoding_premium(PubKeyImplToSpec(pubkey));
{
    var kpi := RSAInternalFromPubKey(pubkey);
    var nref := kpi.n; //- do something real to kpi.n so dafnycc knows it's allocated
    var eref := kpi.e; //- do something real to kpi.e so dafnycc knows it's allocated
    var recip_ref := if kpi.nReciprocal.FNDivKnownReciprocal? then kpi.nReciprocal.TwoTo32wDividedByD else kpi.n; //- do something real to reciprocal for dafnycc

    msg := rfc4251_encode_sshrsa_pubkey_internal(kpi);
}

method rfc4251_decode_sshrsa(msg:seq<int>) returns (success:bool, pubkey:RSAPubKeyImpl)
    requires IsByteSeq(msg);
    requires Word32(|msg|);
    requires public(msg);
    ensures WellformedRSAPubKeyImpl(pubkey);
    ensures success ==> PubKeyImplToSpec(pubkey).e < power2(power2(34));
    ensures success ==> PubKeyImplToSpec(pubkey).n < power2(power2(34));
    ensures success ==> (msg == rfc4251_sshrsa_pubkey_encoding_premium(PubKeyImplToSpec(pubkey)));
    ensures public(success);
    ensures public(pubkey.size);
    ensures public(KV(pubkey.n));
    ensures public(KV(pubkey.e));
{
    var pi;
    success,pi := rfc4251_decode_sshrsa_internal(msg);
    var nref := pi.n; //- do something real to pi.n so dafnycc knows it's allocated
    var eref := pi.e; //- do something real to pi.e so dafnycc knows it's allocated
    var recip_ref := if pi.nReciprocal.FNDivKnownReciprocal? then pi.nReciprocal.TwoTo32wDividedByD else pi.n; //- do something real to reciprocal for dafnycc

    pubkey := RSAPubKeyFromInternal(pi);
    assert PubKeyImplToSpec(pubkey) == PubKeyImplToSpec_internal(pi);
}

method rfc4251_encode_mpint_legacy(V:BigNat) returns (msg:seq<int>)
    requires ModestBigNatValue(V);
    ensures KV(V) < power2(power2(34));
    ensures IsByteSeq(msg);
    ensures msg == rfc4251_mpint_encoding_premium(KV(V));
{
    var vfn := BigNatToFatNat(V);
    msg := rfc4251_encode_mpint(vfn);
}

method rfc4251_decode_mpint_legacy(msg:seq<int>) returns (success:bool,V:BigNat,bytes_consumed:int)
    requires IsByteSeq(msg);
    requires public(msg);
    ensures ModestKeyValue(V);
    ensures I(V) < power2(power2(34));
    ensures 0 <= bytes_consumed <= |msg|;
    ensures success ==> (msg[..bytes_consumed] == rfc4251_mpint_encoding_premium(KV(V)));
    ensures public(success);
    ensures public(I(V));
    ensures public(bytes_consumed);
{
    var vfn;
    success,vfn,bytes_consumed := rfc4251_decode_mpint(msg);
    V := FatNatToBigNat(vfn);
}

method Decrypt(key:RSAKeyPairImpl, ciphertext:seq<int>) returns (result:bool, plaintext:seq<int>)
    requires WellformedRSAKeyPairImpl(key);
    requires IsByteSeq(ciphertext);
    requires |ciphertext|>0;
//-    requires |ciphertext|%4==0;
        
        
        
        
        
    ensures WellformedRSAKeyPairSpec(KeyPairImplToSpec(key));
    ensures result ==> (IsByteSeq(plaintext) && RSADecryptionRelation(KeyPairImplToSpec(key), ciphertext, plaintext));
    ensures !result ==>
        forall any_plaintext :: !(IsByteSeq(any_plaintext) && RSADecryptionRelation(KeyPairImplToSpec(key), ciphertext, any_plaintext));
{
    var kpi := RSAInternalFromKeyPair(key);
    var nref := kpi.pub.n; //- do something real to kpi.pub.n so dafnycc knows it's allocated
    var eref := kpi.pub.e; //- do something real to kpi.pub.e so dafnycc knows it's allocated
    var dref := kpi.d;     //- do something real to kpi.d so dafnycc knows it's allocated
    var recip_ref := if kpi.pub.nReciprocal.FNDivKnownReciprocal? then kpi.pub.nReciprocal.TwoTo32wDividedByD else kpi.pub.n; //- do something real to reciprocal for dafnycc

    result,plaintext := Decrypt_internal(kpi, ciphertext);
}

method Encrypt(pubkey:RSAPubKeyImpl, plaintext:seq<int>) returns (ciphertext:seq<int>)
    requires IsByteSeq(plaintext);
    requires WellformedRSAPubKeyImpl(pubkey);
    requires |plaintext| <= pubkey.size - 11;
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_ready();
    ensures WellformedRSAPubKeySpec(PubKeyImplToSpec(pubkey));
    ensures IsByteSeq(ciphertext);
    ensures exists padding:seq<int> ::
        RSAEncryptionRequires(PubKeyImplToSpec(pubkey), plaintext, padding)
        && RSAEncryption(PubKeyImplToSpec(pubkey), plaintext, padding) == ciphertext;
{
    var pi := RSAInternalFromPubKey(pubkey);
    var nref := pi.n; //- do something real to pi.n so dafnycc knows it's allocated
    var eref := pi.e; //- do something real to pi.e so dafnycc knows it's allocated
    var recip_ref := if pi.nReciprocal.FNDivKnownReciprocal? then pi.nReciprocal.TwoTo32wDividedByD else pi.n; //- do something real to reciprocal for dafnycc

    ciphertext := Encrypt_internal(pi, plaintext);
}

method DigestedSign(key:RSAKeyPairImpl, message:seq<int>) returns (signature:seq<int>)
    requires WellformedRSAKeyPairImpl(key);
    requires IsByteSeq(message);
    requires |message| < power2(28);
    requires RSA_DIGEST_MIN_KEY_SIZE() <= key.pub.size;
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_ready();
    ensures TPM==old(TPM);
    ensures IoMemPerm==old(IoMemPerm);
    ensures RSASignatureRequires(KeyPairImplToSpec(key), message);
    ensures IsByteSeq(signature);
    ensures RSASignature(KeyPairImplToSpec(key), message) == signature;
    ensures |signature|<power2(32);
{
    var kpi := RSAInternalFromKeyPair(key);
    var nref := kpi.pub.n; //- do something real to kpi.pub.n so dafnycc knows it's allocated
    var eref := kpi.pub.e; //- do something real to kpi.pub.e so dafnycc knows it's allocated
    var dref := kpi.d;     //- do something real to kpi.d so dafnycc knows it's allocated
    var recip_ref := if kpi.pub.nReciprocal.FNDivKnownReciprocal? then kpi.pub.nReciprocal.TwoTo32wDividedByD else kpi.pub.n; //- do something real to reciprocal for dafnycc

    var sfn := DigestedSign_internal(kpi, message);
//-    lemma_2toX();
    constrain_word_from_overflowing(sfn.Length);
//-    assert sfn.Length < 0x100000000;
    assert sfn.Length < power2(32);
    signature := sfn[..];
}

method DigestedVerify(pubkey:RSAPubKeyImpl, message:seq<int>, signature:seq<int>) returns (verifies:bool)
    requires WellformedRSAPubKeyImpl(pubkey);
    requires RSA_DIGEST_MIN_KEY_SIZE() <= pubkey.size < power2(60);
    requires IsByteSeq(message);
//-    requires |message| < power2(61);
    requires |message| < power2(28);
    requires IsByteSeq(signature);
    requires |signature| == pubkey.size;
//-    requires signature[0] == 0;
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_ready();
    ensures TPM==old(TPM);
    ensures IoMemPerm==old(IoMemPerm);
    ensures WellformedRSAPubKeySpec(PubKeyImplToSpec(pubkey));
    ensures verifies <==> (
        RSAVerificationRelationRequires(PubKeyImplToSpec(pubkey), message, signature)
        && RSAVerificationRelation(PubKeyImplToSpec(pubkey), message, signature));
{
    var pi := RSAInternalFromPubKey(pubkey);
    var nref := pi.n; //- do something real to pi.n so dafnycc knows it's allocated
    var eref := pi.e; //- do something real to pi.e so dafnycc knows it's allocated
    var recip_ref := if pi.nReciprocal.FNDivKnownReciprocal? then pi.nReciprocal.TwoTo32wDividedByD else pi.n; //- do something real to reciprocal for dafnycc

    verifies := DigestedVerify_internal(pi, message, signature);
}
