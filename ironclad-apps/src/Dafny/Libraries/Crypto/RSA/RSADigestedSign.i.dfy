include "RSASpec.s.dfy"
include "RSA.i.dfy"
include "RSAOps.i.dfy"

method {:dafnycc_conservative_seq_triggers} DigestedSign_internal(key:RSAKeyPairImpl_internal, message:seq<int>)
                                                                 returns (signature:array<int>)
    requires WellformedRSAKeyPairImpl_internal(key);
    requires IsByteSeq(message);
    requires |message| < power2(28);
    requires RSA_DIGEST_MIN_KEY_SIZE() <= key.pub.size;
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_ready();
    ensures TPM==old(TPM);
    ensures IoMemPerm==old(IoMemPerm);
    ensures RSASignatureRequires(KeyPairImplToSpec_internal(key), message);
    ensures signature!=null;
    ensures IsByteSeq(signature[..]);
    ensures RSASignature(KeyPairImplToSpec_internal(key), message) == signature[..];
    ensures fresh(signature);
//-    ensures Word32(signature.Length);
{
    var nref := key.pub.n; //- do something real to key.pub.n so dafnycc knows it's allocated
    var eref := key.pub.e; //- do something real to key.pub.e so dafnycc knows it's allocated
    var dref := key.d;     //- do something real to key.d so dafnycc knows it's allocated
    var recip_ref := if key.pub.nReciprocal.FNDivKnownReciprocal? then key.pub.nReciprocal.TwoTo32wDividedByD else key.pub.n; //- dafnycc

    calc {
        |BEByteSeqToBitSeq_premium(message)|;
        <
        calc {
            |BEByteSeqToBitSeq_premium(message)|;
                { lemma_BEByteSeqToBitSeq_ensures(message); }
            |message|*8;
                { lemma_mul_is_mul_boogie(|message|, 8); }
            mul(|message|,8);
                { lemma_2toX32(); }
            |message|*power2(3);
            <   { lemma_mul_strict_inequality(|message|,power2(28),power2(3)); }
            power2(28)*power2(3);
                { lemma_power2_adds(28,3); }
            power2(31);
            <=  { lemma_power2_increases(31,64); }
            power2(64);
        }
        power2(64);
    }

    lemma_power2_increases(28,61);
    lemma_power2_increases(28,29);

    var digested_message := SHA256DigestImpl(message);
    signature := DigestedSignSecondPart(key, message, digested_message);
}

predicate {:heap} DigestedSignSecondPartRequirements(key:RSAKeyPairImpl_internal, message:seq<int>, digested_message:seq<int>)
    reads key.pub.n;
    reads key.pub.e;
    reads key.d;
    reads if key.pub.nReciprocal.FNDivKnownReciprocal? then key.pub.nReciprocal.TwoTo32wDividedByD else key.pub.n;
{
    WellformedRSAKeyPairImpl_internal(key)
    && IsByteSeq(message)
    && |message| < power2(28)
    && |message| < power2(29)
    && |message| < power2(61)
    && RSA_DIGEST_MIN_KEY_SIZE() <= key.pub.size
    && |BEByteSeqToBitSeq(message)| < power2(64)
    && IsBitSeq(BEByteSeqToBitSeq(message))
    && IsByteSeq(digested_message)
    && digested_message == SHA256Digest(message)
    && |digested_message| == 51
}

method {:dafnycc_conservative_seq_triggers} DigestedSignSecondPart(key:RSAKeyPairImpl_internal, message:seq<int>, digested_message:seq<int>)
                                                                  returns (signature:array<int>)
    requires DigestedSignSecondPartRequirements(key, message, digested_message);
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_ready();
    ensures TPM==old(TPM);
    ensures IoMemPerm==old(IoMemPerm);
    ensures RSASignatureRequires(KeyPairImplToSpec_internal(key), message);
    ensures signature!=null;
    ensures IsByteSeq(signature[..]);
    ensures RSASignature(KeyPairImplToSpec_internal(key), message) == signature[..];
    ensures fresh(signature);
{
    var nref := key.pub.n; //- do something real to key.pub.n so dafnycc knows it's allocated
    var eref := key.pub.e; //- do something real to key.pub.e so dafnycc knows it's allocated
    var dref := key.d;     //- do something real to key.d so dafnycc knows it's allocated
    var recip_ref := if key.pub.nReciprocal.FNDivKnownReciprocal? then key.pub.nReciprocal.TwoTo32wDividedByD else key.pub.n; //- dafnycc

    calc {
        PadCount(digested_message, key.pub.size);
        key.pub.size - 3 - |digested_message|;
        >= RSA_DIGEST_MIN_KEY_SIZE() - 3 - 51;
        62 - 3 - 51;
        8;
    }

    var messageN:array<int>;
    ghost var padded_msg:seq<int>;
    messageN,padded_msg := MessageToInteger(digested_message, key.pub.size, PadModeSign());
    assert padded_msg == PKCS15_SignaturePad(SHA256Digest(message), key.pub.size);

    assert TPM == old(TPM);
    assert IoMemPerm == old(IoMemPerm);

    lemma_PKCS15_SignaturePad(SHA256Digest_premium(message), key.pub.size);
    assert RSASignatureRequires(KeyPairImplToSpec_internal(key), message);
    signature := DigestedSignThirdPart(key, message, digested_message, messageN, padded_msg);
}

predicate {:heap} DigestedSignThirdPartRequirements (key:RSAKeyPairImpl_internal, message:seq<int>, digested_message:seq<int>,
                                                     messageN:seq<int>, padded_msg:seq<int>)
    reads key.pub.n;
    reads key.pub.e;
    reads key.d;
    reads if key.pub.nReciprocal.FNDivKnownReciprocal? then key.pub.nReciprocal.TwoTo32wDividedByD else key.pub.n;
{
    DigestedSignSecondPartRequirements(key, message, digested_message)
    && IsWordSeq(messageN)
    && IsByteSeq(padded_msg)
//-    && PKCS15_SignaturePad(SHA256Digest(message), key.pub.size) == [0, BlockType(PadModeSign())] + RepeatDigit(SignaturePadByte(), key.pub.size - 3 - |SHA256Digest(message)|) + [0] + SHA256Digest(message)
    && PKCS15_SignaturePad(digested_message, key.pub.size) == padded_msg
    && PKCS15_PaddingRelation(padded_msg, digested_message, PadModeSign())
    && RSASignatureRequires(KeyPairImplToSpec_internal(key), message)
    && BigEndianIntegerValue(padded_msg)==BEWordSeqToInt(messageN)
    && BEByteSeqToInt(padded_msg)==BEWordSeqToInt(messageN)
    && 0 < BEWordSeqToInt(messageN) < power2(8*(key.pub.size-1))
    && |padded_msg|==key.pub.size
}

method {:dafnycc_conservative_seq_triggers} DigestedSignThirdPart(key:RSAKeyPairImpl_internal, ghost message:seq<int>,
                                                                  ghost digested_message:seq<int>, messageN:array<int>,
                                                                  ghost padded_msg:seq<int>) returns (signature:array<int>)
    requires WellformedFatNat(messageN);
    requires DigestedSignThirdPartRequirements(key, message, digested_message, messageN[..], padded_msg);
    requires messageN != key.pub.n && messageN != key.pub.e;
    requires key.pub.nReciprocal.FNDivKnownReciprocal? ==> messageN != key.pub.nReciprocal.TwoTo32wDividedByD;
    ensures RSASignatureRequires(KeyPairImplToSpec_internal(key), message);
    ensures signature!=null;
    ensures IsByteSeq(signature[..]);
    ensures RSASignature(KeyPairImplToSpec_internal(key), message) == signature[..];
    ensures fresh(signature);
{
    var nref := key.pub.n; //- do something real to key.pub.n so dafnycc knows it's allocated
    var eref := key.pub.e; //- do something real to key.pub.e so dafnycc knows it's allocated
    var dref := key.d;     //- do something real to key.d so dafnycc knows it's allocated
    var recip_ref := if key.pub.nReciprocal.FNDivKnownReciprocal? then key.pub.nReciprocal.TwoTo32wDividedByD else key.pub.n; //- dafnycc

    var signatureN:array<int> := InnerDecrypt(key, messageN);
    var short_signature := BEWordArrayToByteArray(signatureN);

    calc {
        BEDigitSeqToInt(power2(8), short_signature[..]);
        J(signatureN);
        <
        J(key.pub.n);
        <
        power2(8*key.pub.size);
            { lemma_power2_unfolding(8, key.pub.size);
              lemma_mul_is_mul_boogie(8, key.pub.size); }
        power(power2(8), key.pub.size);
    }
    lemma_CanonicalLengthBound(power2(8), short_signature[..], key.pub.size);
    //-assert short_signature.Length <= key.pub.size;

    signature := DigestedSignFourthPart(key, message, digested_message, messageN[..], padded_msg, signatureN[..], short_signature);
}

predicate {:heap} DigestedSignFourthPartRequirements (key:RSAKeyPairImpl_internal, message:seq<int>, digested_message:seq<int>,
                                                      messageN:seq<int>, padded_msg:seq<int>, signatureN:seq<int>,
                                                      short_signature:seq<int>)
    reads key.pub.n;
    reads key.pub.e;
    reads key.d;
    reads if key.pub.nReciprocal.FNDivKnownReciprocal? then key.pub.nReciprocal.TwoTo32wDividedByD else key.pub.n;
{
    DigestedSignThirdPartRequirements(key, message, digested_message, messageN, padded_msg)
    && IsWordSeq(signatureN)
    && BEWordSeqToInt(signatureN) == power(BEWordSeqToInt(messageN), BEWordSeqToInt(key.d[..])) % BEWordSeqToInt(key.pub.n[..])
    && IsByteSeq(short_signature)
    && BEByteSeqToInt(short_signature) == BEWordSeqToInt(signatureN)
    && |short_signature| <= key.pub.size
    && BEByteSeqToInt(short_signature) < power(power2(8), key.pub.size)
}

method {:dafnycc_conservative_seq_triggers} DigestedSignFourthPart(key:RSAKeyPairImpl_internal, ghost message:seq<int>,
                                                                   ghost digested_message:seq<int>, ghost messageN:seq<int>,
                                                                   ghost padded_msg:seq<int>, ghost signatureN:seq<int>,
                                                                   short_signature:array<int>) returns (signature:array<int>)
    requires short_signature != null;
    requires DigestedSignFourthPartRequirements(key, message, digested_message, messageN, padded_msg, signatureN, short_signature[..]);
    requires short_signature != key.pub.n && short_signature != key.pub.e;
    requires key.pub.nReciprocal.FNDivKnownReciprocal? ==> short_signature != key.pub.nReciprocal.TwoTo32wDividedByD;
    ensures RSASignatureRequires(KeyPairImplToSpec_internal(key), message);
    ensures signature!=null;
    ensures IsByteSeq(signature[..]);
    ensures RSASignature(KeyPairImplToSpec_internal(key), message) == signature[..];
    ensures fresh(signature);
{
    var nref := key.pub.n; //- do something real to key.pub.n so dafnycc knows it's allocated
    var eref := key.pub.e; //- do something real to key.pub.e so dafnycc knows it's allocated
    var dref := key.d;     //- do something real to key.d so dafnycc knows it's allocated
    var recip_ref := if key.pub.nReciprocal.FNDivKnownReciprocal? then key.pub.nReciprocal.TwoTo32wDividedByD else key.pub.n; //- dafnycc

    signature := PadArrayLeft(key.pub.size - short_signature.Length, short_signature);

    ghost var shorts := short_signature[..];
    ghost var longs := signature[..];
    forall (i | |longs|-|shorts|<=i<|longs|)
        ensures longs[i] == shorts[i - (|longs|-|shorts|)];
    {
        calc {
            longs[i];
            signature[..][i];
            signature[key.pub.size - short_signature.Length .. ][i - (key.pub.size - short_signature.Length)];
              { assert signature[key.pub.size - short_signature.Length .. ] == short_signature[..]; }
            short_signature[..][i - (key.pub.size - short_signature.Length)];
            shorts[i - (key.pub.size - short_signature.Length)];
            shorts[i - (|longs|-|shorts|)];
        }
    }
               
    calc {
        BEByteSeqToInt(signature[..]);
            { lemma_LeadingZeros(power2(8), short_signature[..], signature[..]); }
        BEByteSeqToInt(short_signature[..]);
        BEWordSeqToInt(signatureN);
    }

    Lemma_DigestedSignFourthPartHelper(KeyPairImplToSpec_internal(key), message, digested_message, messageN, padded_msg, signatureN, short_signature[..], signature[..]);
}

lemma {:dafnycc_conservative_seq_triggers} Lemma_DigestedSignFourthPartHelper(key:RSAKeyPairSpec, message:seq<int>,
                                                                              digested_message:seq<int>, messageN:seq<int>,
                                                                              padded_msg:seq<int>, signatureN:seq<int>,
                                                                              short_signature:seq<int>, signature:seq<int>)
    requires WellformedRSAKeyPairSpec(key);
    requires IsByteSeq(message);
    requires RSA_DIGEST_MIN_KEY_SIZE() <= key.pub.size;
    requires IsByteSeq(padded_msg);
    requires IsByteSeq(digested_message);
    requires IsBitSeq(BEByteSeqToBitSeq(message));
    requires |BEByteSeqToBitSeq(message)| < power2(64);
    requires digested_message == SHA256Digest(message);
    requires |digested_message| == 51;
    requires PKCS15_PaddingRelation(padded_msg, digested_message, PadModeSign());
    requires PKCS15_SignaturePad(digested_message, key.pub.size) == padded_msg;
    requires RSASignatureRequires(key, message);
    requires IsWordSeq(messageN);
    requires BigEndianIntegerValue(padded_msg)==BEWordSeqToInt(messageN);
    requires BEByteSeqToInt(padded_msg)==BEWordSeqToInt(messageN);
    requires |padded_msg|==key.pub.size;
    requires IsWordSeq(signatureN);
    requires BEWordSeqToInt(signatureN) == power(BEWordSeqToInt(messageN), key.d) % key.pub.n;
    requires IsByteSeq(short_signature);
    requires BEByteSeqToInt(short_signature) == BEWordSeqToInt(signatureN);
    requires |short_signature| <= key.pub.size;
    requires BEByteSeqToInt(short_signature) < power(power2(8), key.pub.size);
    requires |signature| == key.pub.size;
    requires IsByteSeq(signature);
    requires forall i :: |signature|-|short_signature| <= i < |signature| ==> signature[i] == short_signature[i - (|signature| - |short_signature|)];
    requires BEByteSeqToInt(signature) == BEWordSeqToInt(signatureN);

    ensures RSASignature(key, message) == signature;
{
    //-assert BEIntToByteSeq(I(signatureN)) == signature;

    ghost var padded_nint := BEByteSeqToInt(PKCS15_SignaturePad(SHA256Digest(message), key.pub.size));
    ghost var sign_n := power(padded_nint, key.d) % key.pub.n;
    assert power(padded_nint, key.d) % key.pub.n == BEWordSeqToInt(signatureN);
    ghost var sslen := |short_signature|;
    if (key.pub.size < sslen)
    {
        //- The calc below is nested to hide the internals of the calc from later code even in DafnyCC
        calc {
            true ==>
            calc {
                key.pub.n;
                <
                power2(8*key.pub.size);
                <=   { lemma_power2_increases(8*key.pub.size, 8*(sslen-1)); }
                power2(8*(sslen-1));
                    { lemma_power2_unfolding(8, (sslen-1));
                        lemma_mul_is_mul_boogie(8, (sslen-1)); }
                power(power2(8), sslen-1);
                    { lemma_mul_basics_forall(); }
                mul(1, power(power2(8), sslen-1));
                <=  {
                    lemma_power_positive(power2(8), sslen-1);
                    lemma_mul_inequality(1, short_signature[0], power(power2(8), sslen-1));
                }
                short_signature[0] * power(power2(8), sslen-1);
                <=  { lemma_BEDigitSeqToInt_bound(power2(8), short_signature); }
                BEByteSeqToInt(short_signature);
                BEWordSeqToInt(signatureN);
            }
            false;
        }
    }
    calc {
        signature;
            { lemma_BEDigitSeqToInt_invertibility(power2(8), BEWordSeqToInt(signatureN), signature); }
        BEIntToDigitSeq(power2(8), |signature|, BEWordSeqToInt(signatureN));
        BEIntToDigitSeq(power2(8), key.pub.size, sign_n);
            { assert WellformedRSAKeyPairSpec(key); }
        RSASignature(key, message);
    }

    assert BEWordSeqToInt(signatureN) < key.pub.n;
    lemma_BEIntToDigitSeq_properties(power2(8), 0, BEWordSeqToInt(signatureN));

    calc {
        |signature|;
        <=  { if (BEWordSeqToInt(signatureN)==0) { reveal_BEIntToDigitSeq_private(); } }
        key.pub.size;
    }
}
