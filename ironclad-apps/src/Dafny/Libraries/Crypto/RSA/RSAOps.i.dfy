include "RSASpec.s.dfy"
include "RSA.i.dfy"

//- Eventually useful for lemma_message_transmission
predicate {:heap} EncryptionRelation(pubkey:RSAPubKeyImpl_internal, p:array<int>, c:array<int>)
    requires WellformedRSAPubKeyImpl_internal(pubkey);
    requires WellformedFatNat(p);
    requires WellformedFatNat(c);
    reads pubkey.n;
    reads pubkey.e;
    reads if pubkey.nReciprocal.FNDivKnownReciprocal? then pubkey.nReciprocal.TwoTo32wDividedByD else pubkey.n;
    reads p;
    reads c;
{
    J(c)==power(J(p),J(pubkey.e)) % J(pubkey.n)
}

method InnerEncrypt(pubkey:RSAPubKeyImpl_internal, plaintext:array<int>) returns (ciphertext:array<int>)
    requires WellformedRSAPubKeyImpl_internal(pubkey);
//-    requires FrumpyBigNat(plaintext);
    requires WellformedFatNat(plaintext);
    requires 0 < J(plaintext) < J(pubkey.n);
//-    ensures FrumpyBigNat(ciphertext);
    ensures WellformedFatNat(ciphertext);
    ensures J(ciphertext) < J(pubkey.n);
    ensures EncryptionRelation(pubkey, plaintext, ciphertext);
{
//-    ciphertext := BigNatModExp(plaintext, pubkey.e, pubkey.n);
//-    var B := BigNatToFatNat(plaintext);
//-    var E := BigNatToFatNat(pubkey.e);
//-    var N := BigNatToFatNat(pubkey.n);
    var B := plaintext;
    var E := pubkey.e;
    var N := pubkey.n;

    ghost var pv := power2(32);
//-    assert IsCanonicalDigitSeq(pv, B[..]);
//-    assert IsCanonicalDigitSeq(pv, E[..]);
//-    assert IsCanonicalDigitSeq(pv, N[..]);
    ghost var Bv := BEWordSeqToInt(B[..]);
    ghost var Ev := BEWordSeqToInt(E[..]);
    ghost var Nv := BEWordSeqToInt(N[..]);

    assert Bv < Nv;
//-    calc {
//-        Ev;
//-        <
//-        Frump();
//-        power2(power2(30));
//-        <=  { lemma_power2_increases(30,31);
//-              lemma_power2_increases(power2(30),power2(31)); }
//-        power2(power2(31));
//-    }
//-    lemma_CanonicalLength_inherit(pv, B[..], N[..], power2(25));
//-    requires BEWordSeqToInt(E[..]) < power2(power2(31));
//-    requires B.Length < power2(25);
//-    requires N.Length < power2(25);

    var R := FatNatModExpUsingReciprocal(B, E, N, pubkey.nReciprocal);
//-    ciphertext := FatNatToBigNat(R);
    ciphertext := R;
}

static predicate RSAEncryptionRequires(pubkey:RSAPubKeySpec, msg:seq<int>, padding:seq<int>)
{
    WellformedRSAPubKeySpec(pubkey)
        && IsByteSeq(msg)
        && IsByteSeq(padding)
        && |padding| == PadCount(msg, pubkey.size)
        && PadCount(msg, pubkey.size) >= 8
        && NonzeroPad(padding)
        && IsDigitSeq(power2(8), PKCS15_EncryptionPad(msg, pubkey.size, padding))
}

static lemma lemma_seq_remove_first_element(s:seq<int>, j:int)
    requires 0 <= j < |s|;
    ensures s[j..] == [s[j]] + s[j+1..];
{
}

static lemma lemma_seq_break_middle(s:seq<int>, i:int, j:int)
    requires 0 <= i <= j <= |s|;
    ensures s[i..] == s[i..j] + s[j..];
{
}

lemma {:heap} lemma_Encrypt_fragile_bit(pubkey:RSAPubKeySpec, plaintext:seq<int>, padded_plaintext:seq<int>, ep:seq<int>, padding:seq<int>)
    requires WellformedRSAPubKeySpec(pubkey);
    requires IsByteSeq(plaintext);
    requires IsByteSeq(padded_plaintext);
    requires IsByteSeq(ep);
    requires IsByteSeq(padding);
    requires PKCS15_PaddingRelationWith(padded_plaintext, plaintext, PadModeEncrypt(), padding);
    requires |padding| == PadCount(plaintext, pubkey.size);
    requires ep == PKCS15_EncryptionPad(plaintext, pubkey.size, padding);
    ensures padded_plaintext == ep;
{
    calc {
        padded_plaintext;
        { lemma_seq_remove_first_element(padded_plaintext, 0); }
        [padded_plaintext[0]] + padded_plaintext[1..];
        [0] + padded_plaintext[1..];
        { lemma_seq_remove_first_element(padded_plaintext, 1); }
        [0] + [padded_plaintext[1]] + padded_plaintext[2..];
        [0] + [BlockType(PadModeEncrypt())] + padded_plaintext[2..];
        { lemma_seq_break_middle(padded_plaintext, 2, |padding|+2); }
        [0] + [BlockType(PadModeEncrypt())] + padded_plaintext[2..|padding|+2] + padded_plaintext[|padding|+2..];
        [0] + [BlockType(PadModeEncrypt())] + padding + padded_plaintext[|padding|+2..];
        { lemma_seq_remove_first_element(padded_plaintext, |padding|+2); }
        [0] + [BlockType(PadModeEncrypt())] + padding + [padded_plaintext[|padding|+2]] + padded_plaintext[|padding|+3..];
        [0] + [BlockType(PadModeEncrypt())] + padding + [0] + padded_plaintext[|padding|+3..];
        [0] + [BlockType(PadModeEncrypt())] + padding + [0] + plaintext;
        { assert [0, BlockType(PadModeEncrypt())] == [0] + [BlockType(PadModeEncrypt())]; }
        [0, BlockType(PadModeEncrypt())] + padding + [0] + plaintext;
        PKCS15_EncryptionPad(plaintext, pubkey.size, padding);
        ep;
    }
}

method {:dafnycc_conservative_seq_triggers} Encrypt_internal(pubkey:RSAPubKeyImpl_internal, plaintext:seq<int>) returns (ciphertext:seq<int>)
    requires IsByteSeq(plaintext);
    requires WellformedRSAPubKeyImpl_internal(pubkey);
    requires |plaintext| <= pubkey.size - 11;
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_ready();
    ensures WellformedRSAPubKeyImpl_internal(pubkey);
    ensures WellformedRSAPubKeySpec(PubKeyImplToSpec_internal(pubkey));
    ensures IsByteSeq(ciphertext);
    ensures exists padding:seq<int> ::
        RSAEncryptionRequires(PubKeyImplToSpec_internal(pubkey), plaintext, padding)
        && RSAEncryption(PubKeyImplToSpec_internal(pubkey), plaintext, padding) == ciphertext;
{
    var nref := pubkey.n; //- do something real to pubkey.n so dafnycc knows it's allocated
    var eref := pubkey.e; //- do something real to pubkey.e so dafnycc knows it's allocated
    var recip_ref := if pubkey.nReciprocal.FNDivKnownReciprocal? then pubkey.nReciprocal.TwoTo32wDividedByD else pubkey.n; //- do something real to reciprocal for dafnycc

    var plainN:array<int>;
    ghost var padded_plaintext:seq<int>;
    plainN,padded_plaintext := MessageToInteger(plaintext, pubkey.size, PadModeEncrypt());
    
    calc {
        J(plainN);
            <= power2(8*(pubkey.size-1));
            <= {
                //- KeySizeIs ensures
                assert KeyModulusMatchesSizeInBytes(PubKeyImplToSpec_internal(pubkey).n, pubkey.size);
                assert (pubkey.size>0 ==> power2(8*(pubkey.size-1)) <= J(pubkey.n));
                assert power2(8*(pubkey.size-1)) <= J(pubkey.n);
            }
        J(pubkey.n);
    }
//-    assert FrumpyBigNat(plainN);
        
    var cipherN:array<int> := InnerEncrypt(pubkey, plainN);
    var ciphertext_raw := IntegerToBESeq(cipherN);

    assert IsByteSeq(ciphertext_raw);        
    assert IsByteSeq(padded_plaintext);
    assert PKCS15_PaddingRelation(padded_plaintext, plaintext, PadModeEncrypt());

    calc {
        BigEndianIntegerValue(ciphertext_raw);
        J(cipherN);
        //- InnerEncrypt ensures, EncryptionRelation ensures
        power(J(plainN),J(pubkey.e)) % J(pubkey.n);
        power(BigEndianIntegerValue(padded_plaintext),J(pubkey.e)) % J(pubkey.n);
        power(BigEndianIntegerValue(padded_plaintext),PubKeyImplToSpec_internal(pubkey).e) % PubKeyImplToSpec_internal(pubkey).n;
    }

    ciphertext := EncryptSecondStep(PubKeyImplToSpec_internal(pubkey), plaintext, J(plainN), padded_plaintext, J(cipherN), ciphertext_raw);
}

method {:dafnycc_conservative_seq_triggers} EncryptSecondStep(ghost pubkey:RSAPubKeySpec, ghost plaintext:seq<int>,
                                                              ghost plainN:int, ghost padded_plaintext:seq<int>, ghost cipherN:int,
                                                              ciphertext_raw:seq<int>) returns (ciphertext:seq<int>)
    requires IsByteSeq(plaintext);
    requires WellformedRSAPubKeySpec(pubkey);
    requires |plaintext| <= pubkey.size - 11;
    requires plainN < pubkey.n;
    requires IsByteSeqOfLen(padded_plaintext, pubkey.size);
    requires PKCS15_PaddingRelation(padded_plaintext, plaintext, PadModeEncrypt());
    requires plainN == BigEndianIntegerValue(padded_plaintext);
    requires cipherN < pubkey.n;
    requires cipherN == power(plainN, pubkey.e) % pubkey.n;
    requires IsByteSeq(ciphertext_raw);
    requires |ciphertext_raw| >= 1;
    requires cipherN == BigEndianIntegerValue(ciphertext_raw);
    requires ciphertext_raw == [0] + BEIntToByteSeq(cipherN);
    requires BigEndianIntegerValue(ciphertext_raw) == power(BigEndianIntegerValue(padded_plaintext), pubkey.e) % pubkey.n;
    ensures IsByteSeq(ciphertext);
    ensures exists padding:seq<int> ::
        RSAEncryptionRequires(pubkey, plaintext, padding)
        && RSAEncryption(pubkey, plaintext, padding) == ciphertext;
{
    
    
    ciphertext := ciphertext_raw[1..];
        
    ghost var padding:seq<int> :| PKCS15_PaddingRelationWith(padded_plaintext, plaintext, PadModeEncrypt(), padding);
        
    ghost var ep := PKCS15_EncryptionPad(plaintext, pubkey.size, padding);
    //-        assert IsByteSeq(ep);
    ghost var pad_msg := BEByteSeqToInt(ep);

    lemma_Encrypt_fragile_bit(pubkey, plaintext, padded_plaintext, ep, padding);

    calc {
        RSAEncryption(pubkey, plaintext, padding);
        BEIntToByteSeq(power(pad_msg, pubkey.e) % pubkey.n);
        {
            calc {    
                power(pad_msg, pubkey.e) % pubkey.n;
                {
                    calc {
                        plainN;
                        BigEndianIntegerValue(padded_plaintext);
                            { lemma_BigEndianIntegerValue_equals_BEByteSeqToInt(padded_plaintext); }
                        BEByteSeqToInt(ep);
                        pad_msg;
                    }
                }
                power(plainN, pubkey.e) % pubkey.n;
                cipherN;
            }
            //- Note that here we merely show equivalent integer values;
            //- the legacy function IntegerToBESeq has been equipped with an
            //- additional ensures about BEIntToByteSeq.
        }
        BEIntToByteSeq(cipherN);
            { assert [0] + BEIntToByteSeq(cipherN) == ciphertext_raw; }
        ciphertext_raw[1..];
        ciphertext;
    }
}

//- Eventually useful for lemma_message_transmission
predicate {:heap} DecryptionRelation(key:RSAKeyPairImpl_internal, c:array<int>, p:array<int>)
    requires WellformedRSAKeyPairImpl_internal(key);
    requires WellformedFatNat(c);
    requires WellformedFatNat(p);
    reads c;
    reads p;
    reads key.pub.n;
    reads key.pub.e;
    reads key.d;
    reads if key.pub.nReciprocal.FNDivKnownReciprocal? then key.pub.nReciprocal.TwoTo32wDividedByD else key.pub.n;
{
    J(p)==power(J(c),J(key.d)) % J(key.pub.n)
}

method InnerDecrypt(key:RSAKeyPairImpl_internal, ciphertext:array<int>) returns (plaintext:array<int>)
    requires WellformedRSAKeyPairImpl_internal(key);
    requires WellformedFatNat(ciphertext);
    requires 0 < J(ciphertext) < J(key.pub.n);
    ensures WellformedFatNat(plaintext);
    ensures J(plaintext) < J(key.pub.n);
    ensures DecryptionRelation(key, ciphertext, plaintext);
{
    plaintext := FatNatModExpUsingReciprocal(ciphertext, key.d, key.pub.n, key.pub.nReciprocal);
}

static lemma lemma_about_PKCS15_PaddingRelationWith(padded_msg:seq<int>, msg:seq<int>, pad_mode:PadMode, padding:seq<int>)
    requires IsByteSeq(padded_msg);
    requires IsByteSeq(msg);
    requires PKCS15_PaddingRelationWith(padded_msg, msg, pad_mode, padding);
    ensures padded_msg == [0] + [BlockType(pad_mode)] + padding + [0] + msg;
{
}

static lemma lemma_PKCS15_EncryptionPad(msg:seq<int>, k:nat, padding:seq<int>)
    requires IsByteSeq(msg);
    requires IsByteSeq(padding);
    requires |padding| == k - 3 - |msg|;
    requires |padding| >= 8;
    requires NonzeroPad(padding);
    ensures PKCS15_EncryptionPad(msg, k, padding)
        == [0, BlockType(PadModeEncrypt())] + padding + [0] + msg;
    ensures IsByteSeq(PKCS15_EncryptionPad(msg, k, padding));
{
    lemma_2toX();
}

static lemma lemma_PKCS15_SignaturePad(msg:seq<int>, k:nat)
    requires IsByteSeq(msg);
    requires k - 3 - |msg| >= 8;
    ensures PKCS15_SignaturePad(msg, k)
        == [0, BlockType(PadModeSign())] + RepeatDigit(SignaturePadByte(), k - 3 - |msg|) + [0] + msg;
    ensures IsByteSeq(PKCS15_SignaturePad(msg, k));
{
    lemma_2toX();
    lemma_RepeatDigit_for_ByteSeq(SignaturePadByte(), k - 3 - |msg|);
}

static lemma lemma_obvious_concatenation(x:int, y:int)
    ensures [x] + [y] == [x,y];
{
}

static lemma lemma_obvious_length(x:seq<int>, y:seq<int>, z:seq<int>)
    requires x == y + z;
    ensures |x| == |y| + |z|;
{
}

static predicate RSASignatureRequires(key: RSAKeyPairSpec, message: seq<int>)
{
    WellformedRSAKeyPairSpec(key)
    && IsByteSeq(message)
    && IsBitSeq(BEByteSeqToBitSeq_premium(message))
    && |BEByteSeqToBitSeq_premium( message)| < power2(64)
    && IsWordSeq(SHA256(BEByteSeqToBitSeq_premium(message)))
    && IsByteSeq(SHA256Digest(message))
    && PadCount(SHA256Digest(message), key.pub.size) >= 8
    && IsByteSeq(PKCS15_SignaturePad(SHA256Digest(message), key.pub.size))
}

static lemma lemma_RSA_message_length_bound(message:seq<int>)
    requires IsByteSeq(message);
    requires |message| < power2(28);
    ensures IsByteSeq(SHA256_DigestInfo_premium() + message);
    ensures |BEByteSeqToBitSeq_premium(SHA256_DigestInfo_premium() + message)| < power2(64);
{
    calc {
        |SHA256_DigestInfo() + message|;
        19 + |message|;
        < 19 + power2(28);
        <   { lemma_2toX(); lemma_power2_add8(24); lemma_power2_add8(56); }
        power2(61);
    }
    //- Drop a hint to Dafny that IsByteSeq extends across seq addition:
    assert IsByteSeq(SHA256_DigestInfo_premium() + message);
    calc {
        |BEByteSeqToBitSeq_premium(SHA256_DigestInfo() + message)|;
        8*|SHA256_DigestInfo() + message|;
        <   8*power2(61);
            { lemma_2toX(); lemma_power2_add8(56); }
        power2(64);
    }
}

static function method RSA_DIGEST_MIN_KEY_SIZE() : int { 62 }

static predicate RSAVerificationRelationRequires(pubkey:RSAPubKeySpec, message:seq<int>, signature:seq<int>)
{
    //- NB we premium-ify methods to trigger corresponding ensures
    IsByteSeq(signature)
    && IsByteSeq(message)
    && IsBitSeq(BEByteSeqToBitSeq_premium(message))
    && |BEByteSeqToBitSeq_premium(message)| < power2(64)
    && IsWordSeq(SHA256(BEByteSeqToBitSeq_premium(message)))
    && IsByteSeq(SHA256Digest(message))
    && PadCount(SHA256Digest(message), pubkey.size) >= 8
    && IsByteSeq(PKCS15_SignaturePad(SHA256Digest(message), pubkey.size))
}

method {:timeLimitMultiplier 3} DigestedVerifyCommonCase(pubkey:RSAPubKeyImpl_internal, message:seq<int>, signature:seq<int>, signatureN:array<int>) returns (verifies:bool)
    requires WellformedRSAPubKeyImpl_internal(pubkey);
    requires RSA_DIGEST_MIN_KEY_SIZE() <= pubkey.size < power2(60);
    requires RSAVerificationRelationRequires(PubKeyImplToSpec_internal(pubkey), message, signature);
    requires |message| < power2(28);
    requires |signature| == pubkey.size;
    requires WellformedRSAPubKeySpec(PubKeyImplToSpec_internal(pubkey));
    requires signatureN != null;
    requires IsWordSeq(signatureN[..]);
    requires BEWordSeqToInt(signatureN[..]) == BEByteSeqToInt(signature);
    requires |signature| == pubkey.size;
    requires BEWordSeqToInt(signatureN[..]) != 0;
    requires J(signatureN) < J(pubkey.n);
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_ready();
    ensures TPM==old(TPM);
    ensures IoMemPerm==old(IoMemPerm);
    ensures WellformedRSAPubKeySpec(PubKeyImplToSpec_internal(pubkey));
    ensures verifies <==> RSAVerificationRelation(PubKeyImplToSpec_internal(pubkey), message, signature);
{
    var nref := pubkey.n; //- do something real to pubkey.n so dafnycc knows it's allocated
    var eref := pubkey.e; //- do something real to pubkey.e so dafnycc knows it's allocated
    var recip_ref := if pubkey.nReciprocal.FNDivKnownReciprocal? then pubkey.nReciprocal.TwoTo32wDividedByD else pubkey.n; //- dafnycc

    lemma_2toX32();
    var digested_message := SHA256DigestImpl(message);
    var padded_message_raw := PadMessage(digested_message, pubkey.size, PadModeSign());
    var padded_message := padded_message_raw;
    var padded_message_array := SeqToArray(padded_message);
    var padded_messageN := BEByteArrayToWordArray(padded_message_array);

    assert 0 < J(signatureN) < J(pubkey.n);
    var putative_padded_messageN := InnerEncrypt(pubkey, signatureN);

    verifies := FatNatEq(padded_messageN, putative_padded_messageN);

    lemma_RSA_message_length_bound(message);
}

method DigestedVerify_internal(pubkey:RSAPubKeyImpl_internal, message:seq<int>, signature:seq<int>) returns (verifies:bool)
    requires WellformedRSAPubKeyImpl_internal(pubkey);
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
    ensures WellformedRSAPubKeySpec(PubKeyImplToSpec_internal(pubkey));
    ensures verifies <==> (
        RSAVerificationRelationRequires(PubKeyImplToSpec_internal(pubkey), message, signature)
        && RSAVerificationRelation(PubKeyImplToSpec_internal(pubkey), message, signature));
{
    var nref := pubkey.n; //- do something real to pubkey.n so dafnycc knows it's allocated
    var eref := pubkey.e; //- do something real to pubkey.e so dafnycc knows it's allocated
    var recip_ref := if pubkey.nReciprocal.FNDivKnownReciprocal? then pubkey.nReciprocal.TwoTo32wDividedByD else pubkey.n; //- dafnycc

    lemma_WellformedPubKeyImplImpliesWellformedPubKeySpec(pubkey);

    var signature_array := SeqToArray(signature);
    var signatureN := BEByteArrayToWordArray(signature_array);

    var zerosig := FatNatIsZero(signatureN);
    if (|signature|!=pubkey.size || zerosig)
    {
        assert BEByteSeqToInt(signature)==0;
        verifies := false;
        return;
    }

    lemma_2toX32();
    calc {
        |BEByteSeqToBitSeq_premium(message)|;
        |message|*8;
        <= power2(28)*8;
            { lemma_mul_is_mul_boogie(power2(28), 8); }
        power2(28)*power2(3);
            { lemma_power2_adds(28,3); }
        power2(31);
    }
    lemma_power2_strictly_increases(31,61);
    lemma_power2_strictly_increases(31,64);
    lemma_PKCS15_SignaturePad(SHA256Digest_premium(message), pubkey.size);

    var sig_short_enough := FatNatLt(signatureN, pubkey.n);
    if (!sig_short_enough)
    {
        assert !(BEByteSeqToInt(signature) < PubKeyImplToSpec_internal(pubkey).n);
        assert !RSAVerificationRelation(PubKeyImplToSpec_internal(pubkey), message, signature);
        verifies := false;
        return;
    }

    verifies := DigestedVerifyCommonCase(pubkey, message, signature, signatureN);
}

//-lemma lemma_message_transmission(key:RSAKeyPairImpl_internal, p_in:BigNat, c:BigNat, p_out:BigNat)
//-    requires WellformedRSAKeyPairImpl_internal(key);
//-    requires WellformedBigNat(p_in);
//-    requires WellformedBigNat(c);
//-    requires WellformedBigNat(p_out);
//-    requires I(p_in) < I(key.pub.n);
//-    requires I(c) < I(key.pub.n);
//-    requires I(p_out) < I(key.pub.n);
//-    requires EncryptionRelation(key.pub, p_in, c);
//-    requires DecryptionRelation(key, c, p_out);
//-    ensures p_in == p_out;
//
//
//
