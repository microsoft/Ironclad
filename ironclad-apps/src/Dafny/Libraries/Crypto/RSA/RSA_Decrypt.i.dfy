include "RSASpec.s.dfy"
include "../Hash/Digest.i.dfy"
include "../../BigNum/BigNum.i.dfy"
include "../../BigNum/BigNatDiv.i.dfy"
include "../../BigNum/BigNatMod.i.dfy"
include "KeyGen.i.dfy"
include "BlockEncoding.i.dfy"
include "KeyImpl.i.dfy"
include "RSA.i.dfy"
include "RSAOps.i.dfy"

static function PKCS15_EncryptionPad_premium(msg:seq<int>, k:nat, padding:seq<int>) : seq<int>
    requires IsByteSeq(msg);
    requires IsByteSeq(padding);
    requires |padding| == PadCount(msg, k);
    requires NonzeroPad(padding);
    requires PadCount(msg, k) >= 8;
    ensures IsByteSeq(PKCS15_EncryptionPad_premium(msg, k, padding));
{
    lemma_PKCS15_EncryptionPad(msg, k, padding);
    PKCS15_EncryptionPad(msg, k, padding)
}

lemma lemma_zero_ciphertexts_do_not_decrypt(key:RSAKeyPairImpl_internal, ciphertext:seq<int>, cipherN:array<int>)
    requires WellformedRSAKeyPairImpl_internal(key);
    requires IsByteSeq(ciphertext);
    requires |ciphertext|>0;
    requires WellformedFatNat(cipherN);
    requires J(cipherN) == BEByteSeqToInt(ciphertext);
    requires J(cipherN)==0;
    ensures forall any_plaintext :: !RSADecryptionRelation(KeyPairImplToSpec_internal(key), ciphertext, any_plaintext);
{
    forall (any_plaintext |
             IsByteSeq(any_plaintext))
        ensures !RSADecryptionRelation(KeyPairImplToSpec_internal(key), ciphertext, any_plaintext);
    {
        forall (padding |
            IsByteSeq(padding)
            && |padding| == PadCount(any_plaintext, key.pub.size)
            && NonzeroPad(padding)
            && PadCount(any_plaintext, key.pub.size) >= 8)
            ensures
                var padded_msg_n := BEByteSeqToInt(PKCS15_EncryptionPad_premium(any_plaintext, key.pub.size, padding));
                power(J(cipherN), J(key.d)) % J(key.pub.n) != padded_msg_n;
        {
            var padded_msg := PKCS15_EncryptionPad_premium(any_plaintext, key.pub.size, padding);
            var padtail := padded_msg[1..];
            assert padtail[0]==2;

            var padded_msg_n := BEByteSeqToInt(padded_msg);
            var L0 := 0;
            var L1 := 1;
            assert J(cipherN) == 0;

            if (J(key.d)==0)
            {
                //- This case isn't really meaningful, but our spec doesn't currently disallow it.
                calc {
                    power(J(cipherN), J(key.d)) % J(key.pub.n);
                        { reveal_power(); }
                    L1 % J(key.pub.n);
                    <=  { lemma_mod_decreases(L1, J(key.pub.n)); }
                    1;
                }
            }
            else
            {
                calc {
                    power(J(cipherN), J(key.d)) % J(key.pub.n);
                        { lemma_0_power(J(key.d)); }
                    L0 % J(key.pub.n);
                        { lemma_small_mod(L0, J(key.pub.n)); }
                    L0;
                    0;
                }
            }
            calc
            {
                power(J(cipherN), J(key.d)) % J(key.pub.n);
                <
                2;
                    { lemma_mul_is_mul_boogie(1, 2); }
                mul(1, 2);
                <=  {
                    lemma_power_positive(power2(8), |padtail|-1);
                    lemma_mul_inequality_forall();
                }
                mul(power(power2(8), |padtail|-1), 2);
                    { lemma_mul_is_commutative_forall(); }
                mul(2, power(power2(8), |padtail|-1));
                <= { lemma_BEDigitSeqToInt_bound(power2(8), padtail); }
                BEByteSeqToInt(padtail);
                    { lemma_LeadingZeros(power2(8), padtail, padded_msg); }
                BEByteSeqToInt(padded_msg);
                padded_msg_n;
            }
        }
    }
}

lemma lemma_mispadded_plaintexts_do_not_decrypt(key:RSAKeyPairImpl_internal, ciphertext:seq<int>, cipherN:array<int>, plainN:array<int>)
    requires WellformedRSAKeyPairImpl_internal(key);
    requires IsByteSeq(ciphertext);
    requires |ciphertext|>0;
    requires WellformedFatNat(cipherN);
    requires WellformedFatNat(plainN);
    requires J(cipherN) == BEByteSeqToInt(ciphertext);
    requires J(plainN)==power(J(cipherN),J(key.d)) % J(key.pub.n);
    requires !CanDecodeFatInteger(plainN, key.pub.size, PadModeEncrypt());
    ensures forall any_plaintext :: !RSADecryptionRelation(KeyPairImplToSpec_internal(key), ciphertext, any_plaintext);
{
    forall (any_plaintext | IsByteSeq(any_plaintext))
        ensures !RSADecryptionRelation(KeyPairImplToSpec_internal(key), ciphertext, any_plaintext);
    {
        forall (padding |
            IsByteSeq(padding)
            && |padding| == PadCount(any_plaintext, key.pub.size)
            && NonzeroPad(padding)
            && PadCount(any_plaintext, key.pub.size) >= 8)
            ensures
                var padded_msg_n := BEByteSeqToInt(PKCS15_EncryptionPad_premium(any_plaintext, key.pub.size, padding));
                power(J(cipherN), J(key.d)) % J(key.pub.n) != padded_msg_n;
        {
            var pm := PKCS15_EncryptionPad_premium(any_plaintext, key.pub.size, padding);
            assert !IsByteSeq(pm)
                || !IsByteSeq(any_plaintext)
                || !PKCS15_PaddingRelation(pm, any_plaintext, PadModeEncrypt())
                || !(BigEndianIntegerValue(pm)==J(plainN))
                || !(|pm|==key.pub.size);   //- OBSERVE

            var padded_msg_n := BEByteSeqToInt(PKCS15_EncryptionPad_premium(any_plaintext, key.pub.size, padding));
            if (power(J(cipherN), J(key.d)) % J(key.pub.n) == padded_msg_n)
            {
                lemma_BigEndianIntegerValue_equals_BEByteSeqToInt(pm);
                assert !PKCS15_PaddingRelationWith(pm, any_plaintext, PadModeEncrypt(), padding);   //- OBSERVE
                //- assert false;    //- This is a contradiction.
            }
        }
    }
}

method{:dafnycc_conservative_seq_triggers} Decrypt_internal(key:RSAKeyPairImpl_internal, ciphertext:seq<int>) returns (result:bool, plaintext:seq<int>)
    requires WellformedRSAKeyPairImpl_internal(key);
    requires IsByteSeq(ciphertext);
    requires |ciphertext|>0;
//-    requires |ciphertext|%4==0;
        
        
        
        
        
    ensures WellformedRSAKeyPairSpec(KeyPairImplToSpec_internal(key));
    ensures result ==> (IsByteSeq(plaintext) && RSADecryptionRelation(KeyPairImplToSpec_internal(key), ciphertext, plaintext));
    ensures !result ==>
        forall any_plaintext :: !(IsByteSeq(any_plaintext) && RSADecryptionRelation(KeyPairImplToSpec_internal(key), ciphertext, any_plaintext));
{
    var nref := key.pub.n; //- do something real to key.pub.n so dafnycc knows it's allocated
    var eref := key.pub.e; //- do something real to key.pub.e so dafnycc knows it's allocated
    var dref := key.d;     //- do something real to key.d so dafnycc knows it's allocated
    var recip_ref := if key.pub.nReciprocal.FNDivKnownReciprocal? then key.pub.nReciprocal.TwoTo32wDividedByD else key.pub.n; //- dafnycc

    var plaintext_raw := [];
    plaintext := []; //- dafnycc: initialize variable

    var cipherN:array<int> := BESeqToInteger(ciphertext);
    assert WellformedFatNat(cipherN);

    var ciphertext_too_big:bool := FatNatGe(cipherN, key.pub.n);

    var cipherZero := FatNatIsZero(cipherN);
    if (cipherZero)
    {
        lemma_zero_ciphertexts_do_not_decrypt(key, ciphertext, cipherN);
        result := false;
    }
    else if (ciphertext_too_big)
    {
        //- basic condition of spec
        forall (any_plaintext |
                 IsByteSeq(any_plaintext))
            ensures !RSADecryptionRelation(KeyPairImplToSpec_internal(key), ciphertext, any_plaintext);
        {
        }
        result := false;
    }
    else
    {
        assert J(cipherN) < J(key.pub.n);    //- we just checked.

        var plainN:array<int> := InnerDecrypt(key, cipherN);
        ghost var padded_plaintext:seq<int>;
        var success:bool;
        success,plaintext_raw,padded_plaintext := IntegerToMessage(plainN, key.pub.size, PadModeEncrypt());

        if (!success) {
            lemma_mispadded_plaintexts_do_not_decrypt(key, ciphertext, cipherN, plainN);
            result := false;
        }
        else {
            result := true;
            plaintext := DecryptCommonCase(KeyPairImplToSpec_internal(key), ciphertext, J(cipherN), J(plainN), plaintext_raw, padded_plaintext);
            assert 0<J(key.pub.n);
            assert WellformedRSAKeyPairSpec(KeyPairImplToSpec_internal(key));
        }
    }
}

method{:dafnycc_conservative_seq_triggers} DecryptCommonCase(ghost key:RSAKeyPairSpec, ciphertext:seq<int>, ghost cipherN:int,
                                                             ghost plainN:int, plaintext_raw:seq<int>, ghost padded_plaintext:seq<int>)
                                                            returns (plaintext:seq<int>)
    requires WellformedRSAKeyPairSpec(key);
    requires IsByteSeq(ciphertext);
    requires |ciphertext|>0;
    requires 0 < cipherN < key.pub.n;
    requires cipherN == BigEndianIntegerValue(ciphertext);
    requires 0 <= plainN < key.pub.n;
    requires plainN == power(cipherN, key.d) % key.pub.n;
    requires IsByteSeq(plaintext_raw);
    requires IsByteSeq(padded_plaintext);
    requires PKCS15_PaddingRelation(padded_plaintext, plaintext_raw, PadModeEncrypt());
    requires BigEndianIntegerValue(padded_plaintext) == plainN;
    requires |padded_plaintext| == key.pub.size;
    ensures IsByteSeq(plaintext);
    ensures RSADecryptionRelation(key, ciphertext, plaintext);
{
    ghost var padding:seq<int> :| PKCS15_PaddingRelationWith(padded_plaintext, plaintext_raw, PadModeEncrypt(), padding);
    lemma_about_PKCS15_PaddingRelationWith(padded_plaintext, plaintext_raw, PadModeEncrypt(), padding);
    assert padded_plaintext == [0] + [BlockType(PadModeEncrypt())] + padding + [0] + plaintext_raw;

    plaintext := plaintext_raw;
    assert IsByteSeq(padded_plaintext);

    calc {
        power(BigEndianIntegerValue(ciphertext), key.d) % key.pub.n;
        power(cipherN, key.d) % key.pub.n;
        plainN;
        BigEndianIntegerValue(padded_plaintext);
    }

    assert power(BigEndianIntegerValue(ciphertext), key.d) % key.pub.n
        == BigEndianIntegerValue(padded_plaintext);
    assert PKCS15_PaddingRelation(padded_plaintext, plaintext_raw, PadModeEncrypt());

    //- proving RSADecryptionRelation(key, ciphertext, plaintext)
    ghost var padding_n := padding;
    ghost var ep := PKCS15_EncryptionPad(plaintext, key.pub.size, padding_n);

    lemma_PKCS15_EncryptionPad(plaintext, key.pub.size, padding_n);
    assert IsByteSeq(ep);

    ghost var cipher_n := BEByteSeqToInt(ciphertext);
    ghost var padded_msg_n := BEByteSeqToInt(ep);
    assert IsByteSeq(ep);
    calc {    
        padded_plaintext;
        [0] + [BlockType(PadModeEncrypt())] + padding + [0] + plaintext_raw;
        [0] + [BlockType(PadModeEncrypt())] + padding_n + [0] + plaintext;
            { lemma_obvious_concatenation(0, BlockType(PadModeEncrypt())); }
        [0, BlockType(PadModeEncrypt())] + padding_n + [0] + plaintext;
        ep;
    }

    calc {
        cipher_n;
        BEByteSeqToInt(ciphertext);
            { lemma_BigEndianIntegerValue_equals_BEByteSeqToInt(ciphertext); }
        BigEndianIntegerValue(ciphertext);
        cipherN;
    }

    calc {    
        power(cipher_n, key.d) % key.pub.n;
        power(cipherN, key.d) % key.pub.n;
        plainN;
        calc {
            plainN;
            BigEndianIntegerValue(padded_plaintext);
                { lemma_BigEndianIntegerValue_equals_BEByteSeqToInt(padded_plaintext); }
            BEByteSeqToInt(ep);
            padded_msg_n;
        }
        padded_msg_n;
    }
    assert power(cipher_n, key.d) % key.pub.n == padded_msg_n;
    assert RSADecryptionRelation(key, ciphertext, plaintext);
}
