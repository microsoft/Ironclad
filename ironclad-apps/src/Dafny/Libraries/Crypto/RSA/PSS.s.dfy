include "OAEP.s.dfy"

//-////////////////////////////////////////////////////////////////////////
//- High-level functions for external use
//-////////////////////////////////////////////////////////////////////////

static predicate {:autoReq} PSSSignatureRelation(key:RSAKeyPairSpec, M:seq<int>, S:seq<int>, old_TPM:TPM_struct, new_TPM:TPM_struct)
{
    new_TPM.random_index - old_TPM.random_index == sLen() &&
    S == RSASSA_PSS_SIGN(key, M, TPM_random_bytes(old_TPM.random_index, new_TPM.random_index))
}

static predicate {:autoReq} PSSVerificationRelation(pubkey:RSAPubKeySpec, M:seq<int>, S:seq<int>, verification_result:bool)
{
    RSASSA_PSS_VERIFY(pubkey, M, S) == verification_result
}

//-////////////////////////////////////////////////////////////////////////
//- Helper functions
//-////////////////////////////////////////////////////////////////////////

static function CountBits(x:nat) : int
{
    if x == 0 then 0 else 1 + CountBits(x/2)
}

static function ClearMSBs(s:seq<int>, numZeroBits:int) : seq<int>
    requires 0 <= numZeroBits <= 8;
{
    if s == [] then
        s
    else
        s[0 := s[0] % power2(8 - numZeroBits)]
}

//-////////////////////////////////////////////////////////////////////////
//- RSAVP1 as defined in RFC 3447 section 5.2
//-////////////////////////////////////////////////////////////////////////

static function RSAVP1(pubkey:RSAPubKeySpec, s:int) : int
    requires WellformedRSAPubKeySpec(pubkey);
    requires 0 <= s < pubkey.n;
{
    power(s, pubkey.e) % pubkey.n
}

//-////////////////////////////////////////////////////////////////////////
//- RSASSA-PSS-SIGN as defined in RFC 3447 section 8.1.1
//-////////////////////////////////////////////////////////////////////////

static function {:autoReq} RSASSA_PSS_SIGN(key:RSAKeyPairSpec, M:seq<int>, salt:seq<int>) : seq<int>
    requires WellformedRSAKeyPairSpec(key);
    requires IsByteSeq(M);
    requires IsByteSeqOfLen(salt, sLen());
{
    var modBits := CountBits(key.pub.n);
    var EM := EMSA_PSS_ENCODE(M, modBits - 1, salt);
    var m := OS2IP(EM);
    var s := RSASP1(key, m);
    var S := I2OSP(s, key.pub.size);
    S
}

//-////////////////////////////////////////////////////////////////////////
//- RSASSA-RSS-VERIFY as defined in RFC 3447 section 8.1.2
//-////////////////////////////////////////////////////////////////////////

static predicate {:autoReq} RSASSA_PSS_VERIFY(pubkey:RSAPubKeySpec, M:seq<int>, S:seq<int>)
    requires WellformedRSAPubKeySpec(pubkey);
    requires IsByteSeq(M);
    requires IsByteSeq(S);
{
    |S|==pubkey.size &&
    var s := OS2IP(S);
    0 <= s < pubkey.n &&
    var m := RSAVP1(pubkey, s);
    var modBits := CountBits(pubkey.n);
    var emLen := DivideRoundingUp(modBits - 1, 8);
    emLen >= 0 &&
    0 <= m < power(power2(8), emLen) &&
    var EM := I2OSP(m, emLen);
    EMSA_PSS_VERIFY(M, EM, modBits - 1)
}

//-////////////////////////////////////////////////////////////////////////
//- EMSA-PSS-ENCODE as defined in RFC 3447 section 9.1.1
//-////////////////////////////////////////////////////////////////////////

static function {:autoReq} EMSA_PSS_ENCODE(M:seq<int>, emBits:int, salt:seq<int>) : seq<int>
    requires IsByteSeq(M);
    requires |M| * 8 >= emBits;
    requires IsByteSeqOfLen(salt, sLen());
    requires DivideRoundingUp(emBits, 8) >= hLen() + sLen() + 2;
    requires 8 * DivideRoundingUp(emBits, 8) - emBits <= 8;
{
    var mHash := SHA256_BytesToBytes(M);
    var emLen := DivideRoundingUp(emBits, 8);
    var M' := RepeatDigit(0, 8) + mHash + salt;
    var H := SHA256_BytesToBytes(M');
    var PS := RepeatDigit(0, emLen - sLen() - hLen() - 2);
    var DB := PS + [0x01] + salt;
    var dbMask := MGF1(H, emLen - hLen() - 1);
    var maskedDB := ByteSeqXor(DB, dbMask);
    var nZeroBits := 8 * emLen - emBits;
    var maskedDB_reduced := ClearMSBs(maskedDB, nZeroBits);
    var EM := maskedDB_reduced + H + [0xbc];
    EM
}

//-////////////////////////////////////////////////////////////////////////
//- EMSA-PSS-VERIFY as defined in RFC 3447 section 9.1.2
//-////////////////////////////////////////////////////////////////////////

static predicate {:autoReq} EMSA_PSS_VERIFY(M:seq<int>, EM:seq<int>, emBits:int)
    requires IsByteSeq(EM);
    requires IsByteSeq(M);
{
    |M| < power2(61) &&
    var mHash := SHA256_BytesToBytes(M);
    var emLen := DivideRoundingUp(emBits, 8);
    emLen >= hLen() + sLen() + 2 &&
    |EM| >= emLen - 1 &&
    EM[|EM|-1] == 0xbc &&
    var maskedDB:seq<int> := EM[.. emLen - hLen() - 1];
    var H := EM[emLen - hLen() - 1 .. emLen - 1];
    var nZeroBits := 8*emLen - emBits;
    |maskedDB| > 0 &&
    8 - nZeroBits >= 0 &&
    maskedDB[0] < power2(8-nZeroBits) &&
    var dbMask := MGF1(H, emLen - hLen() - 1);
    var DB := ByteSeqXor(maskedDB, dbMask);
    var DB_reduced := ClearMSBs(DB, nZeroBits);
    |DB_reduced| > emLen - hLen() - sLen() - 2 &&
    DB_reduced[.. emLen - hLen() - sLen() - 2] == RepeatDigit(0, emLen - hLen() - sLen() - 2) &&
    DB_reduced[emLen - hLen() - sLen() - 2] == 0x01 &&
    |DB_reduced| >= sLen() &&
    var salt := DB_reduced[|DB_reduced| - sLen() ..];
    var M' := RepeatDigit(0, 8) + mHash + salt;
    var H' := SHA256_BytesToBytes(M');
    H == H'
}
