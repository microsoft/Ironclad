include "../../Math/power.s.dfy"
include "../../Math/round.s.dfy"
include "../../Util/be_sequences.s.dfy"
include "../../../Drivers/TPM/tpm-device.s.dfy"
include "RSASpec.s.dfy"

//-
//- The spec in this file is based on RFC 3447, which can be found at
//- http://www.ietf.org/rfc/rfc3447.txt
//-

//-////////////////////////////////////////////////////////////////////////
//- High-level functions for external use
//-////////////////////////////////////////////////////////////////////////

datatype OAEPDecryptionResult = OAEPDecryptionResult_Success(M:seq<int>) |
                                OAEPDecryptionResult_Undecryptable();

static predicate {:autoReq} OAEPEncryptionRelation(pubkey:RSAPubKeySpec, M:seq<int>, EM:seq<int>, old_TPM:TPM_struct, new_TPM:TPM_struct)
{
    new_TPM.random_index - old_TPM.random_index == hLen() &&
    EM == RSAES_OAEP_ENCRYPT(pubkey, M, [] /* use empty string as label */, TPM_random_bytes(old_TPM.random_index, new_TPM.random_index))
}

static predicate {:autoReq} OAEPDecryptionRelation(key:RSAKeyPairSpec, C:seq<int>, decryption_result:OAEPDecryptionResult)
{
    RSAES_OAEP_DECRYPT(key, C, [] /* use empty string as label */) == decryption_result
}

//-////////////////////////////////////////////////////////////////////////
//- Helper functions
//-////////////////////////////////////////////////////////////////////////

static function {:autoReq} SHA256_BytesToBytes(M:seq<int>) : seq<int>
    requires IsByteSeq(M);
{
    BEWordSeqToByteSeq(SHA256(BEByteSeqToBitSeq(M)))
}

static function ByteSeqXor(X:seq<int>, Y:seq<int>) : seq<int>
    requires IsByteSeq(X);
    requires IsByteSeq(Y);
{
    if X == [] || Y == [] then
        []
    else if Word32(X[0]) && Word32(Y[0]) then
        [BitwiseXor(X[0], Y[0])] + ByteSeqXor(X[1..], Y[1..])
    else
        [0] + ByteSeqXor(X[1..], Y[1..])
}

static function FindFirstNonzeroByte(s:seq<int>, minpos:nat) : int
    ensures FindFirstNonzeroByte(s, minpos) >= minpos;
    decreases |s| - minpos;
{
    if minpos >= |s| || s[minpos] != 0 then
        minpos
    else
        FindFirstNonzeroByte(s, minpos + 1)
}

//-////////////////////////////////////////////////////////////////////////
//- Definitions from RFC 3447 section 2
//-////////////////////////////////////////////////////////////////////////

static function hLen() : int
{
    32  
}

static function sLen() : int
{
    hLen()
}

//-////////////////////////////////////////////////////////////////////////
//- I2OSP, OS2IP as defined in RFC 3447 section 4.1
//-////////////////////////////////////////////////////////////////////////

static function I2OSP(x:int, xLen:int) : seq<int>
    requires 0 <= xLen;
    requires 0 <= x < power(power2(8), xLen);
{
    BEIntToDigitSeq(power2(8), xLen, x)
}

static function OS2IP(X:seq<int>) : int
    requires IsByteSeq(X);
{
    BEByteSeqToInt(X)
}

//-////////////////////////////////////////////////////////////////////////
//- RSAEP, RSADP as defined in RFC 3447 section 5.1
//-////////////////////////////////////////////////////////////////////////

static function RSAEP(pubkey:RSAPubKeySpec, m:int) : int
    requires WellformedRSAPubKeySpec(pubkey);
    requires 0 <= m < pubkey.n;
{
    power(m, pubkey.e) % pubkey.n
}

static function RSADP(keypair:RSAKeyPairSpec, c:int) : int
    requires WellformedRSAKeyPairSpec(keypair);
    requires 0 <= c < keypair.pub.n;
{
    power(c, keypair.d) % keypair.pub.n
}

//-////////////////////////////////////////////////////////////////////////
//- RSASP1 as defined in RFC 3447 section 5.2
//-////////////////////////////////////////////////////////////////////////

static function RSASP1(key:RSAKeyPairSpec, m:int) : int
    requires WellformedRSAKeyPairSpec(key);
    requires 0 <= m < key.pub.n;
{
    power(m, key.d) % key.pub.n
}

//-////////////////////////////////////////////////////////////////////////
//- MGF1 as defined in RFC 3447 section B.2.1
//-////////////////////////////////////////////////////////////////////////

static predicate MGF1_step_requirements(seed:seq<int>, counter:nat)
{
       0 <= counter < power(power2(8), 4)
    && IsByteSeq(seed)
    && IsByteSeq(I2OSP(counter, 4))
    && IsBitSeq(BEByteSeqToBitSeq(seed + I2OSP(counter, 4)))
    && |BEByteSeqToBitSeq(seed + I2OSP(counter, 4))| < power2(64)
}

static function MGF1_step(seed:seq<int>, counter:nat) : seq<int>
    requires MGF1_step_requirements(seed, counter);
{
    var C := I2OSP(counter, 4);
    SHA256_BytesToBytes(seed + C)
}

static function MGF1_prefix(seed:seq<int>, counter:nat) : seq<int>
    requires forall j :: 0 <= j < counter ==> MGF1_step_requirements(seed, j);
    decreases counter;
{
    if counter == 0 then [] else MGF1_prefix(seed, counter-1) + MGF1_step(seed, counter-1)
}

static function MGF1(seed:seq<int>, maskLen:int) : seq<int>
    requires 0 <= maskLen <= power2(32) * hLen();
    requires var counter := DivideRoundingUp(maskLen, hLen());
             counter >= 0 &&
             (forall j :: 0 <= j < counter ==> MGF1_step_requirements(seed, j)) &&
             |MGF1_prefix(seed, counter)| >= maskLen;
{
    MGF1_prefix(seed, DivideRoundingUp(maskLen, hLen()))[..maskLen]
}

//-////////////////////////////////////////////////////////////////////////
//- RSAES_OAEP_ENCRYPT as defined in RFC 3447 section 7.1.1
//-////////////////////////////////////////////////////////////////////////

static function {:autoReq} RSAES_OAEP_ENCRYPT(pubkey:RSAPubKeySpec, M:seq<int>, L:seq<int>, seed:seq<int>) : seq<int>
    requires WellformedRSAPubKeySpec(pubkey);
    requires IsByteSeq(M);
    requires IsByteSeq(L);
    requires IsByteSeq(seed);
    requires |M| <= pubkey.size - 2 * hLen() - 2;
    requires |seed| == hLen();
{
    var lHash := SHA256_BytesToBytes(L);
    var k := pubkey.size;
    var PS := RepeatDigit(0, k - |M| - 2*hLen() - 2);
    var DB := lHash + PS + [0x01] + M;
    var dbMask := MGF1(seed, k - hLen() - 1);
    var maskedDB := ByteSeqXor(DB, dbMask);
    var seedMask := MGF1(maskedDB, hLen());
    var maskedSeed := ByteSeqXor(seed, seedMask);
    var EM := [0x00] + maskedSeed + maskedDB;
    var m := OS2IP(EM);
    var c := RSAEP(pubkey, m);
    var C := I2OSP(c, k);
    C
}

//-////////////////////////////////////////////////////////////////////////
//- RSAES-OAEP-DECRYPT as defined in RFC 3447 section 7.1.2
//-////////////////////////////////////////////////////////////////////////

static function {:autoReq} RSAES_OAEP_DECRYPT(key:RSAKeyPairSpec, C:seq<int>, L:seq<int>) : OAEPDecryptionResult
    requires WellformedRSAKeyPairSpec(key);
    requires IsByteSeq(C);
    requires IsByteSeq(L);
{
    var k := key.pub.size;
    if |C| != k || k < 2*hLen() + 2 then
        OAEPDecryptionResult_Undecryptable()
    else
        var c := OS2IP(C);
        var m := RSADP(key, c);
        var EM := I2OSP(m, k);
        var lHash := SHA256_BytesToBytes(L);
        if |EM| != k then
            OAEPDecryptionResult_Undecryptable()
        else
            var Y := EM[0];
            var maskedSeed := EM[1..hLen()+1];
            var maskedDB := EM[hLen()+1..k];
            var seedMask := MGF1(maskedDB, hLen());
            var seed := ByteSeqXor(maskedSeed, seedMask);
            var dbMask := MGF1(seed, k - hLen() - 1);
            var DB := ByteSeqXor(maskedDB, dbMask);
            if |DB| < hLen() then
                OAEPDecryptionResult_Undecryptable()
            else
                var lHash' := DB[..hLen()];
                var firstNonZero := FindFirstNonzeroByte(DB, hLen());
                if lHash' != lHash || firstNonZero >= |DB| || DB[firstNonZero] != 0x01 || Y != 0 then
                    OAEPDecryptionResult_Undecryptable()
                else
                    OAEPDecryptionResult_Success(DB[firstNonZero+1..])
}
