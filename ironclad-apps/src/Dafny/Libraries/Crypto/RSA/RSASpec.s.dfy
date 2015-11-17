include "../Hash/Digest.s.dfy"
include "../../Math/power.s.dfy"
include "MillerRabin.s.dfy"
include "../../Math/GCD.s.dfy"
include "KeyGen.s.dfy"

datatype PadMode = PadModeEncrypt() | PadModeSign();

static function method BlockType(pad_mode:PadMode) : int
{
    if (pad_mode.PadModeSign?) then 1 else 2
}

static function method SignaturePadByte() : int { 0xff }

static predicate PaddedMessageStartIndex(padded_msg:seq<int>, i:nat, pad_mode:PadMode, padding:seq<int>)
{
    IsByteSeq(padded_msg)
    && 0 < i <= |padded_msg|
    && 2 <= |padded_msg|
    && IsByteSeq(padding)
    && (forall j :: 0 <= j < |padding| ==> padding[j]!=0)
    && padded_msg[0]==0
    && padded_msg[1]==BlockType(pad_mode)
    && 2<i
    && padded_msg[2..i-1] == padding
    && padded_msg[i-1]==0
}

static predicate PKCS15_PaddingRelationWith(padded_msg:seq<int>, msg:seq<int>, pad_mode:PadMode, padding:seq<int>)
    requires IsByteSeq(padded_msg);
    requires IsByteSeq(msg);
{
    |padding| >= 8
    && PaddedMessageStartIndex(padded_msg, |padding|+3, pad_mode, padding)
    && padded_msg[|padding|+3..] == msg
}

static predicate PKCS15_PaddingRelation(padded_msg:seq<int>, msg:seq<int>, pad_mode:PadMode)
    requires IsByteSeq(padded_msg);    
    requires IsByteSeq(msg);
{
    exists padding:seq<int> :: PKCS15_PaddingRelationWith(padded_msg, msg, pad_mode, padding)
}

static function PadCount(msg:seq<int>, k:nat) : int
    { k - 3 - |msg| }

static predicate NonzeroPad(padding:seq<int>)
{
    forall i :: 0 <= i < |padding| ==> padding[i] != 0
}






static function PKCS15_EncryptionPad(msg:seq<int>, k:nat, padding:seq<int>) : seq<int>
    requires IsByteSeq(msg);
    requires IsByteSeq(padding);
    requires |padding| == PadCount(msg, k);
    requires NonzeroPad(padding);
    requires PadCount(msg, k) >= 8;
    //- lemma proves PKCS15_PaddingRelation(PKCS15_EncryptionPad(msg), msg, PadModeEncrypt())
{
    [0, BlockType(PadModeEncrypt())] + padding + [0] + msg
}

static function PKCS15_SignaturePad(msg:seq<int>, k:nat) : seq<int>
    requires IsByteSeq(msg);
    requires PadCount(msg, k) >= 8;
    //- lemma proves PKCS15_PaddingRelation(PKCS15_SignaturePad(msg), msg, PadModeSign())
{
    [0, BlockType(PadModeSign())] + RepeatDigit(SignaturePadByte(), PadCount(msg,k)) + [0] + msg
}

datatype RSAPubKeySpec = RSAPublicKeySpec_c(
    n:nat,    //- modulus
    size:nat,
    e:nat    //- public key exponent
    );

static predicate KeyModulusMatchesSizeInBytes(n:nat, k:nat)
{
    (k>0 ==> power2(8*(k-1)) <= n)
    && n < power2(8*k)
}

static predicate WellformedRSAPubKeySpec(pubkey:RSAPubKeySpec)
{
    0 < pubkey.n
    && KeyModulusMatchesSizeInBytes(pubkey.n, pubkey.size)
}

datatype RSAKeyPairSpec = RSAKeyPairSpec_c(
    pub:RSAPubKeySpec,
    d:nat    //- private key exponent
    );

static predicate WellformedRSAKeyPairSpec(key:RSAKeyPairSpec)
{
    WellformedRSAPubKeySpec(key.pub)
}

static function {:autoReq} RSAEncryption(pubkey:RSAPubKeySpec, msg:seq<int>, padding:seq<int>) : seq<int>
    requires WellformedRSAPubKeySpec(pubkey);
{
    var pad_msg :=
        BEByteSeqToInt(PKCS15_EncryptionPad(msg, pubkey.size, padding));

    BEIntToByteSeq(power(pad_msg, pubkey.e) % pubkey.n)
}

//- predicate form is appropriate here, where we don't actually know
//- the value of the padding (and can't, until it's decrypted!)

static predicate {:autoReq} RSADecryptionRelation(key:RSAKeyPairSpec, ciphertext:seq<int>, msg:seq<int>)
{
    var cipher_n := BEByteSeqToInt(ciphertext);

    WellformedRSAKeyPairSpec(key)
    && cipher_n < key.pub.n //- Decrypter MUST ignore aliased ciphertexts.
    && exists padding:seq<int> :: (
        var padded_msg_n := BEByteSeqToInt(PKCS15_EncryptionPad(msg, key.pub.size, padding));
        power(cipher_n, key.d) % key.pub.n == padded_msg_n)
}

static function {:autoReq} RSASignature(key:RSAKeyPairSpec, message:seq<int>) : seq<int>
    requires WellformedRSAKeyPairSpec(key);
{
    var padded_nint := BEByteSeqToInt(PKCS15_SignaturePad(SHA256Digest(message), key.pub.size));
    BEIntToDigitSeq(power2(8), key.pub.size, power(padded_nint, key.d) % key.pub.n)
}

//- predicate form is appropriate here, because that's the actual output.

static predicate {:autoReq} RSAVerificationRelation(pubkey:RSAPubKeySpec, message:seq<int>, signature:seq<int>)
{
    var sig_n := BEByteSeqToInt(signature);
    var padded_msg_n := BEByteSeqToInt(PKCS15_SignaturePad(SHA256Digest(message), pubkey.size));

    WellformedRSAPubKeySpec(pubkey)
    && sig_n != 0
    && |signature| == pubkey.size
    && sig_n < pubkey.n //- disallow "alias" signatures (sig_n + k * pubkey.n)
    && power(sig_n, pubkey.e) % pubkey.n == padded_msg_n
}

//-////////////////////////////////////////////////////////////////////////////
//------------------------------------------------------------//

datatype RSAKeyGenerationWorksheetRow = RSAKeyGenerationWorksheetRow_c(
    P:PrimeGenerationWorksheet,
    Q:PrimeGenerationWorksheet,
    accepted:bool,
    randoms:seq<int>);

static function RSA_public_exponent() : int { 65537 }

static predicate {:autoReq} RSAKeyAccepted(row:RSAKeyGenerationWorksheetRow)
{
    var phi_n := (PrimeGenerationOutput(row.P)-1) * (PrimeGenerationOutput(row.Q)-1);
    if (phi_n < 0) then
        false   //- case shouldn't occur, but don't want to prove that here.
    else
        is_gcd(phi_n, RSA_public_exponent(), 1)
}

static predicate {:autoReq} RSAKeyGenerationWorksheetRowValid(keybits:int, row:RSAKeyGenerationWorksheetRow)
{
    var halfbits := keybits/2 + 2;
    PrimeGenerationWorksheetValid(halfbits, row.P)
    && PrimeGenerationWorksheetValid(halfbits, row.Q)
    && row.accepted == RSAKeyAccepted(row)
    && row.randoms == row.P.randoms + row.Q.randoms
}

//------------------------------------------------------------//

datatype RSAKeyGenerationWorksheet = RSAKeyGenerationWorksheet_c(
    keybits:int,
    rows:seq<RSAKeyGenerationWorksheetRow>,
    randoms:seq<int>,
    p:int,
    q:int,
    phi:int,
    n:int
    );

static function RSAKeyGenerationWorksheetConsumesRandoms(rows:seq<RSAKeyGenerationWorksheetRow>) : seq<int>
{
    if (rows==[]) then
        []
    else
        RSAKeyGenerationWorksheetConsumesRandoms(rows[..|rows|-1]) + rows[|rows|-1].randoms
}

static predicate RSAKeyGenerationWorksheetSummaryValid(worksheet:RSAKeyGenerationWorksheet)
    requires 0 < |worksheet.rows|;
{
    var final := worksheet.rows[|worksheet.rows|-1];
    worksheet.rows[|worksheet.rows|-1].accepted
    && 0 < |final.P.rows|
    && worksheet.p == PrimeGenerationOutput(final.P)
    && 0 < |final.Q.rows|
    && worksheet.q == PrimeGenerationOutput(final.Q)
    && worksheet.phi == (worksheet.p-1)*(worksheet.q-1)
    && worksheet.phi != 0
    && worksheet.n == worksheet.p*worksheet.q
}

static predicate {:autoReq} RSAKeyGenerationWorksheetValid(keybits:int, worksheet:RSAKeyGenerationWorksheet)
{
    worksheet.keybits == keybits
    && (forall i :: 0 <= i < |worksheet.rows| ==> RSAKeyGenerationWorksheetRowValid(worksheet.keybits, worksheet.rows[i]))
    && (forall i :: 0 <= i < |worksheet.rows|-1 ==> !worksheet.rows[i].accepted)
    && RSAKeyGenerationWorksheetConsumesRandoms(worksheet.rows) == worksheet.randoms
    && 0<|worksheet.rows|
    && RSAKeyGenerationWorksheetSummaryValid(worksheet)
}

static predicate {:autoReq} RSAKeyConsistentWithWorksheet(requested_keybits:int, key:RSAKeyPairSpec, worksheet:RSAKeyGenerationWorksheet)
{
    WellformedRSAKeyPairSpec(key)
    && RSAKeyGenerationWorksheetValid(requested_keybits, worksheet)
    && key.pub.n == worksheet.p * worksheet.q
    && key.pub.e == RSA_public_exponent()
    && key.pub.size >= requested_keybits / 8
    && (key.d * key.pub.e) % worksheet.phi == 1
}

static predicate {:autoReq} RSAKeyGenerationValid(requested_keybits:int, key:RSAKeyPairSpec, randoms:seq<int>)
{
    exists worksheet:RSAKeyGenerationWorksheet ::
        RSAKeyConsistentWithWorksheet(requested_keybits, key, worksheet) && worksheet.randoms == randoms
}
