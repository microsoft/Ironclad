
include "../../Util/be_sequences.s.dfy"
include "RSASpec.s.dfy"

static function {:autoReq} rfc4251_word32_encoding(w:int) : seq<int>
{
    BEWordSeqToByteSeq([w])
}

static function {:autoReq} rfc4251_string_encoding(s:seq<int>) : seq<int>
    //- NB caller responsible to check that the result IsByteSeq().
{
    rfc4251_word32_encoding(|s|) + s
}

//- RFC4251 allows for encoding negative numbers two's-complement,
//- and thus mandates how we encode positive numbers that use the top bit.
static predicate rfc4251_positive_twoscomplement(s:seq<int>)
{
    (|s|==0
        || 0<s[0]<128
        || (s[0]==0 && |s|>1 && s[1]>=128))
}

//- Takes a normalized natural-valued seq<int> (left byte nonzero) and returns
//- an equivalently-valued rfc4251 twoscomplement number satisfying
//- rfc4251_positive_twoscomplement().
static function rfc4251_positive_to_twoscomplement(s:seq<int>) : seq<int>
{
    if |s|==0 || s[0]<128 then
        s
    else
        [0]+s
}

static function {:autoReq} rfc4251_mpint_encoding(v:nat) : seq<int>
{
    var tc := rfc4251_positive_to_twoscomplement(BEIntToByteSeq(v));
    rfc4251_word32_encoding(|tc|) + tc
}

static function method STR_SSH_RSA() : seq<int>
    //-ensures ByteSeq(STR_SSH_RSA())
{
    
    //- This sequence is the string "ssh-rsa"
    [115, 115, 104, 45, 114, 115, 97]
}

static function {:autoReq} rfc4251_sshrsa_encoding(e:nat, n:nat) : seq<int>
{
    rfc4251_string_encoding(STR_SSH_RSA())
        + rfc4251_mpint_encoding(e)
        + rfc4251_mpint_encoding(n)
}

static function {:autoReq} rfc4251_sshrsa_pubkey_encoding(key:RSAPubKeySpec) : seq<int>
    requires WellformedRSAPubKeySpec(key);
{
    rfc4251_sshrsa_encoding(key.e, key.n)
}
