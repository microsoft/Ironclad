//-<NuBuild BasmEnableSymdiff true />
include "PassHash.s.dfy"
include "../../Libraries/Util/relational.s.dfy"
include "../../Libraries/Util/repeat_digit.i.dfy"
include "../../Libraries/Crypto/Hash/sha256.i.dfy"
include "../../Drivers/TPM/tpm-wrapper.i.dfy"

//-////////////////////////////////////////////////////////////////////////
//- Implementing PassHashState with PassHashStateImpl
//-////////////////////////////////////////////////////////////////////////

datatype PassHashStateImpl = PassHashStateImplConstructor(secret:seq<int>);

static function PassHashStateImplToSpec(s:PassHashStateImpl):PassHashState
{
    PassHashStateConstructor(s.secret)
}

static predicate PassHashStateImplValid(s:PassHashStateImpl)
{
    IsByteSeq(s.secret) &&
    32 <= |s.secret| <= 2048
}

//-////////////////////////////////////////////////////////////////////////
//- Exported methods
//-////////////////////////////////////////////////////////////////////////

method PassHashInitialize() returns (passhash_state:PassHashStateImpl)
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM_satisfies_integrity_policy(TPM);

    ensures TPM_ready();
    ensures PassHashStateImplValid(passhash_state);
    ensures PassHashInitializeValid(PassHashStateImplToSpec(passhash_state), old(TPM), TPM);

    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_ready();
    ensures TPMs_match_except_for_randoms(TPM, old(TPM)[PCR_19 := TPM.PCR_19]);
    ensures TPM_valid(TPM);
    ensures IoMemPerm.Null?;
{
    lemma_2toX();
    establish_locality();
    var secret := get_random(32);
    passhash_state := PassHashStateImplConstructor(secret);
}

method{:dafnycc_conservative_seq_triggers} PassHashPerformHash (passhash_state:PassHashStateImpl, message:seq<int>, salt:seq<int>)
                                                               returns (error_code:int, passhash_hash:seq<int>)
    requires PassHashStateImplValid(passhash_state);
    requires IsByteSeq(message);
    requires IsByteSeq(salt);

    ensures Word32(error_code);
    ensures |passhash_hash| == 32;
    ensures IsByteSeq(passhash_hash);
    ensures error_code == 0 ==> |BEByteSeqToBitSeq_premium(passhash_state.secret + salt + message)| < power2(64);
    ensures PassHashPerformHashValid(PassHashStateImplToSpec(passhash_state), message, salt, error_code, passhash_hash);

    requires public(message);
    requires public(salt);
    ensures public(error_code);
{
    lemma_2toX();

    if !((|salt| + |message| + 2048) * 8 <= 0xFFFFFFFF) {
        error_code := 1;
        passhash_hash := RepeatDigit_impl(0, 32);
        return;
    }

    error_code := 0;

    var preimage := passhash_state.secret + salt + message;
    calc {
        |preimage| * 8;
        <= (|passhash_state.secret| + |salt| + |message|) * 8;
        <= (|salt| + |message| + 2048) * 8;
        <= 0xFFFFFFFF;
        < power2(32);
    }

    calc {
        |BEByteSeqToBitSeq_premium(preimage)|;
        == 8 * |preimage|;
        < power2(32);
        < { lemma_power2_strictly_increases(35, 64); }
          power2(64);
    }

    var hash := SHA256_impl_Bytes(preimage);
    passhash_hash := BEWordSeqToByteSeq_impl(hash);
}
