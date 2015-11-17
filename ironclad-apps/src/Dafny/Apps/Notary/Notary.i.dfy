//-<NuBuild BasmEnableSymdiff true />
include "Notary.s.dfy"
include "../../Libraries/Util/relational.s.dfy"
include "../../Libraries/BigNum/BigNum.i.dfy"
include "../../Libraries/BigNum/BigNatBitCount.i.dfy"
include "../../Libraries/Crypto/RSA/KeyGen.i.dfy"
include "../../Libraries/Crypto/RSA/RSA.i.dfy"
include "../../Libraries/Crypto/RSA/RSAOps.i.dfy"
include "../../Libraries/Crypto/RSA/rfc4251impl.i.dfy"
include "../Common/CommonState.i.dfy"

//- This method has problems verifying unless it's the first one in the file.

method {:timeLimitMultiplier 2} CreateNotaryStatement (new_counter_value:BigNat, message:seq<int>) returns (success:bool, notary_statement:seq<int>)
    requires WellformedBigNat(new_counter_value);
    requires ModestBigNatValue(new_counter_value);
    requires IsByteSeq(message);

    ensures I(new_counter_value) < power2(power2(34));
    ensures notary_statement == [34] + rfc4251_mpint_encoding_premium(I(new_counter_value)) + message;
    ensures success == (|notary_statement| <= 0xFFFFFF);
    ensures success ==> Word32(|rfc4251_positive_to_twoscomplement(BEIntToByteSeq(I(new_counter_value)))|) &&
                        IsByteSeq(notary_statement) && |notary_statement| < power2(28) && Word32(|notary_statement|) &&
                        notary_statement == NotaryCounterAdvanceStatement(I(new_counter_value), message);
{
    lemma_2toX();
    lemma_power2_add8(24);

    var counter_encoding := rfc4251_encode_mpint_legacy(new_counter_value);
    notary_statement := [34] + counter_encoding + message;
    success := |notary_statement| <= 0xFFFFFF;
    if !success {
        return;
    }

    Lemma_NotaryCounterAdvanceStatementValid(notary_statement, I(new_counter_value), message, counter_encoding);
    assert IsByte(34);
    assert IsByteSeq(notary_statement);
    assert |notary_statement| <= 0xFFFFFFF < power2(28);
    assert Word32(|rfc4251_positive_to_twoscomplement(BEIntToByteSeq(I(new_counter_value)))|);
    assert Word32(|notary_statement|);
    assert notary_statement == NotaryCounterAdvanceStatement(I(new_counter_value), message);
}

//-////////////////////////////////////////////////////////////////////////
//- Implementing NotaryState with NotaryStateImpl
//-////////////////////////////////////////////////////////////////////////

datatype NotaryStateImpl = NotaryStateImplConstructor(counter:BigNat);

static function NotaryStateImplToSpec(s:NotaryStateImpl):NotaryState
{
    NotaryStateConstructor(if WellformedBigNat(s.counter) then I(s.counter) else 0)
}

static predicate NotaryStateImplValid(notary_state:NotaryStateImpl)
{
    WellformedBigNat(notary_state.counter)
    && ModestBigNatValue(notary_state.counter)
}

//-////////////////////////////////////////////////////////////////////////
//- Lemmas
//-////////////////////////////////////////////////////////////////////////

lemma Lemma_NotaryCounterAdvanceStatementValid(statement:seq<int>, new_counter_value:nat, message:seq<int>, counter_encoding:seq<int>)
    requires IsByteSeq(message);
    requires new_counter_value < power2(power2(34));
    requires counter_encoding == rfc4251_mpint_encoding_premium(new_counter_value);
    requires statement == [34] + counter_encoding + message;
    ensures statement == NotaryCounterAdvanceStatement(new_counter_value, message);
{
}

//-////////////////////////////////////////////////////////////////////////
//- Exported methods
//-////////////////////////////////////////////////////////////////////////

method NotaryInitialize() returns (notary_state:NotaryStateImpl)
    ensures NotaryStateImplValid(notary_state);
    ensures NotaryInitializeValid(NotaryStateImplToSpec(notary_state));
    ensures public(NotaryStateImplToSpec(notary_state));
{
    var zero := MakeSmallLiteralBigNat(0);
    notary_state := NotaryStateImplConstructor(zero);
    assert NotaryStateImplToSpec(notary_state) == NotaryStateConstructor(0);
}

static predicate NotaryAdvanceCounterValid_premium(in_state:NotaryState, out_state:NotaryState, common_state:CommonState,
                                                   message_in:seq<int>, notary_statement_out:seq<int>, notary_attestation_out:seq<int>)
    requires WellformedRSAKeyPairSpec(common_state.key_pair);
    requires IsByteSeq(message_in);
    requires IsByteSeq(notary_statement_out);
    requires Word32(|notary_statement_out|);
    requires IsByteSeq(notary_attestation_out);
    requires Word32(|notary_attestation_out|);
    requires out_state.counter < KindaBigNat();
    requires RSASignatureRequires(common_state.key_pair, notary_statement_out);
{
    calc {
        out_state.counter;
        < KindaBigNat();
        == power2(power2(31));
        <= { lemma_power2_increases(31, 34); lemma_power2_increases(power2(31), power2(34)); }
           power2(power2(34));
    }
    assert IsByteSeq(rfc4251_mpint_encoding_premium(out_state.counter));
    assert IsDigitSeq(power2(32), [|rfc4251_positive_to_twoscomplement(BEIntToByteSeq(out_state.counter))|]);
    NotaryAdvanceCounterValid(in_state, out_state, common_state, message_in, notary_statement_out, notary_attestation_out)
}

method AddOneAndRemainModest (n:BigNat) returns (success:bool, nPlusOne:BigNat)
    requires WellformedBigNat(n);

    ensures WellformedBigNat(nPlusOne);
    ensures I(nPlusOne) == I(n) + 1;
    ensures success == (WellformedBigNat(nPlusOne) && I(nPlusOne) < KindaBigNat());
{
    lemma_2toX();

    var one := MakeSmallLiteralBigNat(1);
    nPlusOne := BigNatAdd(n, one);
    success := IsModestBigNat(nPlusOne);
}

method{:dafnycc_conservative_seq_triggers} NotaryAdvanceCounter (in_state:NotaryStateImpl, common_state:CommonStateImpl, message:seq<int>)
                             returns (out_state:NotaryStateImpl, error_code:int, notary_statement:seq<int>, notary_attestation:seq<int>)
    requires NotaryStateImplValid(in_state);
    requires CommonStateImplValid(common_state);
    requires common_state.key_pair.pub.size >= 1024 / 8;
    requires IsByteSeq(message);
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_ready();
    ensures old(TPM)==TPM;
    ensures NotaryStateImplValid(out_state);
    ensures Word32(error_code);
    ensures Word32(|notary_statement|);
    ensures Word32(|notary_attestation|);
    ensures IsByteSeq(notary_statement);
    ensures IsByteSeq(notary_attestation);
    ensures error_code == 0 ==> RSASignatureRequires(CommonStateImplToSpec(common_state).key_pair, notary_statement) &&
                                NotaryAdvanceCounterValid_premium(NotaryStateImplToSpec(in_state), NotaryStateImplToSpec(out_state),
                                                                  CommonStateImplToSpec(common_state), message, notary_statement,
                                                                  notary_attestation);
    ensures error_code != 0 ==> out_state == in_state && notary_statement == [] && notary_attestation == [];
    requires public(NotaryStateImplToSpec(in_state));
    requires public(message);
    ensures public(NotaryStateImplToSpec(out_state));
    ensures public(error_code);
    ensures public(notary_statement);
{
    lemma_2toX();

    var success, new_counter_value := AddOneAndRemainModest(in_state.counter);
    if !success {
        error_code := 1;
        out_state := in_state;
        notary_statement := [];
        notary_attestation := [];
        return;
    }

    success, notary_statement := CreateNotaryStatement(new_counter_value, message);
    if !success {
        error_code := 2;
        out_state := in_state;
        notary_statement := [];
        notary_attestation := [];
        return;
    }

    assert old(TPM)==TPM;
    notary_attestation := DigestedSign(common_state.key_pair, notary_statement);
    assert old(TPM)==TPM;

    error_code := 0;
    out_state := NotaryStateImplConstructor(new_counter_value);

    assert NotaryStateImplToSpec(out_state) == NotaryStateConstructor(I(new_counter_value));
    assert notary_statement == NotaryCounterAdvanceStatement(NotaryStateImplToSpec(out_state).counter, message);
}
