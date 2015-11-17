//-<NuBuild BasmEnableSymdiff true />
include "TrInc.s.dfy"
include "../../Libraries/Util/relational.s.dfy"
include "../../Libraries/BigNum/BigNum.i.dfy"
include "../../Libraries/BigNum/BigNatBitCount.i.dfy"
include "../../Libraries/Crypto/RSA/KeyGen.i.dfy"
include "../../Libraries/Crypto/RSA/RSA.i.dfy"
include "../../Libraries/Crypto/RSA/RSAOps.i.dfy"
include "../../Libraries/Crypto/RSA/rfc4251decode.i.dfy"
include "../Common/CommonState.i.dfy"

//-////////////////////////////////////////////////////////////////////////
//- Implementing TrIncCounter with TrIncCounterImpl
//-////////////////////////////////////////////////////////////////////////

datatype TrIncCounterImpl = TrIncCounterImpl_c(public_key:RSAPubKeyImpl, counter_value:BigNat);

predicate TrIncCounterImplValid (c:TrIncCounterImpl)
{
    WellformedBigNat(c.counter_value) &&
    ModestBigNatValue(c.counter_value) &&
    WellformedRSAPubKeyImpl(c.public_key) &&
    WellformedRSAPubKeySpec(PubKeyImplToSpec(c.public_key)) &&
    RSA_DIGEST_MIN_KEY_SIZE() <= PubKeyImplToSpec(c.public_key).size < power2(60)
}

predicate TrIncCounterImplSeqValid (s:seq<TrIncCounterImpl>)
{
    forall i :: 0 <= i < |s| ==> TrIncCounterImplValid(s[i])
}

function TrIncCounterImplToSpec (c:TrIncCounterImpl) : TrIncCounter
    requires TrIncCounterImplValid(c);
{
    TrIncCounterConstructor(PubKeyImplToSpec(c.public_key), I(c.counter_value))
}

function TrIncCounterImplSeqToSpec (s:seq<TrIncCounterImpl>) : seq<TrIncCounter>
    requires TrIncCounterImplSeqValid(s);
{
    if |s| == 0 then
        []
    else
        TrIncCounterImplSeqToSpec(s[..|s|-1]) + [TrIncCounterImplToSpec(s[|s|-1])]
}

lemma Lemma_TrIncCounterImplSeqToSpecRelation (s_impl:seq<TrIncCounterImpl>, s_spec:seq<TrIncCounter>)
    requires TrIncCounterImplSeqValid(s_impl);
    requires s_spec == TrIncCounterImplSeqToSpec(s_impl);
    ensures |s_spec| == |s_impl|;
    ensures forall i :: 0 <= i < |s_spec| ==> s_spec[i] == TrIncCounterImplToSpec(s_impl[i]);
    ensures forall i :: 0 <= i < |s_spec| ==> s_spec[i].public_key == PubKeyImplToSpec(s_impl[i].public_key);
    ensures forall i :: 0 <= i < |s_spec| ==> s_spec[i].counter_value == I(s_impl[i].counter_value);
    decreases |s_impl|;
{
    if |s_impl| > 0 {
        assert s_spec == TrIncCounterImplSeqToSpec(s_impl[..|s_impl|-1]) + [TrIncCounterImplToSpec(s_impl[|s_impl|-1])];
        assert s_spec[|s_spec|-1] == TrIncCounterImplToSpec(s_impl[|s_impl|-1]);
        Lemma_TrIncCounterImplSeqToSpecRelation(s_impl[..|s_impl|-1], s_spec[..|s_spec|-1]);
        assert forall i :: 0 <= i < |s_spec|-1 ==> s_spec[i] == TrIncCounterImplToSpec(s_impl[i]);
    }
}

lemma Lemma_TrIncCounterImplSeqToSpecOfOne(c:TrIncCounterImpl)
    requires TrIncCounterImplValid(c);
    ensures TrIncCounterImplSeqToSpec([c]) == [TrIncCounterImplToSpec(c)];
{
    calc {
        TrIncCounterImplSeqToSpec([c]);
        TrIncCounterImplSeqToSpec([c][..|[c]|-1]) + [TrIncCounterImplToSpec([c][|[c]|-1])];
        TrIncCounterImplSeqToSpec([c][..0]) + [TrIncCounterImplToSpec([c][|[c]|-1])];
        TrIncCounterImplSeqToSpec([]) + [TrIncCounterImplToSpec([c][|[c]|-1])];
        [] + [TrIncCounterImplToSpec([c][|[c]|-1])];
        [TrIncCounterImplToSpec([c][|[c]|-1])];
        [TrIncCounterImplToSpec([c][0])];
        [TrIncCounterImplToSpec(c)];
    }
}

lemma Lemma_IndexIntoSequenceConcatenation(s1:seq<TrIncCounter>, s2:seq<TrIncCounter>, i:int)
    requires |s1| <= i < |s1| + |s2|;
    ensures (s1+s2)[i] == s2[i - |s1|];
{
}

lemma Lemma_TrIncCounterImplSeqToSpecConcatenation (s1:seq<TrIncCounterImpl>, s2:seq<TrIncCounterImpl>)
    requires TrIncCounterImplSeqValid(s1);
    requires TrIncCounterImplSeqValid(s2);
    ensures TrIncCounterImplSeqToSpec(s1+s2) == TrIncCounterImplSeqToSpec(s1) + TrIncCounterImplSeqToSpec(s2);
{
    ghost var s12 := s1 + s2;
    ghost var s1_spec := TrIncCounterImplSeqToSpec(s1);
    ghost var s2_spec := TrIncCounterImplSeqToSpec(s2);
    ghost var s12_spec := TrIncCounterImplSeqToSpec(s1+s2);
    ghost var s1_spec_s2_spec := s1_spec + s2_spec;

    Lemma_TrIncCounterImplSeqToSpecRelation(s1, s1_spec);
    Lemma_TrIncCounterImplSeqToSpecRelation(s2, s2_spec);
    Lemma_TrIncCounterImplSeqToSpecRelation(s12, s12_spec);

    forall i | 0 <= i < |s1|
        ensures s1_spec_s2_spec[i] == s12_spec[i];
    {
        calc {
            s1_spec_s2_spec[i];
            s1_spec[i];
            s12_spec[i];
        }
    }

    forall i | |s1| <= i < |s1|+|s2|
        ensures s1_spec_s2_spec[i] == s12_spec[i];
    {
        calc {
            s1_spec_s2_spec[i];
            (s1_spec + s2_spec)[i];
            { Lemma_IndexIntoSequenceConcatenation(s1_spec, s2_spec, i); }
            s2_spec[i - |s1_spec|];
            s2_spec[i - |s1|];
            {
                Lemma_TrIncCounterImplSeqToSpecRelation(s1, s1_spec);
                Lemma_TrIncCounterImplSeqToSpecRelation(s2, s2_spec);
                Lemma_TrIncCounterImplSeqToSpecRelation(s12, s12_spec);
            }
            s12_spec[i];
        }
    }
}

//-////////////////////////////////////////////////////////////////////////
//- Implementing TrIncState with TrIncStateImpl
//-////////////////////////////////////////////////////////////////////////

datatype TrIncStateImpl = TrIncStateImpl_c(counters:seq<TrIncCounterImpl>);

predicate TrIncStateImplValid (trinc_state:TrIncStateImpl)
{
    Word32(|trinc_state.counters|)
    && TrIncCounterImplSeqValid(trinc_state.counters)
}

function TrIncStateImplToSpec (s:TrIncStateImpl) : TrIncState
    requires TrIncStateImplValid(s);
{
    TrIncStateConstructor(TrIncCounterImplSeqToSpec(s.counters))
}

lemma Lemma_TrIncStateImplToSpecRelation (s_impl:TrIncStateImpl, s_spec:TrIncState)
    requires TrIncStateImplValid(s_impl);
    requires s_spec == TrIncStateImplToSpec(s_impl);
    ensures |s_spec.counters| == |s_impl.counters|;
    ensures forall i :: 0 <= i < |s_spec.counters| ==> s_spec.counters[i] == TrIncCounterImplToSpec(s_impl.counters[i]);
{
    Lemma_TrIncCounterImplSeqToSpecRelation(s_impl.counters, s_spec.counters);
}

lemma Lemma_TrIncStateImplValidImpliesTrIncStateValid (trinc_state:TrIncStateImpl)
    requires TrIncStateImplValid(trinc_state);
    ensures TrIncStateValid(TrIncStateImplToSpec(trinc_state));
{
    Lemma_TrIncStateImplToSpecRelation(trinc_state, TrIncStateImplToSpec(trinc_state));
}

lemma Lemma_ConvertStateCounterImpl (state:TrIncStateImpl, i:int)
    requires TrIncStateImplValid(state);
    requires 0 <= i < |state.counters|;
    ensures |TrIncStateImplToSpec(state).counters| == |state.counters|;
    ensures TrIncCounterImplToSpec(state.counters[i]) == TrIncStateImplToSpec(state).counters[i];
{
    Lemma_TrIncStateImplToSpecRelation(state, TrIncStateImplToSpec(state));
}

lemma Lemma_SplittingOffHeadOfCounterSequence (s:seq<TrIncCounter>, left:int, right:int)
    requires 0 <= left < right <= |s|;
    ensures s[left..right] == [s[left]] + s[left+1..right];
{
}

lemma Lemma_SplittingOffHeadOfTrIncCounterImplSequence (s:seq<TrIncCounterImpl>, left:int, right:int)
    requires 0 <= left < right <= |s|;
    ensures s[left..right] == [s[left]] + s[left+1..right];
{
}

lemma Lemma_ConvertStateCounterImplSeqSubset (state:TrIncStateImpl, left:int, right:int)
    requires TrIncStateImplValid(state);
    requires 0 <= left <= right <= |state.counters|;
    ensures |TrIncStateImplToSpec(state).counters| == |state.counters|;
    ensures TrIncCounterImplSeqToSpec(state.counters[left..right]) == TrIncStateImplToSpec(state).counters[left..right];
    decreases right - left;
{
    ghost var state_spec := TrIncStateImplToSpec(state);
    Lemma_TrIncStateImplToSpecRelation(state, state_spec);
    if left < right {
        calc {
            TrIncCounterImplSeqToSpec(state.counters[left..right]);
            { Lemma_SplittingOffHeadOfTrIncCounterImplSequence(state.counters, left, right);
              Lemma_TrIncCounterImplSeqToSpecConcatenation([state.counters[left]], state.counters[left+1..right]); }
            TrIncCounterImplSeqToSpec([state.counters[left]] + state.counters[left+1..right]);
            { Lemma_TrIncCounterImplSeqToSpecConcatenation([state.counters[left]], state.counters[left+1..right]); }
            TrIncCounterImplSeqToSpec([state.counters[left]]) + TrIncCounterImplSeqToSpec(state.counters[left+1..right]);
            {  Lemma_ConvertStateCounterImplSeqSubset(state, left+1, right); }
            TrIncCounterImplSeqToSpec([state.counters[left]]) + state_spec.counters[left+1..right];
            { Lemma_TrIncCounterImplSeqToSpecOfOne(state.counters[left]); }
            [TrIncCounterImplToSpec(state.counters[left])] + state_spec.counters[left+1..right];
            { Lemma_ConvertStateCounterImpl(state, left); }
            [state_spec.counters[left]] + state_spec.counters[left+1..right];
            { Lemma_SplittingOffHeadOfCounterSequence(state_spec.counters, left, right); }
            state_spec.counters[left..right];
        }
    }
}

//-////////////////////////////////////////////////////////////////////////
//- Lemmas
//-////////////////////////////////////////////////////////////////////////

lemma Lemma_UpdatingStateEnsuresProperUpdatesToSpec (in_state:TrIncStateImpl, out_state:TrIncStateImpl,
                                                     in_state_spec:TrIncState, out_state_spec:TrIncState,
                                                     counter_index:nat, new_counter_value:BigNat)
    requires TrIncStateImplValid(in_state);
    requires in_state_spec == TrIncStateImplToSpec(in_state);
    requires TrIncStateImplValid(out_state);
    requires out_state_spec == TrIncStateImplToSpec(out_state);
    requires |in_state_spec.counters| == |in_state.counters|;
    requires 0 <= counter_index < |in_state.counters|;
    requires WellformedBigNat(new_counter_value);
    requires |out_state.counters| == |in_state.counters|;
    requires forall i :: 0 <= i < |in_state.counters| && i != counter_index ==> out_state.counters[i] == in_state.counters[i];
    requires out_state.counters[counter_index].public_key == in_state.counters[counter_index].public_key;
    requires out_state.counters[counter_index].counter_value == new_counter_value;

    ensures |in_state_spec.counters| == |out_state_spec.counters|;
    ensures forall i :: 0 <= i < |in_state.counters| && i != counter_index ==> out_state_spec.counters[i] == in_state_spec.counters[i];
    ensures out_state_spec.counters[counter_index].public_key == in_state_spec.counters[counter_index].public_key;
    ensures out_state_spec.counters[counter_index].counter_value == I(new_counter_value);
    ensures TrIncStateImplValid(out_state);
{
    Lemma_TrIncStateImplToSpecRelation(in_state, in_state_spec);
    Lemma_TrIncStateImplToSpecRelation(out_state, out_state_spec);
}

lemma Lemma_TrIncCounterAdvanceStatementValid (statement:seq<int>, counter_index:nat, old_counter_value:nat, new_counter_value:nat,
                                               counter_index_encoding:seq<int>, old_counter_value_encoding:seq<int>,
                                               new_counter_value_encoding:seq<int>, message:seq<int>)
    requires IsByteSeq(message);
    requires Word32(counter_index);
    requires old_counter_value < power2(power2(34));
    requires new_counter_value < power2(power2(34));
    requires counter_index_encoding == rfc4251_word32_encoding(counter_index);
    requires old_counter_value_encoding == rfc4251_mpint_encoding_premium(old_counter_value);
    requires new_counter_value_encoding == rfc4251_mpint_encoding_premium(new_counter_value);
    requires statement == [34] + counter_index_encoding + old_counter_value_encoding + new_counter_value_encoding + message;
    ensures statement == TrIncCounterAdvanceStatement(counter_index, old_counter_value, new_counter_value, message);
    ensures IsByteSeq(statement);
{
    lemma_2toX();
    reveal_power2();
    assert IsByte(34);
    assert counter_index_encoding == BEWordSeqToByteSeq_premium([counter_index]);
    assert IsByteSeq(counter_index_encoding);
    assert IsByteSeq(old_counter_value_encoding);
    assert IsByteSeq(new_counter_value_encoding);
}

lemma Lemma_SufficientlySmallMessageCanBeSigned (message:seq<int>)
    requires IsByteSeq(message);
    requires |message| <= 0xFFFFFFFF;
    ensures |message| < power2(61);
    ensures |BEByteSeqToBitSeq(message)| < power2(64);
{
    calc {
        |BEByteSeqToBitSeq(message)|;
        |BEByteSeqToBitSeq_premium(message)|;
        8 * |message|;
        <= 8 * 0xFFFFFFFF;
        < 0x800000000;
        < { lemma_2toX(); reveal_power2(); }
          power2(64);
    }

    calc {
        |message|;
        <= 0xFFFFFFFF;
        < { lemma_2toX(); reveal_power2(); }
          power2(61);
    }
}

//-////////////////////////////////////////////////////////////////////////
//- Helpers
//-////////////////////////////////////////////////////////////////////////

method CheckClientSignature (public_key:RSAPubKeyImpl, new_counter_value_encoding:seq<int>, message:seq<int>,
                             request_attestation:seq<int>) returns (error_code:int)
    requires WellformedRSAPubKeyImpl(public_key);
    requires RSA_DIGEST_MIN_KEY_SIZE() <= public_key.size < power2(60);
    requires IsByteSeq(new_counter_value_encoding);
    requires IsByteSeq(message);
    requires IsByteSeq(request_attestation);

    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_ready();
    ensures TPM==old(TPM);

    ensures Word32(error_code);
    ensures error_code == 0 ==>
                var request := new_counter_value_encoding + message;
                |request| < power2(28) &&
                RSAVerificationRelationRequires(PubKeyImplToSpec(public_key), request, request_attestation) &&
                RSAVerificationRelation(PubKeyImplToSpec(public_key), request, request_attestation);

    requires public(PubKeyImplToSpec(public_key));
    requires public(new_counter_value_encoding);
    requires public(message);
    requires public(request_attestation);
    ensures public(error_code);
{
    lemma_2toX32();

    var request:seq<int> := new_counter_value_encoding + message;

    if |request| >= 0x10000000 {
        error_code := 2;
        return;
    }
    calc {
        |request|;
        < 0x10000000;
        == { reveal_power2(); }
           power2(28);
    }
    Lemma_SufficientlySmallMessageCanBeSigned(request);

    if |request_attestation| != public_key.size {
        error_code := 3;
        return;
    }

    var signature_ok := DigestedVerify(public_key, request, request_attestation);
    if !signature_ok {
        error_code := 5;
        return;
    }

    error_code := 0;
}

method CheckAdvanceCounterParameters (in_state:TrIncStateImpl, counter_index:nat, new_counter_value_encoding:seq<int>,
                                     message:seq<int>, request_attestation:seq<int>)
                                     returns (error_code:int, new_counter_value:BigNat)
    requires TrIncStateImplValid(in_state);
    requires IsByteSeq(new_counter_value_encoding);
    requires IsByteSeq(message);
    requires IsByteSeq(request_attestation);

    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_ready();
    ensures TPM==old(TPM);

    ensures Word32(error_code);
    ensures WellformedBigNat(new_counter_value);
    ensures error_code == 0 ==> 0 <= counter_index < |in_state.counters| &&
                                ModestBigNatValue(new_counter_value) &&
                                I(new_counter_value) < power2(power2(34)) &&
                                new_counter_value_encoding == rfc4251_mpint_encoding_premium(I(new_counter_value)) &&
                                I(in_state.counters[counter_index].counter_value) <= I(new_counter_value) &&
                                WellformedRSAPubKeyImpl(in_state.counters[counter_index].public_key) &&
                                RSAVerificationRelationRequires(PubKeyImplToSpec(in_state.counters[counter_index].public_key),
                                                                new_counter_value_encoding + message, request_attestation) &&
                                RSAVerificationRelation(PubKeyImplToSpec(in_state.counters[counter_index].public_key),
                                                        new_counter_value_encoding + message, request_attestation);

    requires public(TrIncStateImplToSpec(in_state));
    requires public(counter_index);
    requires public(new_counter_value_encoding);
    requires public(message);
    requires public(request_attestation);
    ensures public(error_code);
    ensures public(I(new_counter_value));
{
    Lemma_TrIncStateImplToSpecRelation(in_state, TrIncStateImplToSpec(in_state));
    new_counter_value := MakeSmallLiteralBigNat(0);

    lemma_2toX();

    if counter_index < 0 || counter_index >= |in_state.counters| {
        error_code := 1;
        return;
    }

    error_code := CheckClientSignature(in_state.counters[counter_index].public_key, new_counter_value_encoding, message,
                                       request_attestation);
    if error_code != 0 {
        return;
    }

    var success:bool;
    var bytes_consumed:int;
    success, new_counter_value, bytes_consumed := rfc4251_decode_mpint_legacy(new_counter_value_encoding);
    if !success {
        error_code := 6;
        new_counter_value := MakeSmallLiteralBigNat(0);
        return;
    }
    if bytes_consumed != |new_counter_value_encoding| {
        error_code := 7;
        new_counter_value := MakeSmallLiteralBigNat(0);
        return;
    }

    assert I(in_state.counters[counter_index].counter_value) == TrIncStateImplToSpec(in_state).counters[counter_index].counter_value;
    var too_small := BigNatLt(new_counter_value, in_state.counters[counter_index].counter_value);
    if too_small {
        error_code := 7;
        return;
    }
    assert I(new_counter_value) >= I(in_state.counters[counter_index].counter_value);

    var modest := IsModestBigNat(new_counter_value);
    if !modest {
        error_code := 8;
        return;
    }

    error_code := 0;
}

method EncodeAdvanceStatement (in_state:TrIncStateImpl, counter_index:nat, new_counter_value:BigNat,
                               new_counter_value_encoding:seq<int>, message:seq<int>)
                              returns (error_code:int, TrInc_statement:seq<int>, ghost ghost_old_counter_value_encoding:seq<int>)
    requires TrIncStateImplValid(in_state);
    requires WellformedBigNat(new_counter_value);
    requires IsByteSeq(message);
    requires 0 <= counter_index < |in_state.counters|;
    requires I(in_state.counters[counter_index].counter_value) <= I(new_counter_value);
    requires ModestBigNatValue(new_counter_value);
    requires I(new_counter_value) < power2(power2(34));
    requires new_counter_value_encoding == rfc4251_mpint_encoding_premium(I(new_counter_value));
    ensures Word32(error_code);
    ensures ghost_old_counter_value_encoding == rfc4251_mpint_encoding_premium(I(in_state.counters[counter_index].counter_value));
    ensures IsByteSeq(TrInc_statement);
    ensures TrInc_statement == TrIncCounterAdvanceStatement(counter_index,
                                                            I(in_state.counters[counter_index].counter_value),
                                                            I(new_counter_value),
                                                            message);
    ensures error_code == 0 ==>
                I(in_state.counters[counter_index].counter_value) < power2(power2(34)) &&
                Word32(|TrInc_statement|) &&
                |TrInc_statement| < power2(28) &&
                |BEByteSeqToBitSeq_premium(TrInc_statement)| < power2(64);

    requires public(TrIncStateImplToSpec(in_state));
    requires public(counter_index);
    requires public(I(new_counter_value));
    requires public(new_counter_value_encoding);
    requires public(message);
    ensures public(error_code);
    ensures public(TrInc_statement);
{
    Lemma_TrIncStateImplToSpecRelation(in_state, TrIncStateImplToSpec(in_state));
    lemma_2toX32();

    assert KV(in_state.counters[counter_index].counter_value) == I(in_state.counters[counter_index].counter_value);
    assert KV(in_state.counters[counter_index].counter_value) == TrIncStateImplToSpec(in_state).counters[counter_index].counter_value;

    var counter_index_encoding := rfc4251_encode_word32(counter_index);
    var old_counter_value_encoding := rfc4251_encode_mpint_legacy(in_state.counters[counter_index].counter_value);
    ghost_old_counter_value_encoding := old_counter_value_encoding;
    TrInc_statement := [34] + counter_index_encoding + old_counter_value_encoding + new_counter_value_encoding + message;
    Lemma_TrIncCounterAdvanceStatementValid(TrInc_statement, counter_index,
                                            I(in_state.counters[counter_index].counter_value), I(new_counter_value),
                                            counter_index_encoding, old_counter_value_encoding, new_counter_value_encoding, message);

    if |TrInc_statement| >= 0x10000000 {
        error_code := 7;
        return;
    }
    calc {
        |TrInc_statement|;
        < 0x10000000;
        ==
        power2(28);
    }


    error_code := 0;
    assert IsByte(34);
    assert IsByteSeq(TrInc_statement);
    Lemma_SufficientlySmallMessageCanBeSigned(TrInc_statement);

    assert TrInc_statement == TrIncCounterAdvanceStatement(counter_index,
                                                           TrIncStateImplToSpec(in_state).counters[counter_index].counter_value,
                                                           I(new_counter_value),
                                                           message);
}

method {:dafnycc_conservative_seq_triggers} UpdateStateByModifyingCounterValue
    (in_state:TrIncStateImpl, ghost in_state_spec:TrIncState, counter_index:nat, new_counter_value:BigNat)
    returns (out_state:TrIncStateImpl)
    requires TrIncStateImplValid(in_state);
    requires in_state_spec == TrIncStateImplToSpec(in_state);
    requires 0 <= counter_index < |in_state.counters|;
    requires WellformedBigNat(new_counter_value);
    requires ModestBigNatValue(new_counter_value);
    ensures |out_state.counters| == |in_state.counters|;
    ensures forall i :: 0 <= i < |in_state.counters| && i != counter_index ==> out_state.counters[i] == in_state.counters[i];
    ensures out_state.counters[counter_index].public_key == in_state.counters[counter_index].public_key;
    ensures out_state.counters[counter_index].counter_value == new_counter_value;

    requires public(in_state_spec);
    requires public(counter_index);
    requires public(I(new_counter_value));
    ensures public(TrIncStateImplToSpec(out_state));
{
    Lemma_TrIncCounterImplSeqToSpecRelation(in_state.counters, TrIncCounterImplSeqToSpec(in_state.counters));
    var counters:seq<TrIncCounterImpl> := [];
    var j:int := 0;

    counters := in_state.counters[..counter_index] +
                [TrIncCounterImpl_c(in_state.counters[counter_index].public_key, new_counter_value)] +
                in_state.counters[counter_index+1..];
    out_state := TrIncStateImpl_c(counters);

    calc {
        TrIncStateImplToSpec(out_state);
        TrIncStateConstructor(TrIncCounterImplSeqToSpec(out_state.counters));
        TrIncStateConstructor(TrIncCounterImplSeqToSpec(counters));
        TrIncStateConstructor(TrIncCounterImplSeqToSpec(
            in_state.counters[..counter_index] + [TrIncCounterImpl_c(in_state.counters[counter_index].public_key, new_counter_value)] +
            in_state.counters[counter_index+1..]));
           { Lemma_TrIncCounterImplSeqToSpecConcatenation(
                 in_state.counters[..counter_index] + [TrIncCounterImpl_c(in_state.counters[counter_index].public_key, new_counter_value)],
                 in_state.counters[counter_index+1..]); }
        TrIncStateConstructor(TrIncCounterImplSeqToSpec(
            in_state.counters[..counter_index] + [TrIncCounterImpl_c(in_state.counters[counter_index].public_key, new_counter_value)]) +
            TrIncCounterImplSeqToSpec(in_state.counters[counter_index+1..]));
           { Lemma_TrIncCounterImplSeqToSpecConcatenation(
                 in_state.counters[..counter_index],
                 [TrIncCounterImpl_c(in_state.counters[counter_index].public_key, new_counter_value)]); }
        TrIncStateConstructor(TrIncCounterImplSeqToSpec(in_state.counters[..counter_index]) +
                              TrIncCounterImplSeqToSpec([TrIncCounterImpl_c(in_state.counters[counter_index].public_key, new_counter_value)]) +
                              TrIncCounterImplSeqToSpec(in_state.counters[counter_index+1..]));
           { Lemma_ConvertStateCounterImplSeqSubset(in_state, 0, counter_index);
             assert in_state.counters[..counter_index] == in_state.counters[0..counter_index];
             assert in_state_spec.counters[..counter_index] == in_state_spec.counters[0..counter_index]; }
        TrIncStateConstructor(in_state_spec.counters[..counter_index] +
                              TrIncCounterImplSeqToSpec([TrIncCounterImpl_c(in_state.counters[counter_index].public_key, new_counter_value)]) +
                              TrIncCounterImplSeqToSpec(in_state.counters[counter_index+1..]));
           { Lemma_ConvertStateCounterImplSeqSubset(in_state, counter_index+1, |in_state.counters|);
             assert |in_state.counters| == |in_state_spec.counters|;
             assert in_state.counters[counter_index+1..] == in_state.counters[counter_index+1..|in_state.counters|];
             assert in_state_spec.counters[counter_index+1..] == in_state_spec.counters[counter_index+1..|in_state.counters|]; }
        TrIncStateConstructor(in_state_spec.counters[..counter_index] +
                              TrIncCounterImplSeqToSpec([TrIncCounterImpl_c(in_state.counters[counter_index].public_key, new_counter_value)]) +
                              in_state_spec.counters[counter_index+1..]);
           { Lemma_TrIncCounterImplSeqToSpecOfOne(TrIncCounterImpl_c(in_state.counters[counter_index].public_key, new_counter_value)); }
        TrIncStateConstructor(in_state_spec.counters[..counter_index] +
                              [TrIncCounterImplToSpec(TrIncCounterImpl_c(in_state.counters[counter_index].public_key, new_counter_value))] +
                              in_state_spec.counters[counter_index+1..]);
           { Lemma_ConvertStateCounterImpl(in_state, counter_index); }
        TrIncStateConstructor(in_state_spec.counters[..counter_index] +
                              [TrIncCounterConstructor(in_state_spec.counters[counter_index].public_key, I(new_counter_value))] +
                              in_state_spec.counters[counter_index+1..]);
    }
}

//-////////////////////////////////////////////////////////////////////////
//- Exported methods
//-////////////////////////////////////////////////////////////////////////

method TrIncInitialize () returns (trinc_state:TrIncStateImpl)
    ensures TrIncStateImplValid(trinc_state);
    ensures TrIncInitializeValid(TrIncStateImplToSpec(trinc_state));
    ensures public(TrIncStateImplToSpec(trinc_state));
{
    trinc_state := TrIncStateImpl_c([]); //- dafnycc: initialize variable
    Lemma_TrIncStateImplToSpecRelation(trinc_state, TrIncStateImplToSpec(trinc_state));
}

method TrIncCreateCounter (in_state:TrIncStateImpl, common_state:CommonStateImpl, public_key_encoding:seq<int>)
                          returns (out_state:TrIncStateImpl, error_code:int, counter_index:nat)
    requires TrIncStateImplValid(in_state);
    requires CommonStateImplValid(common_state);
    requires IsByteSeq(public_key_encoding);
    ensures TrIncStateImplValid(out_state);
    ensures error_code == 0 ==> TrIncCreateCounterValid(TrIncStateImplToSpec(in_state), TrIncStateImplToSpec(out_state),
                                                        CommonStateImplToSpec(common_state), public_key_encoding, counter_index);
    ensures error_code != 0 ==> out_state == in_state;
    ensures Word32(error_code);
    ensures Word32(counter_index);

    requires public(TrIncStateImplToSpec(in_state));
    requires public(public_key_encoding);
    ensures public(TrIncStateImplToSpec(out_state));
    ensures public(error_code);
    ensures public(counter_index);
{
    out_state := in_state;
    counter_index := 0;

    lemma_2toX();
    Lemma_TrIncStateImplToSpecRelation(in_state, TrIncStateImplToSpec(in_state));
    if |in_state.counters| >= 0xFFFFFFFF {
        error_code := 1;
        return;
    }

    if |public_key_encoding| >= 0xFFFFFFFF {
        error_code := 2;
        return;
    }

    var success, public_key := rfc4251_decode_sshrsa(public_key_encoding);
    if !success {
        error_code := 3;
        return;
    }

    assert WellformedRSAPubKeyImpl(public_key);
    assert WellformedRSAPubKeySpec(PubKeyImplToSpec(public_key));

    if public_key.size < RSA_DIGEST_MIN_KEY_SIZE() || public_key.size >= 0xFFFFFFFF {
        error_code := 4;
        return;
    }

    error_code := 0;
    var zero := MakeSmallLiteralBigNat(0);
    var new_counter := TrIncCounterImpl_c(public_key, zero);
    out_state := TrIncStateImpl_c(in_state.counters + [new_counter]);
    counter_index := |out_state.counters| - 1;

    calc {
        TrIncStateImplToSpec(out_state);
        TrIncStateConstructor(TrIncCounterImplSeqToSpec(in_state.counters + [new_counter]));
        { Lemma_TrIncCounterImplSeqToSpecConcatenation(in_state.counters, [new_counter]); }
        TrIncStateConstructor(TrIncCounterImplSeqToSpec(in_state.counters) + TrIncCounterImplSeqToSpec([new_counter]));
        { Lemma_TrIncCounterImplSeqToSpecOfOne(new_counter); }
        TrIncStateConstructor(TrIncCounterImplSeqToSpec(in_state.counters) + [TrIncCounterImplToSpec(new_counter)]);
        TrIncStateConstructor(TrIncStateImplToSpec(in_state).counters + [TrIncCounterImplToSpec(new_counter)]);
        TrIncStateConstructor(TrIncStateImplToSpec(in_state).counters + [TrIncCounterConstructor(PubKeyImplToSpec(new_counter.public_key), I(new_counter.counter_value))]);
        TrIncStateConstructor(TrIncStateImplToSpec(in_state).counters + [TrIncCounterConstructor(PubKeyImplToSpec(new_counter.public_key), 0)]);
        TrIncStateConstructor(TrIncStateImplToSpec(in_state).counters + [TrIncCounterConstructor(PubKeyImplToSpec(public_key), 0)]);
    }

//-    Lemma_TrIncStateImplToSpecRelation(out_state, TrIncStateImplToSpec(out_state));
//-    Lemma_TrIncCounterImplSeqToSpecConcatenation(in_state.counters, [new_counter]);
    assert counter_index == |TrIncStateImplToSpec(out_state).counters| - 1;
}

method{:dafnycc_conservative_seq_triggers} TrIncAdvanceCounter
    (in_state:TrIncStateImpl, common_state:CommonStateImpl, counter_index:nat,
     new_counter_value_encoding:seq<int>, message:seq<int>, request_attestation:seq<int>)
    returns (out_state:TrIncStateImpl, error_code:int, TrInc_statement:seq<int>, TrInc_attestation:seq<int>)
    requires TrIncStateImplValid(in_state);
    requires CommonStateImplValid(common_state);
    requires RSA_DIGEST_MIN_KEY_SIZE() <= common_state.key_pair.pub.size;
    requires IsByteSeq(new_counter_value_encoding);
    requires IsByteSeq(message);
    requires IsByteSeq(request_attestation);

    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM==old(TPM);
    ensures TPM_ready();

    ensures TrIncStateImplValid(out_state);
    ensures error_code == 0 ==> TrIncAdvanceCounterValid(TrIncStateImplToSpec(in_state), TrIncStateImplToSpec(out_state),
                                                         CommonStateImplToSpec(common_state),
                                                         counter_index, new_counter_value_encoding, message, request_attestation,
                                                         TrInc_statement, TrInc_attestation);
    ensures error_code != 0 ==> out_state == in_state;
    ensures TrIncStateImplValid(out_state);
    ensures Word32(error_code);
    ensures Word32(|TrInc_statement|);
    ensures Word32(|TrInc_attestation|);
    ensures IsByteSeq(TrInc_statement);
    ensures IsByteSeq(TrInc_attestation);

    requires public(TrIncStateImplToSpec(in_state));
    requires public(counter_index);
    requires public(new_counter_value_encoding);
    requires public(message);
    requires public(request_attestation);
    ensures public(TrIncStateImplToSpec(out_state));
    ensures public(error_code);
    ensures public(TrInc_statement);
{
    out_state := in_state;
    TrInc_statement := [];
    TrInc_attestation := [];
    ghost var in_state_spec := TrIncStateImplToSpec(in_state);
    Lemma_TrIncStateImplValidImpliesTrIncStateValid(in_state);

    var new_counter_value:BigNat;
    error_code, new_counter_value := CheckAdvanceCounterParameters(in_state, counter_index, new_counter_value_encoding,
                                                                   message, request_attestation);
    if (error_code != 0) {
        out_state := in_state;
        return;
    }

    ghost var old_counter_value_encoding:seq<int>;
    error_code, TrInc_statement, old_counter_value_encoding := 
        EncodeAdvanceStatement(in_state, counter_index, new_counter_value, new_counter_value_encoding, message);
    if (error_code != 0) {
        out_state := in_state;
        TrInc_statement := [];
        return;
    }

    TrInc_attestation := DigestedSign(common_state.key_pair, TrInc_statement);

    out_state := UpdateStateByModifyingCounterValue(in_state, in_state_spec, counter_index, new_counter_value);
    Lemma_TrIncCounterImplSeqToSpecRelation(in_state.counters, in_state_spec.counters);
    Lemma_UpdatingStateEnsuresProperUpdatesToSpec(in_state, out_state,
                                                  in_state_spec, TrIncStateImplToSpec(out_state),
                                                  counter_index, new_counter_value);
    Lemma_TrIncStateImplToSpecRelation(out_state, TrIncStateImplToSpec(out_state));

    ghost var new_counter_value_int := I(new_counter_value);  //- Introduce a witness Dafny needs
}
