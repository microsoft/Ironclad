include "be_sequences.s.dfy"
include "../Math/div.i.dfy"
include "seqs_simple.i.dfy"

static lemma Lemma_RepeatDigitProperties(digit:int, count:int)
    decreases count;
    ensures |RepeatDigit(digit, count)| == if count < 0 then 0 else count;
    ensures forall i :: 0 <= i < count ==> RepeatDigit(digit, count)[i] == digit;
{
    if (count > 0)
    {
        Lemma_RepeatDigitProperties(digit, count - 1);
    }
}

static function RepeatDigit_premium(digit:int, count:int) : seq<int>
    ensures |RepeatDigit(digit, count)| == if count < 0 then 0 else count;
    ensures forall i :: 0 <= i < count ==> RepeatDigit(digit, count)[i] == digit;
{
    Lemma_RepeatDigitProperties(digit, count);
    RepeatDigit(digit, count)
}

static function {:opaque} SequenceOfZeros(n:nat) : seq<int>
//-    ensures SequenceOfZeros(n)!=NSeqInt_n();
    ensures |SequenceOfZeros(n)|==n;
    ensures forall i :: 0<=i<n ==> SequenceOfZeros(n)[i]==0;
    ensures forall pv :: 0<pv ==> IsDigitSeq(pv, SequenceOfZeros(n));
{
    if (n==0) then [] else SequenceOfZeros(n-1)+[0]
}

static lemma lemma_SequenceOfZeros_is_RepeatDigit(count:nat)
    ensures SequenceOfZeros(count) == RepeatDigit(0, count);
{
    Lemma_RepeatDigitProperties(0, count);
}

static method SequenceOfZerosIterative(n:nat) returns (Z:seq<int>)
    requires Word32(n);
    ensures Z == SequenceOfZeros(n);
//-    ensures Z!=NSeqInt_n();
    ensures |Z|==n;
    ensures forall i :: 0<=i<n ==> Z[i]==0;
    ensures forall pv :: 0<pv ==> IsDigitSeq(pv, Z);
{
    reveal_SequenceOfZeros();

    var num_zeros := 0;
    var z := [];
    while (num_zeros < n)
        invariant 0 <= num_zeros <= n;
        invariant z == SequenceOfZeros(num_zeros);
    {
        z := z + [0];
        num_zeros := num_zeros + 1;
    }
    Z := z;
}


static lemma lemma_BEIntToDigitSeq_private_zero(pv:int, b:int)
    requires 1<pv;
    requires 0<=b;
    decreases b;
    ensures |BEIntToDigitSeq_private(pv, b, 0)| == b;
    ensures forall i::0<=i<b ==> BEIntToDigitSeq_private(pv, b, 0)[i] == 0;
{
    reveal_BEIntToDigitSeq_private();
    if (b==0)
    {
    }
    else
    {
        lemma_BEIntToDigitSeq_private_zero(pv, b-1);
        calc {
            BEIntToDigitSeq_private(pv, b, 0);
                { lemma_div_pos_is_pos(0,pv); }
            BEIntToDigitSeq_private(pv, b-1, div(0,pv)) + [ mod(0,pv) ];
                { lemma_small_mod(0,pv); }
            BEIntToDigitSeq_private(pv, b-1, div(0,pv)) + [ 0 ];
                { lemma_div_basics(pv); }
            BEIntToDigitSeq_private(pv, b-1, 0) + [ 0 ];
        }
        forall (i | 0<=i<b)
            ensures BEIntToDigitSeq_private(pv, b, 0)[i] == 0;
        {
        }
        assert forall i::0<=i<b ==> BEIntToDigitSeq_private(pv, b, 0)[i] == 0;
    }
}

static lemma lemma_BEIntToDigitSeq_invertibility_zero(pv:int, digitseq:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, digitseq);
    requires digitseq == BEIntToDigitSeq(pv, |digitseq|, 0);
    requires forall i::0<=i<|digitseq| ==> digitseq[i] == 0;
    decreases |digitseq|;
    ensures BEDigitSeqToInt(pv, digitseq) == 0;
{
    reveal_BEDigitSeqToInt_private();
    reveal_BEIntToDigitSeq_private();
    if (|digitseq|==0)
    {
    }
    else
    {
        calc {
            BEDigitSeqToInt(pv, digitseq);
            BEDigitSeqToInt_private(pv, digitseq);
            BEDigitSeqToInt_private(pv, digitseq[0..|digitseq|-1])*pv + digitseq[|digitseq|-1];
            {
                var prefix := digitseq[..|digitseq|-1];
                lemma_BEIntToDigitSeq_private_zero(pv, |digitseq|-1);
                var subzero := BEIntToDigitSeq_private(pv, |digitseq|-1, 0);
                assert |subzero| == |digitseq| - 1;
                assert forall i::0<=i<|digitseq|-1 ==> subzero[i] == 0;
                assert subzero == prefix;

                lemma_BEIntToDigitSeq_invertibility_zero(pv, subzero);
                assert BEDigitSeqToInt(pv, subzero) == 0;
                assert BEDigitSeqToInt_private(pv, prefix) == 0;
                calc {
                    BEDigitSeqToInt_private(pv, digitseq[0..|digitseq|-1]);
                        { lemma_vacuous_statement_about_a_sequence(digitseq, |digitseq|-1); }
                    BEDigitSeqToInt_private(pv, prefix);
                    0;
                }
            }
            mul(0,pv) + digitseq[|digitseq|-1];
                { lemma_mul_basics_forall(); }
            digitseq[|digitseq|-1];
            0;
        }
    }
}

static method RepeatDigit_impl(digit:int, count:int) returns (os:seq<int>)
    ensures os == RepeatDigit_premium(digit, count);
{
    os := [];

    if count < 0 {
        return;
    }

    var i := 0;
    while i < count
        invariant 0 <= i <= count;
        invariant os == RepeatDigit(digit, i);
    {
        os := os + [digit];
        i := i + 1;
    }
}

static method RepeatDigit_impl_arrays(digit:int, count:int) returns (os:array<int>)
    ensures os != null;
    ensures os[..] == RepeatDigit_premium(digit, count);
{
    if count < 0 {
        os := new int[0];
        return;
    }

    os := new int[count];
    var i := 0;
    while i < count
        invariant 0 <= i <= count;
        invariant os[..i] == RepeatDigit(digit, i);
    {
        os[i] := digit;
        i := i + 1;
    }
}
