include "be_sequences.s.dfy"
include "seqs_and_ints.i.dfy"
include "integer_sequences_premium.i.dfy"
include "word_bits.i.dfy"
include "seqs_transforms.i.dfy"
include "../Math/div.i.dfy"
include "../Math/power2.i.dfy"
include "../Math/power.i.dfy"
include "../base.s.dfy"
//-include "../assembly.s.dfy"

static predicate IsWordArray(a: array<int>)
    reads a;
{
    a != null &&
    forall i :: 0 <= i < a.Length ==> Word32(a[i])
}

static function {:opaque} GetArrayBit(a: array<int>, b:int) : int
    requires IsWordArray(a);
    requires 0 <= b < a.Length * 32;
    ensures IsBit(GetArrayBit(a, b));
    ensures GetArrayBit(a, b) == BEWordSeqToBitSeq_premium(a[..])[b];
    reads a;
{
    calc {
        BEWordSeqToBitSeq_premium(a[..])[b];
        BEIntToDigitSeq(power2(1), |a[..]|*32, BEDigitSeqToInt(power2(32), a[..]))[b];
        { lemma_power2_1_is_2(); }
        BEIntToDigitSeq(2, |a[..]|*32, BEDigitSeqToInt(power2(32), a[..]))[b];
        { lemma_BEIntToWordSeq_decomposition(a[..], b); }
        BEIntToDigitSeq(2, 32, a[..][b/32])[b%32];
        BEIntToDigitSeq(2, 32, a[b/32])[b%32];
        { lemma_power2_1_is_2(); }
        BEWordToBitSeq(a[b/32])[b%32];
        GetWordBit(a[b / 32], b % 32);
    }
    GetWordBit(a[b / 32], b % 32)
}

//-/////////////////////
//- Updating arrays
//-/////////////////////

static method UpdateBitOfArray(a: array<int>, pos: int, value: int)
    requires IsWordArray(a);
    requires 0 <= pos < a.Length * 32;
    requires IsBit(value);
    ensures IsWordArray(a);
    ensures GetArrayBit(a, pos) == value;
    ensures forall i {:trigger GetArrayBit(a, i)}{:trigger old(GetArrayBit(a, i))} ::
        0 <= i < a.Length * 32 && i != pos ==> GetArrayBit(a, i) == old(GetArrayBit(a, i));
    modifies a;
{
    reveal_GetArrayBit();
    a[pos / 32] := UpdateBitOfWord(a[pos / 32], pos % 32, value);

    calc {
        GetArrayBit(a, pos);
        { reveal_GetArrayBit(); }
        GetWordBit(a[pos / 32], pos % 32);
        value;
    }

    forall i | 0 <= i < a.Length * 32 && i != pos
        ensures GetArrayBit(a, i) == old(GetArrayBit(a, i));
    {
        if (i / 32 != pos / 32) {
            reveal_GetArrayBit();           
        }
        else {
            calc {
                GetArrayBit(a, i);
                { reveal_GetArrayBit(); }
                GetWordBit(a[pos / 32], i % 32);
                { lemma_fundamental_div_mod(i, 32); lemma_fundamental_div_mod(pos, 32); assert i % 32 != pos % 32; }
                GetWordBit(old(a[i / 32]), i % 32);
                old(GetArrayBit(a, i));
            }
            assert GetArrayBit(a, i) == old(GetArrayBit(a, i));
        }
    }
}

static method AppendBitToArray(a: array<int>, b: int, value: int)
    requires IsWordArray(a);
    requires 0 <= b < a.Length * 32;
    requires IsBit(value);
    ensures IsWordArray(a);
    ensures forall i {:trigger GetArrayBit(a, i)}{:trigger old(GetArrayBit(a, i))} :: 0 <= i < b ==> GetArrayBit(a, i) == old(GetArrayBit(a, i));
    ensures GetArrayBit(a, b) == value;
    modifies a;
{
    UpdateBitOfArray(a, b, value);
}


static method AppendWordToArray(a: array<int>, b: int, value: int)
    requires IsWordArray(a);
    requires 0 <= b;
    requires b % 32 == 0;
    requires b + 32 <= a.Length * 32;
    requires Word32(value);
    ensures IsWordArray(a);
    ensures forall i {:trigger GetArrayBit(a, i)}{:trigger old(GetArrayBit(a, i))} :: 0 <= i < b ==> GetArrayBit(a, i) == old(GetArrayBit(a, i));
    ensures forall i {:trigger a[i]}:: 0 <= i * 32 < b ==> a[i] == old(a[i]);
    ensures a[b / 32] == value;
    modifies a;
{
    reveal_GetArrayBit();
    a[b / 32] := value;
    reveal_GetArrayBit();
}

static method AppendBitsToArray(a: array<int>, b: int, value: int, num_values: int)
    requires IsWordArray(a);
    requires 0 <= b;
    requires 0 <= num_values;
    requires b + num_values <= a.Length * 32;
    requires IsBit(value);
    ensures IsWordArray(a);
    ensures forall i {:trigger GetArrayBit(a, i)}{:trigger old(GetArrayBit(a, i))} :: 0 <= i < b ==> GetArrayBit(a, i) == old(GetArrayBit(a, i));
    ensures forall i {:trigger GetArrayBit(a, i)} :: b <= i < b + num_values ==> GetArrayBit(a, i) == value;
    modifies a;
{
    var j := 0;
    while (j < num_values)
        invariant 0 <= b <= b + j <= b + num_values <= a.Length * 32;
        invariant forall i :: 0 <= i < a.Length ==> Word32(a[i]);
        invariant forall i :: 0 <= i < b ==> GetArrayBit(a, i) == old(GetArrayBit(a, i));
        invariant forall i :: b <= i < b + j ==> GetArrayBit(a, i) == value;
    {
        var old_j := j;
        if (value == 0 && (b + j) % 32 == 0 && j + 32 <= num_values) {
            lemma_2toX();
            AppendWordToArray(a, b + j, 0);
            j := j + 32;
            forall (i | b + old_j <= i < b + j)
                ensures GetArrayBit(a, i) == 0;
            {
                assert i/32 == (b + old_j) / 32;

                assert (b + old_j) % 32 == 0;
                var k := i - (b+old_j);
                assert k < 32;
                assert i == k + (b+old_j);
                assert i/32 == (k + (b+old_j))/32 == (b+old_j)/32;
                assert a[i/32] == a[(b+old_j)/ 32] == 0;
                assert k == i % 32;

                calc {
                    GetArrayBit(a, i);
                    { reveal_GetArrayBit(); }
                    GetWordBit(a[i / 32], i % 32);
                    GetWordBit(0, i % 32);
                    GetWordBit(0, k);
                    { reveal_power2(); lemma_BEIntToDigitSeq_private_zero(power2(1), 32); }
                    0;
                }
            }
        }
        else {
            AppendBitToArray(a, b + j, value);
            j := j + 1;
            forall (i | b <= i < b + j) ensures GetArrayBit(a, i) == value;
            {
                if (i == b + old_j) { }
            }
        }
        reveal_GetArrayBit();
    }
}

static lemma lemma_array_seq_equality(a:array<int>, b:array<int>, a_start:int, a_end:int, b_start:int, b_end:int)
    requires a != null && b != null;
    requires b_end - b_start == a_end - a_start;
    requires 0 <= a_start < a_end <= a.Length;
    requires 0 <= b_start < b_end <= b.Length;
    requires forall i :: 0 <= i < a_end - a_start ==> a[a_start + i] == b[b_start + i];
    ensures a[a_start..a_end] == b[b_start..b_end];
{
    ghost var A := a[a_start..a_end];
    ghost var B := b[b_start..b_end];

    assert |A| == |B|;
    forall i | 0 <= i < |A|
        ensures 0 <= i < |A| ==> A[i] == B[i];
    {
        calc {
            A[i];
            a[a_start..a_end][i];
            a[a_start + i];
            { assert forall j :: 0 <= j < a_end - a_start ==> a[a_start + j] == b[b_start + j]; }
            //-{ assert 0 <= i < a_end - a_start; }
            b[b_start + i];
            b[b_start..b_end][i];
            B[i];
        }
        assert A[i] == B[i];
        //-assert a[a_start..a_end][i] == b[b_start..b_end][i];
    }
    assert A == B;
    assert a[a_start..a_end] == b[b_start..b_end];
}

method SeqToArray(s:seq<int>) returns (a:array<int>)
    ensures fresh(a);
    ensures a != null;
    ensures a.Length == |s|;
    ensures forall i :: 0 <= i < |s| ==> s[i] == a[i];
    ensures a[..] == s;
    ensures fresh(a);
{
    a := new int[|s|];

    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|;
        invariant forall j :: 0 <= j < i ==> s[j] == a[j];
    {
        a[i] := s[i];
        i := i + 1;
    }
}
