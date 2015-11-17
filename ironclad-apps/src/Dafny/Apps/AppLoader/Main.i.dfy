include "../../Drivers/TPM/tpm-wrapper.i.dfy"
include "../../Libraries/Util/arrays_2.i.dfy"










//-method TestArrayAlloc() returns (arr:array<int>)
//-    ensures fresh(arr);
//-    ensures arr != null;
//-    ensures arr.Length == 0x40000;
//-    ensures forall j :: 0 <= j < arr.Length ==> arr[j] == j;
//-    ensures IsWordSeq(arr[..]);
//-{
//-    arr := new int[0x40000];
//-    var i := 0;
//-    while (i < 0x40000) 
//-        invariant 0 <= i <= 0x40000;
//-        invariant forall j :: 0 <= j < i ==> arr[j] == j;
//-        invariant forall j :: 0 <= j < i ==> Word32(arr[j]);
//-    {
//-        arr[i] := i;
//-        i := i + 1;
//-        lemma_2toX();
//-    }
//-}

method PrependArray(first:int, second:int, rest:array<int>) returns (unified:array<int>)
    requires Word32(first) && Word32(second);
    requires rest != null;
    requires IsWordSeq(rest[..]);
    ensures  fresh(unified);
    ensures  unified != null;
    ensures  IsWordSeqOfLen(unified[..], 2 + rest.Length);
    ensures  unified[..] == [first, second] + rest[..];
{
    unified := new int[2 + rest.Length];
    unified[0] := first;
    unified[1] := second;

    var i := 0;
    while (i < rest.Length)
        invariant 0 <= i <= rest.Length;
        invariant unified[..i+2] == [first, second] + rest[..i];
    {
        unified[i+2] := rest[i];
        assert unified[..i+3] == unified[..i+2] + [unified[i+2]];  //- dafnycc
        assert rest[..i+1] == rest[..i] + [rest[i]];        //- dafnycc
        i := i + 1;
    }
    calc {
        unified[..];
        unified[..rest.Length+2];
        [first, second] + rest[..rest.Length];
        [first, second] + rest[..];
    }
}

method hash_code_region(code_start:int, entry_point:int, code_words:array<int>) returns (hash_bytes:seq<int>)
    requires Word32(code_start) && Word32(entry_point);
    requires code_words != null;
    requires code_words.Length == 0x40000;
    requires IsWordSeq(code_words[..]);
    ensures  var hash_input := BEWordSeqToBitSeq_premium([code_start, entry_point] + code_words[..]);
             |hash_input| < power2(64) &&
             IsBitSeq(hash_input) &&
             hash_bytes == BEWordSeqToByteSeq_premium(SHA1(hash_input));
{
    lemma_2toX();
    ghost var sha_input_words := [code_start, entry_point] + code_words[..];
    var unified_input := PrependArray(code_start, entry_point, code_words);
    assert unified_input[..] == [code_start, entry_point] + code_words[..];
    assert |unified_input[..]| == 0x40002;
    assert |BEWordSeqToBitSeq_premium([code_start, entry_point] + code_words[..])| == 32*0x40002; 
    assert |BEWordSeqToBitSeq_premium([code_start, entry_point] + code_words[..])| < power2(64);

    var unified_input_bytes := new int[unified_input.Length*4];
    BEWordArrayToByteArray(unified_input, unified_input_bytes);

    var hash_arr := SHA1_impl_Bytes_arrays(unified_input_bytes);
    assert hash_arr[..] == SHA1(BEByteSeqToBitSeq_premium(unified_input_bytes[..]));
    var hash_seq := hash_arr[..];
    hash_bytes := BEWordSeqToByteSeq_impl(hash_seq);
    lemma_BEByteSeqToBitSeq_BEWordSeqToByteSeq([code_start, entry_point] + code_words[..]);
}

method Main (code_start:int, entry_point:int, code_words:array<int>) returns (result:int)
    requires word32(code_start) && word32(entry_point);
    requires code_words != null;
    requires code_words.Length == 0x40000;
    requires IsWordSeq(code_words[..]);
    requires TPM_valid(TPM);
    requires TPM.PCR_19 == [];
    requires IoMemPerm.Null?;
    requires TPM_satisfies_integrity_policy(TPM);
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures  Word32(code_start) && Word32(entry_point);
    ensures  var hash_input := BEWordSeqToBitSeq([code_start, entry_point] + code_words[..]);
             |hash_input| < power2(64) &&
             IsBitSeq(hash_input) &&
             TPM.PCR_19 == [BEWordSeqToByteSeq(SHA1(hash_input))];
    ensures  result == entry_point;
{
    establish_locality();
    lemma_2toX();
    lemma_word32_Word32();
    assert word32(code_start) ==> Word32(code_start);
    assert word32(entry_point) ==> Word32(entry_point);
    
    var hash_bytes := hash_code_region(code_start, entry_point, code_words);
    var success := extend_PCR(hash_bytes);

    if (!success) {     //- Can't guarantee anything about PCR 19 at this point
        while true
            decreases *;
        {
            debug_print(0, 0x44440021);
        }
    }

//-    calc {
//-        TPM.PCR_19;
//-        [hash_bytes];
//-        [BEWordSeqToByteSeq(hash_seq)];
//-        [BEWordSeqToByteSeq(SHA1(BEByteSeqToBitSeq_premium(unified_input_bytes[..])))];
//-        [BEWordSeqToByteSeq(SHA1(BEByteSeqToBitSeq_premium(BEWordSeqToByteSeq(sha_input_words))))];
//-        [BEWordSeqToByteSeq(SHA1(BEByteSeqToBitSeq_premium(BEWordSeqToByteSeq_premium([code_start, entry_point] + code_words[..]))))];
//-    }
    lemma_BEByteSeqToBitSeq_BEWordSeqToByteSeq([code_start, entry_point] + code_words[..]);

    return entry_point;
}
