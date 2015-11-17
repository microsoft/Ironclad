include "tpm-device.s.dfy"

static predicate read_random_forall(start_index:int, random_bytes:seq<int>)
{
    forall j :: 0 <= j < |random_bytes| ==> TPM_random_byte(start_index + j) == random_bytes[j]
}

static lemma lemma_randoms_forall_is_TPM_random_bytes(start_index:int, random_bytes:seq<int>)
    ensures read_random_forall(start_index, random_bytes)
        == (TPM_random_bytes(start_index, start_index+|random_bytes|) == random_bytes);
    decreases |random_bytes|;
{
    if (|random_bytes|==0)
    {
    }
    else
    {
        lemma_randoms_forall_is_TPM_random_bytes(start_index, random_bytes[..|random_bytes|-1]);
    }
}

static lemma lemma_random_comprehension(start_index:int, ra:seq<int>, rb:seq<int>)
    requires TPM_random_bytes(start_index, start_index+|ra|) == ra;
    requires TPM_random_bytes(start_index+|ra|, start_index+|ra|+|rb|) == rb;
    ensures TPM_random_bytes(start_index, start_index+|ra|+|rb|) == ra+rb;
{
    lemma_randoms_forall_is_TPM_random_bytes(start_index, ra);
    lemma_randoms_forall_is_TPM_random_bytes(start_index+|ra|, rb);
    lemma_randoms_forall_is_TPM_random_bytes(start_index, ra+rb);
}

static lemma lemma_TPM_random_bytes_length(old_random_index:int, new_random_index:int)
    requires old_random_index <= new_random_index;
    ensures |TPM_random_bytes(old_random_index, new_random_index)| == new_random_index - old_random_index;
    decreases new_random_index-old_random_index;
{
    if (old_random_index == new_random_index)
    {
    }
    else
    {
        lemma_TPM_random_bytes_length(old_random_index, new_random_index-1);
    }
}

static function TPM_random_bytes_premium (old_random_index:int, new_random_index:int) : seq<int>
    requires old_random_index <= new_random_index;
    ensures |TPM_random_bytes_premium(old_random_index, new_random_index)| == new_random_index - old_random_index;
{
    lemma_TPM_random_bytes_length(old_random_index, new_random_index);
    TPM_random_bytes(old_random_index, new_random_index)
}

static predicate TPMs_match_except_for_randoms (TPM1:TPM_struct, TPM2:TPM_struct)
{
    TPMs_match(TPM1, TPM2[random_index := TPM1.random_index])
}
