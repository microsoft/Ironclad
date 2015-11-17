include "../Util/arrays_and_seqs.i.dfy"
include "CanonicalArrays.i.dfy"

method BEWordArrayToByteArray(M:array<int>) returns (m:array<int>)
    requires M!=null;
    requires IsWordSeq(M[..]);
    ensures m!=null;
    ensures IsByteSeq(m[..]);
    ensures BEByteSeqToInt(m[..]) == BEWordSeqToInt(M[..]);
//-    ensures BEIntToByteSeq(I(M)) == m;    //- no seq relation equivalence
    ensures m.Length==0 || 0<m[0];
    ensures IsCanonicalDigitSeq(power2(8), m[..]);
    ensures fresh(m);
{
    
    var ms := BEWordSeqToByteSeq_impl(M[..]);
    var mfluffy := SeqToArray(ms);
    lemma_2toX();
    m := TrimLeadingZerosArray(power2(8), mfluffy);
}

method BEByteArrayToWordArray(m:array<int>) returns (M:array<int>)
    requires m!=null;
    requires IsByteSeq(m[..]);
    ensures M!=null;
    ensures IsWordSeq(M[..]);
    ensures BEByteSeqToInt(m[..]) == BEWordSeqToInt(M[..]);
//-    ensures BEIntToByteSeq(I(M)) == m;    //- no seq relation equivalence
    ensures M.Length==0 || 0<M[0];
    ensures fresh(M);
{
    var ms := m[..];
    var Mfluffy;
    ghost var Ms, padbytes;
    Mfluffy, Ms, padbytes := BEByteSeqToWordSeq_impl_arrays(m, m[..]);
    lemma_2toX();
    M := TrimLeadingZerosArray(power2(32), Mfluffy);
}


