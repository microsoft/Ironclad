include "../Util/seqs_canonical.i.dfy"
include "../Util/seqs_and_ints.i.dfy"
include "../Util/seqs_common.i.dfy"

method CountTopZeroWords(n:array<int>) returns (i:int)
    requires n!=null;
//-    requires IsWordSeq(n[..]);
    ensures 0<=i<=n.Length;
    ensures forall j :: 0<=j<i ==> n[j]==0;
    ensures i<n.Length ==> n[i]!=0;
{
    i := 0;
    while (i < n.Length)
        invariant 0<=i<=n.Length;
        invariant forall j :: 0<=j<i ==> n[j]==0;
    {
        if (n[i]!=0) {
            return;
        }
        i := i + 1;
    }
}

method CopyArray(dst:array<int>, doff:nat, src:array<int>, soff:nat, count:nat)
    requires src!=null;
    requires soff+count <= src.Length;
    requires dst!=null;
    requires doff+count <= dst.Length;
    requires src!=dst;
    modifies dst;
    ensures dst[doff..doff+count] == src[soff..soff+count];
{
    var i:=0;
    while (i<count)
        invariant 0<=i<=count;
        invariant src[soff..soff+i] == dst[doff..doff+i];
        decreases count-i;
    {
        dst[doff+i] := src[soff+i];
        assert src[soff..soff+i+1] == src[soff..soff+i] + [src[soff+i]];
        assert dst[doff..doff+i+1] == dst[doff..doff+i] + [dst[doff+i]];
        i := i + 1;
    }
}

method CopyArraySimple(dst:array<int>, src:array<int>)
    requires dst != null;
    requires src != null;
    requires dst.Length == src.Length;
    requires dst != src;
    modifies dst;
    ensures dst != src;
    ensures dst[..] == src[..];
{
    CopyArray(dst, 0, src, 0, src.Length);
    assert dst[..] == dst[0..src.Length];   //- OBSERVE SEQ
    assert src[..] == src[0..src.Length];   //- OBSERVE SEQ
}




function CanonicalizeSeq_def(pv:int, s:seq<int>) : seq<int>
    requires 1<pv;
    requires IsDigitSeq(pv, s);
    decreases |s|;
{
    if (s==[]) then
        s
    else if s[0]!=0 then
        assert BEDigitSeqToInt(pv, s) == BEDigitSeqToInt(pv, s);
        s
    else
        CanonicalizeSeq_def(pv, s[1..])
}

lemma lemma_CanonicalizeSeq(pv:int, s:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, s);
    ensures IsCanonicalDigitSeq(pv, CanonicalizeSeq_def(pv,s));
    ensures BEDigitSeqToInt(pv, CanonicalizeSeq_def(pv,s)) == BEDigitSeqToInt(pv, s);
    ensures |CanonicalizeSeq_def(pv,s)| <= |s|;
    decreases |s|;
{ 
    if (s==[])
    {
    } else if (s[0]!=0) {
    } else {
        lemma_CanonicalizeSeq(pv, s[1..]);
        lemma_LeadingZeros(pv, s[1..], s);
    }
}




function CanonicalizeSeq(pv:int, s:seq<int>) : seq<int>
    requires 1<pv;
    requires IsDigitSeq(pv, s);
    ensures IsCanonicalDigitSeq(pv, CanonicalizeSeq(pv,s));
    ensures BEDigitSeqToInt(pv, CanonicalizeSeq(pv,s)) == BEDigitSeqToInt(pv, s);
    ensures |CanonicalizeSeq(pv,s)| <= |s|;
{
    lemma_CanonicalizeSeq(pv, s);
    CanonicalizeSeq_def(pv, s)
}

method CanonicalizeArray(a:array<int>) returns (na:array<int>)
    requires a!=null;
    requires IsDigitSeq(power2(32), a[..]);
    ensures na!=null;
    ensures IsCanonicalDigitSeq(power2(32), na[..]);
    ensures BEWordSeqToInt(na[..]) == BEWordSeqToInt(a[..]);
    ensures na.Length <= a.Length;
    ensures fresh(na) || na == a;
{
    lemma_2toX();
    ghost var As := a[..];

    var t := CountTopZeroWords(a);
    if (t==0)
    {
        na := a;
        return;
    }
    var count := a.Length - t;
    na := new int[count];
    CopyArray(na, 0, a, t, count);
    ghost var Nas := na[..];

    assert Nas==Nas[0..count];  //- OBSERVE SEQ

    lemma_LeadingZeros(power2(32), Nas, As);
}

method MakeBELiteralArray(x:nat) returns (xa:array<int>)
    requires IsWord(x);
    ensures xa!=null;
    ensures IsWordSeq(xa[..]);
    ensures BEWordSeqToInt(xa[..]) == x;
    ensures xa.Length == if x==0 then 0 else 1;
    ensures IsCanonicalDigitSeq(power2(32), xa[..]);
    ensures fresh(xa);
{
    if (x==0)
    {
        xa := new int[0];
        reveal_BEDigitSeqToInt_private();
        return;
    }
    xa := new int[1];
    xa[0] := x;
    lemma_2toX();
    assert xa[..]==[x]; //- OBSERVE
    lemma_BEDigitSeqToInt_singleton(power2(32), x);
}

predicate IsZeroValue_def(a:seq<int>)
    requires IsWordSeq(a);
{
    forall j :: 0<=j<|a| ==> a[j]==0
}

lemma lemma_IsZeroValue(a:seq<int>)
    requires IsWordSeq(a);
    ensures IsZeroValue_def(a) <==> (BEWordSeqToInt(a[..])==0);
    decreases |a|;
{
    reveal_BEDigitSeqToInt_private();
    lemma_2toX();

    if (IsZeroValue_def(a))
    {
        if (0<|a|)
        {
            lemma_IsZeroValue(a[0..|a|-1]);
        }
    } else {
        lemma_BEDigitSeqToInt_bound(power2(32), a[0..|a|-1]);
        if (a[|a|-1]!=0) {
            calc {
                BEWordSeqToInt(a[..]);
                    { reveal_BEDigitSeqToInt_private(); }
                BEWordSeqToInt(a[0..|a|-1])*power2(32) + a[|a|-1];
                > 0;
            }
        } else {
            if (IsZeroValue_def(a[0..|a|-1]))
            {
                forall (i | 0<=i<|a|)
                    ensures a[i]==0;
                {
                    if (i<|a|-1)
                    {
                        assert a[i]==a[0..|a|-1][i];    //- OBSERVE SEQ
                    }
                }
                assert false;
            }
    //-        assert !IsZeroValue_def(a[0..|a|-1]);
            lemma_IsZeroValue(a[0..|a|-1]);
//-            assert BEWordSeqToInt(a)!=0;
        }
    }
}

predicate IsZeroValue(a:seq<int>)
    requires IsWordSeq(a);
    ensures IsZeroValue(a) <==> (BEWordSeqToInt(a[..])==0);
{
    lemma_IsZeroValue(a);
    IsZeroValue_def(a)
}


method FatNatIsZero(a:array<int>) returns (rc:bool)
    requires a!=null;
    requires IsWordSeq(a[..]);
    ensures rc <==> IsZeroValue(a[..]);
{
    var t := CountTopZeroWords(a);
    rc := t==a.Length;
}

method FatNatZero() returns (Z:array<int>)
    ensures Z!=null;
    ensures IsWordSeq(Z[..]);
    ensures BEWordSeqToInt(Z[..]) == 0;
    ensures fresh(Z);
{
    Z := new int[0];
    assert IsZeroValue(Z[..]);
}

method TrimLeadingZerosArray(ghost pv:int, M:array<int>) returns (N:array<int>)
    requires 1<pv;
    requires M!=null;
    requires IsDigitSeq(pv, M[..]);
    ensures N!=null;
    ensures N.Length <= M.Length;
    ensures N.Length==0 || 0<N[0];
    ensures M[M.Length-N.Length..] == N[..];
    ensures IsDigitSeq(pv, N[..]);
    ensures BEDigitSeqToInt(pv, M[..]) == BEDigitSeqToInt(pv, N[..]);
    ensures fresh(N);
{
    
    
    
    var skip := CountTopZeroWords(M);
    var nlen := M.Length - skip;
    N := new int[nlen];
    CopyArray(N, 0, M, skip, nlen);
    assert M[skip..] == M[skip..skip+nlen]; //- OBSERVE SEQ
    assert N[0..nlen] == N[..];  //- OBSERVE SEQ
    lemma_LeadingZeros(pv, N[..], M[..]);
}

method PadArrayLeft(zeros:nat, a:array<int>) returns (c:array<int>)
    requires a!=null;
    ensures c!=null;
    ensures fresh(c);
    ensures c.Length == zeros+a.Length;
    ensures forall i :: 0<=i<zeros ==> c[i]==0;
    ensures c[zeros..] == a[..];
    ensures IsByteSeq(a[..]) ==> IsByteSeq(c[..]);
    ensures IsWordSeq(a[..]) ==> IsWordSeq(c[..]);
{
    var outlen := zeros+a.Length;
    c := new int[outlen];

    var j := 0;
    while (j<zeros)
        invariant 0<=j<=zeros;
        invariant forall i :: 0 <= i < j ==> c[i]==0;
    {
        c[j] := 0;
        j := j + 1;
    }

    while (j<outlen)
        invariant zeros<=j<=outlen;
        invariant forall i :: 0<=i<zeros ==> c[i]==0;
        invariant c[zeros..j] == a[..j-zeros];
    {
        c[j] := a[j-zeros];
        assert c[zeros..j+1] == c[zeros..j] + [c[j]];
        assert a[..j+1-zeros] == a[..j-zeros] + [a[j-zeros]];
        j := j + 1;
    }
    assert c[zeros..] == c[zeros..j];   //- OBSERVE SEQ
    assert a[..j-zeros] == a[..];   //- OBSERVE SEQ
    lemma_2toX();
    assert power2(8)==256;
    //- ensures IsByteSeq(a[..]) ==> IsByteSeq(c[..]);
    if (IsByteSeq(a[..]))
    {
        forall (i | 0<=i<c.Length)
            ensures 0<=c[i]<power2(8);
        {
            if (i<zeros)
            {
                assert c[i]==0;
            }
            else
            {
                assert c[i]==a[i-zeros];
            }
        }
    }
    if (IsWordSeq(a[..]))
    {
        forall (i | 0<=i<c.Length)
            ensures 0<=c[i]<power2(32);
        {
            if (i<zeros)
            {
                assert c[i]==0;
            }
            else
            {
                assert c[i]==a[i-zeros];
            }
        }
    }
}

