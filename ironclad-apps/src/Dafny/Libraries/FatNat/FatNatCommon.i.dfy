include "../Util/seqs_and_ints.i.dfy"
include "../Util/seqs_common.i.dfy"
include "../BigNum/BigNatX86Shim.i.dfy"
include "CanonicalArrays.i.dfy"

function FatNatAddIndex(L:int, index:int, i:int) : int { L - 1 - (index + i) }

//- Treat i as a "little-endian index", so LEDigitAt(0) is the least-valued,
//- rightmost digit in a BE sequence.
static function method DigitAt(a:seq<int>, i:int) : int
{
    if (0 <= i < |a|) then a[|a|-1-i] else 0
}

//- SelectDigitRange(a, 1, 0) is the bottom digit of a BEDigitSeq
//- (just as a[0..1] is the bottom digit of a LEDigitSeq).
function method SelectDigitRange(a:seq<int>, i:int, j:int) : seq<int>
    requires 0<=j<=i<=|a|;
{
    a[|a|-i..|a|-j]
}

lemma lemma_SelectSingletonRange(a:seq<int>, i:int, j:int)
    requires 0<=j<|a|;
    requires i==j+1;
    ensures SelectDigitRange(a,i,j)==[DigitAt(a,j)];
{
    calc {
        SelectDigitRange(a, i, j);
        a[|a|-i..|a|-j];
        [a[|a|-i]];
        [a[|a|-1-j]];
        [DigitAt(a, j)];
    }
}

lemma lemma_SelectDigitNest(a:seq<int>, h1:int, l1:int, h0:int, l0:int)
    requires 0<=l1<=h1<=|a|;
    requires 0<=l0<=h0<=(h1-l1);
    ensures SelectDigitRange(SelectDigitRange(a, h1, l1), h0, l0)
        == SelectDigitRange(a, h0+l1, l0+l1);
{
    var inner := SelectDigitRange(a, h1, l1);
    assert inner == a[|a|-h1..|a|-l1];
    var outer := SelectDigitRange(inner, h0, l0);
    assert outer == inner[|inner|-h0..|inner|-l0];
    assert |inner| == h1-l1;
    var p := |a|-h1;
    var q := |a|-l1;
    var r := h1-l1-h0;
    var s := h1-l1-l0;
    assert |a[p..q][r..s]| == |a[p+r..p+s]|;
    forall (i | 0<=i<|a[p+r..p+s]|)
        ensures a[p..q][r..s][i] == a[p+r..p+s][i];
    {
        //- OBSERVE SEQ wow, Dafny really needed teeth pulled here!
    }
    assert a[p..q][r..s] == a[p+r..p+s];
//-    calc {
//-        SelectDigitRange(SelectDigitRange(a, h1, l1), h0, l0);
//-        SelectDigitRange(inner, h0, l0);
//-        a[|a|-h1..|a|-l1][h1-l1-h0..h1-l1-l0];
//-        a[p..q][r..s];
//-        a[p+r..p+s];
//-        a[h1-l1-h0+|a|-h1..h1-l1-l0+|a|-h1];
//-        a[|a|-(h0+l1)..|a|-(l0+l1)];
//-        SelectDigitRange(a, h0+l1, l0+l1);
//-    }
}

lemma lemma_BEInterpretation_Select(pv:int, A:seq<int>, i:int)
    //- i counts from right (in LE order)
    requires 1<pv;
    requires IsDigitSeq(pv, A);
    requires 0<=i<=|A|;
    ensures BEDigitSeqToInt(pv, A) ==
        BEDigitSeqToInt(pv, SelectDigitRange(A, |A|, i)) * power(pv,i) + BEDigitSeqToInt(pv, SelectDigitRange(A, i, 0));
{
    lemma_BEInterpretation(pv, A, i);
    assert A[0..|A|-i] == A[..|A|-i];   //- OBSERVE
    assert A[|A|-i..|A|] == A[|A|-i..]; //- OBSERVE
}

lemma lemma_SelectDigitSubrange(a:seq<int>, h:int, m:int, l:int)
    requires 0<=l<=m<=h<=|a|;
    ensures SelectDigitRange(a, h, l) == SelectDigitRange(a, h, m) + SelectDigitRange(a, m, l);
{
}

//- Note that SelectDigits(a,0) == [].
function method SelectDigits(a:seq<int>, i:int) : seq<int>
    requires 0<=i<=|a|;
    ensures SelectDigits(a,i) == SelectDigitRange(a,i,0);
{
    a[|a|-i..]
}


function {:opaque} MaxLen_def(ss:seq<seq<int>>) : int
    decreases |ss|;
{
    if (|ss|==0)
    then 0
    else
        var carlen := |ss[0]|;
        var cdrlen := MaxLen_def(ss[1..]);
        if (carlen > cdrlen) then carlen else cdrlen
}

lemma lemma_MaxLen(ss:seq<seq<int>>)
    ensures forall i :: 0<=i<|ss| ==> |ss[i]| <= MaxLen_def(ss);
    ensures |ss|>0 ==> exists i :: 0<=i<|ss| && |ss[i]|==MaxLen_def(ss);
{
    reveal_MaxLen_def();
    if (|ss|==0) {
    } else {
        var cdr := ss[1..];
        lemma_MaxLen(cdr);

        var carlen := |ss[0]|;
        var cdrlen := MaxLen_def(cdr);
        var i;
        if (carlen > cdrlen) {
            i := 0;
            assert 0<=i<|ss| && |ss[i]|==MaxLen_def(ss);
        } else if (|cdr|==0) {
            i := 0;
            assert 0<=i<|ss| && |ss[i]|==MaxLen_def(ss);
        } else {
            assert |cdr|>0;
            assert exists j :: 0<=j<|cdr| && |cdr[j]|==MaxLen_def(cdr);
            var j :| 0<=j<|cdr| && |cdr[j]|==MaxLen_def(cdr);
            i := j+1;
            assert 0<=i<|ss| && |ss[i]|==MaxLen_def(ss);
        }

        forall (i | 0<=i<|ss|)
            ensures |ss[i]| <= MaxLen_def(ss);
        {
            if (i==0)
            {
            }
            else
            {
                assert cdr[i-1] == ss[i];
            }
        }

    }
}





function MaxLen(ss:seq<seq<int>>) : int
    ensures forall i :: 0<=i<|ss| ==> |ss[i]| <= MaxLen(ss);
    ensures |ss|>0 ==> exists i :: 0<=i<|ss| && |ss[i]|==MaxLen(ss);
{
    lemma_MaxLen(ss);
    MaxLen_def(ss)
}

function MaxLen3(a:seq<int>, b:seq<int>, c:seq<int>) : int
    ensures |a| <= MaxLen3(a,b,c);
    ensures |b| <= MaxLen3(a,b,c);
    ensures |c| <= MaxLen3(a,b,c);
    ensures |a|==MaxLen3(a,b,c) || |b|==MaxLen3(a,b,c) || |c|==MaxLen3(a,b,c);
{
    
    
    var s3 := [a,b,c];
    assert a == s3[0];
    assert b == s3[1];
    assert c == s3[2];
    MaxLen(s3)
}

function Stretch(s:seq<int>, len:int) : seq<int>
    requires |s| <= len;
{
    RepeatDigit_premium(0, len-|s|) + s
}

//-////////////////////////////////////////////////////////////////////////////
//- Array access

static function method ArrayDigitAt(a:array<int>, i:int) : int
    requires a!=null;
    reads a;
    ensures ArrayDigitAt(a,i) == DigitAt(a[..],i);
{
    if (0 <= i < a.Length) then a[a.Length-1-i] else 0
}

function method ArrayDigitAt_add(a:array<int>, i:int) : int
    requires a!=null;
    reads a;
    ensures ArrayDigitAt_add(a,i) == DigitAt(a[..],i);
{
    if (0 <= i < a.Length) then a[a.Length-1-i] else 0
}

function method ArrayDigitAt_sub(a:array<int>, i:int) : int
    requires a!=null;
    reads a;
    ensures ArrayDigitAt_sub(a,i) == DigitAt(a[..],i);
{
    if (0 <= i < a.Length) then a[a.Length-1-i] else 0
}

function method ArrayDigitAt_cmp(a:array<int>, i:int) : int
    requires a!=null;
    reads a;
    ensures ArrayDigitAt_cmp(a,i) == DigitAt(a[..],i);
{
    if (0 <= i < a.Length) then a[a.Length-1-i] else 0
}

function method ArrayDigitAt_mul(a:array<int>, i:int) : int
    requires a!=null;
    reads a;
    ensures ArrayDigitAt_mul(a,i) == DigitAt(a[..],i);
{
    if (0 <= i < a.Length) then a[a.Length-1-i] else 0
}

predicate {:heap} WellformedFatNat(X:array<int>)
//- Word-specific wellformedness.
    reads X;
{
    X!=null && IsWordSeq(X[..])
}

function {:heap} J(X:array<int>) : int
    reads X;
    requires WellformedFatNat(X);
    ensures 0<=J(X);
{
    lemma_BEDigitSeqToInt_bound(power2(32), X[..]);
    BEWordSeqToInt(X[..])
}
