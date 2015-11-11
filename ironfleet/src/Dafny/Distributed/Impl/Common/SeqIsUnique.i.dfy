include "SeqIsUniqueDef.i.dfy"
include "../../Common/Native/NativeTypes.i.dfy"

module Common__SeqIsUnique_i {
import opened Common__SeqIsUniqueDef_i
import opened Native__NativeTypes_i

function UniqueSeqToSet<X>(xs:seq<X>) : set<X>
    requires SeqIsUnique(xs);
{
    set x | x in xs
}

function{:timeLimitMultiplier 3}{:opaque} SetToUniqueSeq<X>(s:set<X>):seq<X>
    ensures  forall x :: x in SetToUniqueSeq(s) <==> x in s;
    ensures  SeqIsUnique(SetToUniqueSeq(s));
    ensures  |SetToUniqueSeq(s)| == |s|;
{
    if s == {} then
    (
        var xs:seq<X> := [];
        calc ==> {true; { reveal_SeqIsUnique(); } SeqIsUnique(xs);}
        xs
    )
    else
    (
        var x :| x in s;
        var s' := s - {x};
        var xs' := SetToUniqueSeq(s');
        calc ==> {true; { reveal_SeqIsUnique(); } SeqIsUnique(xs' + [x]);}
        xs' + [x]
    )
}

function/*TODO:{:opaque}*/ Subsequence<X>(xs:seq<X>, f:X->bool):seq<X>
    reads f.reads;
    requires forall x :: x in xs ==> f.requires(x);
    ensures  forall x :: x in Subsequence(xs, f) <==> x in xs && f(x);
// TODO:    ensures  |Subsequence(xs, f)| <= |xs|;
{
    var s := set x | x in xs && f(x);
    SetToUniqueSeq(s)
}

method SeqToSetConstruct<X>(xs:seq<X>) returns(s:set<X>)
    ensures  forall x :: x in s <==> x in xs;
    ensures  SeqIsUnique(xs) ==> |s| == |xs| && s == UniqueSeqToSet(xs);
{
    reveal_SeqIsUnique();
    s := {};
    var i := 0;
    while (i < |xs|)
        invariant 0 <= i <= |xs|;
        invariant forall x :: x in s <==> x in xs[..i];
        invariant SeqIsUnique(xs[..i]) ==> |s| == i;
    {
        s := s + {xs[i]};
        i := i + 1;
    }
}

method{:timeLimitMultiplier 5} SetToUniqueSeqConstruct<X>(s:set<X>) returns (xs:seq<X>)
    ensures SeqIsUnique(xs);
    ensures UniqueSeqToSet(xs) == s;
    ensures forall x :: x in xs <==> x in s;
    ensures |xs| == |s|;
{
    var arr := new X[|s|];
    var s1 := s;
    ghost var s2 := {};
    ghost var i := 0;
    forall ensures SeqIsUnique(arr[..i]) { reveal_SeqIsUnique(); }
    while (|s1| != 0)
        invariant 0 <= i <= |s|;
        invariant s1 + s2 == s;
        invariant s1 !! s2;
        invariant |s1| == |s| - i;
        invariant |s2| == i;
        invariant SeqIsUnique(arr[..i]);
        invariant forall x :: x in arr[..i] <==> x in s2;
    {
        reveal_SeqIsUnique();
        ghost var old_seq := arr[..i];
        var x :| x in s1;
        assert x !in old_seq;
        assert forall y {:trigger y in s2}{:trigger y in old_seq} :: y in s2 + {x} ==> y in old_seq + [x];
        arr[|s| - |s1|] := x;
        s1 := s1 - {x};
        s2 := s2 + {x};
        i := i + 1;
        assert arr[..i] == old_seq + [x];
    }
    xs := arr[..];
    assert xs == arr[..i];
}

method SubsequenceConstruct<X>(xs:seq<X>, f:X->bool) returns(xs':seq<X>)
    requires forall x :: x in xs ==> f.requires(x);
    ensures  forall x {:trigger x in xs}{:trigger x in xs'} :: x in xs' <==> x in xs && f(x);
    ensures  SeqIsUnique(xs) ==> SeqIsUnique(xs');
{
    reveal_SeqIsUnique();
    var arr := new X[|xs|];
    var i := 0;
    var j := 0;
    while (i < |xs|)
        invariant 0 <= i <= |xs|;
        invariant 0 <= j <= i;
        invariant forall x {:trigger x in xs[..i]}{:trigger x in arr[..j]} :: x in arr[..j] <==> x in xs[..i] && f(x);
        invariant SeqIsUnique(xs) ==> SeqIsUnique(arr[..j]);
    {
        ghost var old_xs := xs[..i];
        ghost var old_xs' := arr[..j];
        if (f(xs[i]))
        {
            if (SeqIsUnique(xs))
            {
                reveal_SeqIsUnique();
                assert forall k :: 0 <= k < i ==> xs[k] != xs[i];
                assert forall k :: 0 <= k < i ==> xs[..i][k] != xs[i];
                assert xs[i] !in arr[..j];
            }

            arr[j] := xs[i];
            j := j + 1;
            assert arr[..j] == old_xs' + [xs[i]];
        }
        i := i + 1;
        assert xs[..i] == old_xs + [xs[i - 1]];
    }
    xs' := arr[..j];
}

method UniqueSubsequenceConstruct<X(==)>(xs:seq<X>, f:X->bool) returns(xs':seq<X>)
    requires forall x :: x in xs ==> f.requires(x);
    ensures  forall x {:trigger x in xs}{:trigger x in xs'} :: x in xs' <==> x in xs && f(x);
    ensures  SeqIsUnique(xs');
{
    var s := set x | x in xs && f(x);
    xs' := SetToUniqueSeqConstruct(s);
}

lemma EstablishAppendToUniqueSeq<X>(xs:seq<X>, x:X, xs':seq<X>)
    requires SeqIsUnique(xs);
    requires x !in xs;
    requires xs' == xs + [x];
    ensures SeqIsUnique(xs');
    ensures x in xs';
{
    var xs'' := xs + [x];
    reveal_SeqIsUnique();
    assert SeqIsUnique(xs'');
}

function method AppendToUniqueSeq<X>(xs:seq<X>, x:X):seq<X>
    requires SeqIsUnique(xs);
    requires x !in xs;
    ensures  SeqIsUnique(AppendToUniqueSeq(xs, x));
    ensures  x in AppendToUniqueSeq(xs, x);
{
    reveal_SeqIsUnique();
    var xs' := xs + [x];
    EstablishAppendToUniqueSeq(xs, x, xs');
    xs'
}

function method AppendToUniqueSeqMaybe<X(==)>(xs:seq<X>, x:X):seq<X>
    requires SeqIsUnique(xs);
    ensures  SeqIsUnique(AppendToUniqueSeqMaybe(xs, x));
    ensures  x in AppendToUniqueSeqMaybe(xs, x);
{
    reveal_SeqIsUnique();
    if x in xs then xs
    else
    (
        var xs' := xs + [x];
        EstablishAppendToUniqueSeq(xs, x, xs');
        xs'
    )
}

lemma lemma_UniqueSeq_SubSeqsUnique<X>(whole:seq<X>, left:seq<X>, right:seq<X>)
    requires SeqIsUnique(whole);
    requires whole == left + right;
    ensures  SeqIsUnique(left);
    ensures  SeqIsUnique(right);
{
    reveal_SeqIsUnique();
}

lemma lemma_seqs_set_cardinality<T>(Q:seq<T>, S:set<T>)
    requires SeqIsUnique(Q);
    requires S == UniqueSeqToSet(Q);
    ensures |Q| == |S|;
{
    reveal_SeqIsUnique();
    if (Q==[]) {
        return;
    }
    var q0 := Q[0];
    var Qr := Q[1..];
    var Sr := UniqueSeqToSet(Qr);
    forall s | s in Sr + {q0} ensures s in S;
    {
        if (s in Sr) {
            var idx :| 0<=idx<|Qr| && Qr[idx]==s;
            assert Q[idx+1]==s;
            assert Q[idx+1] in Q;
            assert s in S;
        } else {
            assert s == q0;
            assert Q[0] == s;
            assert Q[0] in Q;
            assert s in S;
        }
    }
    forall s | s in S ensures s in Sr + {q0};
    {
        var idx :| 0<=idx<|Q| && Q[idx]==s;
        if (idx==0) {
            assert Q[0] == q0;
        } else {
            assert s == Qr[idx-1];
            assert Qr[idx-1] in Qr;
            assert s in Qr;
            assert s in Sr;
        }
        assert s in Sr + {q0};
    }
    assert S == Sr + {q0};
    lemma_seqs_set_cardinality(Qr, Sr);
}


lemma lemma_seqs_set_membership<T>(Q:seq<T>, S:set<T>)
    requires SeqIsUnique(Q);
    requires S == UniqueSeqToSet(Q);
    ensures  forall i :: (i in Q <==> i in S);
{
    reveal_SeqIsUnique();
}

} 
