module Collections__CountMatches_i {

function CountMatchesInSeq<T(!new)>(s:seq<T>, f:T->bool):int
    reads f.reads;
    requires forall x :: f.requires(x);
{
    if |s| == 0 then
        0
    else
        CountMatchesInSeq(s[1..], f) + if f(s[0]) then 1 else 0
}

function CountMatchesInMultiset<T(!new)>(m:multiset<T>, f:T->bool):int
    reads f.reads;
    requires forall x :: f.requires(x);
{
    if |m| == 0 then
        0
    else
        var x :| x in m;
        CountMatchesInMultiset(m - multiset{x}, f) + if f(x) then 1 else 0
}

lemma Lemma_RemovingElementAffectsCount<T>(m:multiset<T>, f:T->bool, x:T)
    requires forall u :: f.requires(u);
    requires x in m;
    ensures  CountMatchesInMultiset(m, f) - CountMatchesInMultiset(m - multiset{x}, f) == if f(x) then 1 else 0;
{
    if |m| > 0
    {
        var x' :| x' in m && CountMatchesInMultiset(m, f) - CountMatchesInMultiset(m - multiset{x'}, f) == if f(x') then 1 else 0;
        if x' != x
        {
            Lemma_RemovingElementAffectsCount(m - multiset{x'}, f, x);
            assert m - multiset{x'} - multiset{x} == m - multiset{x} - multiset{x'};
            Lemma_RemovingElementAffectsCount(m - multiset{x}, f, x');
        }
    }
}

lemma Lemma_MatchCountInSeqIsMatchCountInMultiset<T>(s:seq<T>, m:multiset<T>, f:T->bool)
    requires forall x :: f.requires(x);
    requires m == multiset(s);
    ensures  CountMatchesInSeq(s, f) == CountMatchesInMultiset(m, f);
{
    if |s| > 0
    {
        assert s == [s[0]] + s[1..];
        var m' := multiset(s[1..]);
        assert m' == m - multiset {s[0]};
        Lemma_RemovingElementAffectsCount(m, f, s[0]);
        Lemma_MatchCountInSeqIsMatchCountInMultiset(s[1..], m', f);
    }
}

predicate IsNthHighestValueInSequence(v:int, s:seq<int>, n:int)
{
       0 < n <= |s|
    && v in s
    && CountMatchesInSeq(s, x => x > v) < n
    && CountMatchesInSeq(s, x => x >= v) >= n
}

predicate IsNthHighestValueInMultiset(v:int, m:multiset<int>, n:int)
{
       0 < n <= |m|
    && v in m
    && CountMatchesInMultiset(m, x => x > v) < n
    && CountMatchesInMultiset(m, x => x >= v) >= n
}

lemma Lemma_SequenceToMultisetPreservesIsNthHighestValue(v:int, s:seq<int>, m:multiset<int>, n:int)
    requires m == multiset(s);
    ensures  IsNthHighestValueInSequence(v, s, n) <==> IsNthHighestValueInMultiset(v, m, n);
{
    Lemma_MatchCountInSeqIsMatchCountInMultiset(s, m, x => x > v);
    Lemma_MatchCountInSeqIsMatchCountInMultiset(s, m, x => x >= v);
}

lemma Lemma_CountMatchesInSeqSameForSameFunctions<T>(s:seq<T>, f1:T->bool, f2:T->bool)
    requires forall x :: f1.requires(x);
    requires forall x :: f2.requires(x);
    requires forall x :: f1(x) == f2(x);
    ensures  CountMatchesInSeq(s, f1) == CountMatchesInSeq(s, f2);
{
}

lemma Lemma_CountMatchesInSeqBounds<T>(s:seq<T>, f:T->bool)
    requires forall x :: f.requires(x);
    ensures  0 <= CountMatchesInSeq(s, f) <= |s|;
{
}

lemma Lemma_CountMatchesInSeqAll<T>(s:seq<T>, f:T->bool)
    requires forall x :: f.requires(x);
    requires forall x :: x in s ==> f(x);
    ensures  CountMatchesInSeq(s, f) == |s|;
{
}

lemma Lemma_CountMatchesInSeqCorrespondence<T1, T2>(s1:seq<T1>, f1:T1->bool, s2:seq<T2>, f2:T2->bool)
    requires forall x :: f1.requires(x);
    requires forall x :: f2.requires(x);
    requires |s1| == |s2|;
    requires forall i :: 0 <= i < |s1| ==> f1(s1[i]) == f2(s2[i]);
    ensures  CountMatchesInSeq(s1, f1) == CountMatchesInSeq(s2, f2);
{
}

function{:opaque} EnumerateMatchesInSeq<T(!new)>(s:seq<T>, f:T->bool):seq<T>
    reads f.reads;
    requires forall x :: f.requires(x);
    ensures  forall x :: (x in s && f(x)) <==> x in EnumerateMatchesInSeq(s, f);
    ensures  |EnumerateMatchesInSeq(s, f)| == CountMatchesInSeq(s, f);
{
    if |s| == 0 then
        []
    else if f(s[0]) then
        [s[0]] + EnumerateMatchesInSeq(s[1..], f)
    else
        EnumerateMatchesInSeq(s[1..], f)
}

function EnumerateIndicesOfMatchesInSeq_Helper<T(!new)>(s:seq<T>, f:T->bool, offset:int):seq<int>
    reads f.reads;
    requires forall x :: f.requires(x);
    ensures  forall i :: i in EnumerateIndicesOfMatchesInSeq_Helper(s, f, offset) ==> offset <= i < offset + |s|;
    ensures  forall i :: (0 <= i < |s| && f(s[i])) <==> i+offset in EnumerateIndicesOfMatchesInSeq_Helper(s, f, offset);
    ensures  offset == 0 ==> forall i :: (0 <= i < |s| && f(s[i])) <==> i in EnumerateIndicesOfMatchesInSeq_Helper(s, f, offset);
    ensures  |EnumerateIndicesOfMatchesInSeq_Helper(s, f, offset)| == CountMatchesInSeq(s, f);
{
    if |s| == 0 then
        []
    else if f(s[0]) then
        [offset] + EnumerateIndicesOfMatchesInSeq_Helper(s[1..], f, offset + 1)
    else
        EnumerateIndicesOfMatchesInSeq_Helper(s[1..], f, offset + 1)
}

function{:opaque} EnumerateIndicesOfMatchesInSeq<T(!new)>(s:seq<T>, f:T->bool):seq<int>
    reads f.reads;
    requires forall x :: f.requires(x);
    ensures  forall i :: (0 <= i < |s| && f(s[i])) <==> i in EnumerateIndicesOfMatchesInSeq(s, f);
    ensures  |EnumerateIndicesOfMatchesInSeq(s, f)| == CountMatchesInSeq(s, f);
{
    EnumerateIndicesOfMatchesInSeq_Helper(s, f, 0)
}

function SetOfIndicesOfMatchesInSeq_Helper<T(!new)>(s:seq<T>, f:T->bool, offset:int):set<int>
    reads f.reads;
    requires forall x :: f.requires(x);
    ensures  forall i :: i in SetOfIndicesOfMatchesInSeq_Helper(s, f, offset) ==> offset <= i < offset + |s|;
    ensures  forall i :: (0 <= i < |s| && f(s[i])) <==> i+offset in SetOfIndicesOfMatchesInSeq_Helper(s, f, offset);
    ensures  offset == 0 ==> forall i :: (0 <= i < |s| && f(s[i])) <==> i in SetOfIndicesOfMatchesInSeq_Helper(s, f, offset);
    ensures  |SetOfIndicesOfMatchesInSeq_Helper(s, f, offset)| == CountMatchesInSeq(s, f);
{
    if |s| == 0 then
        {}
    else if f(s[0]) then
        {offset} + SetOfIndicesOfMatchesInSeq_Helper(s[1..], f, offset + 1)
    else
        SetOfIndicesOfMatchesInSeq_Helper(s[1..], f, offset + 1)
}

function{:opaque} SetOfIndicesOfMatchesInSeq<T(!new)>(s:seq<T>, f:T->bool):set<int>
    reads f.reads;
    requires forall x :: f.requires(x);
    ensures  forall i :: (0 <= i < |s| && f(s[i])) <==> i in SetOfIndicesOfMatchesInSeq(s, f);
    ensures  |SetOfIndicesOfMatchesInSeq(s, f)| == CountMatchesInSeq(s, f);
{
    SetOfIndicesOfMatchesInSeq_Helper(s, f, 0)
}

}
