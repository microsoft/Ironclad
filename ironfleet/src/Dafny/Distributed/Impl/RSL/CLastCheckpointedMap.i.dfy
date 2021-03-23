include "CPaxosConfiguration.i.dfy"
include "../../Common/Native/Io.s.dfy"
include "../../Common/Collections/CountMatches.i.dfy"
include "CTypes.i.dfy"
include "../../Protocol/RSL/Acceptor.i.dfy"
include "COperationNumberSort.i.dfy"

module LiveRSL__CLastCheckpointedMap_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__Acceptor_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__COperationNumberSort_i
import opened LiveRSL__Types_i
import opened Collections__CountMatches_i

type CLastCheckpointedMap = seq<COperationNumber>

////////////////////////////////////////////////////////////
// Refining a CLastCheckpointedMap
////////////////////////////////////////////////////////////

predicate CLastCheckpointedMapIsAbstractable(s:CLastCheckpointedMap)
{
  forall ep :: ep in s ==> COperationNumberIsAbstractable(ep)
}

function {:opaque} AbstractifyCLastCheckpointedMapToOperationNumberSequence(s:CLastCheckpointedMap) : seq<OperationNumber>
  ensures |AbstractifyCLastCheckpointedMapToOperationNumberSequence(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> AbstractifyCOperationNumberToOperationNumber(s[i]) == AbstractifyCLastCheckpointedMapToOperationNumberSequence(s)[i]
{
  if |s| == 0 then []
  else [AbstractifyCOperationNumberToOperationNumber(s[0])] + AbstractifyCLastCheckpointedMapToOperationNumberSequence(s[1..])
}


//////////////////////////////////////////////////////////////////////////
// Finding the nth highest operation number
//////////////////////////////////////////////////////////////////////////

method SeqToArray<T(0)>(s:seq<T>) returns (a:array<T>)
  ensures fresh(a)
  ensures a.Length == |s|
  ensures forall i :: 0 <= i < |s| ==> s[i] == a[i]
  ensures a[..] == s
  ensures fresh(a)
{
  a := new T[|s|];

  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> s[j] == a[j]
  {
    a[i] := s[i];
    i := i + 1;
  }
}

predicate IsNthHighestValueInSequenceOfCOperationNumbers(v:COperationNumber, s:seq<COperationNumber>, n:uint64)
{
  && 0 < n as int <= |s|
  && v in s
  && CountMatchesInSeq(s, (x:COperationNumber) => x.n > v.n) < n as int
  && CountMatchesInSeq(s, (x:COperationNumber) => x.n >= v.n) >= n as int
}

predicate IsNthHighestValueInMultisetOfCOperationNumbers(v:COperationNumber, m:multiset<COperationNumber>, n:uint64)
{
  && 0 < n as int <= |m|
  && v in m
  && CountMatchesInMultiset(m, (x:COperationNumber) => x.n > v.n) < n as int
  && CountMatchesInMultiset(m, (x:COperationNumber) => x.n >= v.n) >= n as int
}

lemma lemma_SequenceToMultisetPreservesIsNthHighestValueForCOperationNumbers(v:COperationNumber, s:seq<COperationNumber>, m:multiset<COperationNumber>, n:uint64)
  requires m == multiset(s)
  ensures  IsNthHighestValueInSequenceOfCOperationNumbers(v, s, n) <==> IsNthHighestValueInMultisetOfCOperationNumbers(v, m, n)
{
  Lemma_MatchCountInSeqIsMatchCountInMultiset(s, m, (x:COperationNumber) => x.n > v.n);
  Lemma_MatchCountInSeqIsMatchCountInMultiset(s, m, (x:COperationNumber) => x.n >= v.n);
}

lemma lemma_SortedSequenceMatchCount(s:seq<COperationNumber>, k:int)
  requires |s| > 0
  requires 0 < k <= |s|
  requires forall i, j :: 0 <= i < j < |s| ==> s[i].n <= s[j].n
  ensures CountMatchesInSeq(s, (x:COperationNumber) => x.n > s[|s|-k].n) < k
  ensures CountMatchesInSeq(s, (x:COperationNumber) => x.n >= s[|s|-k].n) >= k
{
  var s' := s[1..];
  var f1 := (x:COperationNumber) => x.n > s[|s|-k].n;
  var f2 := (x:COperationNumber) => x.n >= s[|s|-k].n;

  if k == |s|
  {
    calc {
      CountMatchesInSeq(s, f1);
      CountMatchesInSeq(s', f1);
      < { Lemma_CountMatchesInSeqBounds(s', f1); }
      k;
    }

    Lemma_CountMatchesInSeqAll(s, f2);
  }
  else
  {
    var f1' := (x:COperationNumber) => x.n > s'[|s'|-k].n;
    var f2' := (x:COperationNumber) => x.n >= s'[|s'|-k].n;
    lemma_SortedSequenceMatchCount(s', k);
    assert s'[|s'|-k] == s[|s|-k];

    calc {
      CountMatchesInSeq(s, f1);
      CountMatchesInSeq(s', f1);
        { Lemma_CountMatchesInSeqSameForSameFunctions(s', f1, f1'); }
      CountMatchesInSeq(s', f1');
      < k;
    }

    calc {
      CountMatchesInSeq(s, f2);
      >= CountMatchesInSeq(s', f2);
        { Lemma_CountMatchesInSeqSameForSameFunctions(s', f2, f2'); }
      CountMatchesInSeq(s', f2');
      >= k;
    }
  }
}

lemma lemma_AbstractionOfCOperationNumberIsNthHighestValueInSequence(opn:COperationNumber, cm:CLastCheckpointedMap, n:uint64)
  requires IsNthHighestValueInSequenceOfCOperationNumbers(opn, cm, n)
  ensures  IsNthHighestValueInSequence(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifyCLastCheckpointedMapToOperationNumberSequence(cm), n as int)
{
  var f1 := (x:COperationNumber) => x.n > opn.n;
  var f2 := x => x > AbstractifyCOperationNumberToOperationNumber(opn);
  Lemma_CountMatchesInSeqCorrespondence(cm, f1, AbstractifyCLastCheckpointedMapToOperationNumberSequence(cm), f2);

  var f1' := (x:COperationNumber) => x.n >= opn.n;
  var f2' := x => x >= AbstractifyCOperationNumberToOperationNumber(opn);
  Lemma_CountMatchesInSeqCorrespondence(cm, f1', AbstractifyCLastCheckpointedMapToOperationNumberSequence(cm), f2');
}

method ComputeNthHighestValue(cm:CLastCheckpointedMap, n:uint64) returns (opn:COperationNumber)
  requires CLastCheckpointedMapIsAbstractable(cm)
  requires 0 < n as int <= |cm|
  requires |cm| < 0xffff_ffff_ffff_ffff
  ensures  IsNthHighestValueInSequence(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifyCLastCheckpointedMapToOperationNumberSequence(cm), n as int)
{
  var a := SeqToArray(cm);
  assert multiset(a[..]) == multiset(cm);
  InsertionSortCOperationNumbers(a);

  ghost var s := a[..]; 
  assert multiset(s) == multiset(cm);
  forall i, j | 0 <= i < j < |s|
    ensures s[i].n <= s[j].n
  {
    assert a[i].n <= a[j].n;
  }

  opn := a[a.Length-(n as int)];
  assert opn == s[|s|-(n as int)];

  ghost var f1 := (x:COperationNumber) => x.n > s[|s|-(n as int)].n;
  ghost var f2 := (x:COperationNumber) => x.n > opn.n;
  Lemma_CountMatchesInSeqSameForSameFunctions(s, f1, f2);
  ghost var f1' := (x:COperationNumber) => x.n >= s[|s|-(n as int)].n;
  ghost var f2' := (x:COperationNumber) => x.n >= opn.n;
  Lemma_CountMatchesInSeqSameForSameFunctions(s, f1', f2');

  lemma_SortedSequenceMatchCount(s, n as int);
  assert IsNthHighestValueInSequenceOfCOperationNumbers(opn, s, n);
  lemma_SequenceToMultisetPreservesIsNthHighestValueForCOperationNumbers(opn, s, multiset(cm), n);
  lemma_SequenceToMultisetPreservesIsNthHighestValueForCOperationNumbers(opn, cm, multiset(cm), n);
  lemma_AbstractionOfCOperationNumberIsNthHighestValueInSequence(opn, cm, n);
}


}
