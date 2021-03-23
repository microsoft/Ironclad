include "../../Common/Native/Io.s.dfy"
include "CTypes.i.dfy"

// This file is adapted from
// https://dafny.codeplex.com/SourceControl/latest#Test/dafny3/GenericSort.dfy
// and modified to apply only to COperationNumbers and to use uint64s as indices.

module LiveRSL__COperationNumberSort_i {

import opened Native__NativeTypes_s
import opened LiveRSL__CTypes_i

// In the insertion sort routine below, it's more convenient to keep track of only that
// neighboring elements of the array are sorted...
predicate NeighborSorted_COperationNumber(a: array<COperationNumber>, low: uint64, high: uint64)
  requires a.Length < 0xFFFFFFFFFFFFFFFF
  requires 0 <= low <= high <= a.Length as uint64
  reads a
{
  forall i {:trigger a[i-1].n, a[i].n} :: low < i < high ==> a[i-1].n <= a[i].n
}

predicate Sorted_COperationNumber(a: array<COperationNumber>, low: uint64, high: uint64)
  requires a.Length < 0xFFFFFFFFFFFFFFFF
  requires 0 <= low <= high <= a.Length as uint64
  reads a
{
  forall i, j :: low <= i < j < high ==> a[i].n <= a[j].n
}

// ...but we show that property to imply all pairs to be sorted.  The proof of this
// lemma uses the transitivity property.
lemma lemma_NeighborSortedImpliesSortedCOperationNumber(a: array<COperationNumber>, low: uint64, high: uint64)
  requires a.Length < 0xFFFFFFFFFFFFFFFF
  requires 0 <= low <= high <= a.Length as uint64
  requires NeighborSorted_COperationNumber(a, low, high)
  ensures Sorted_COperationNumber(a, low, high)
  decreases high - low
{
  if low != high {
    lemma_NeighborSortedImpliesSortedCOperationNumber(a, low+1, high);
    forall j | low < j < high
      ensures  a[low].n <= a[j].n
    {
      var i := low+1;
      if(i == j) {
        assert a[j-1].n <= a[j].n;
      } else {
        assert a[i-1].n <= a[i].n;
        assert a[i].n <= a[j].n;
        assert a[low].n <= a[j].n;
      }
    }
  }
}

 // Standard insertion sort method
method InsertionSortCOperationNumbers(a: array<COperationNumber>)
  modifies a
  requires a.Length < 0xFFFFFFFFFFFFFFFF
  ensures Sorted_COperationNumber(a, 0, a.Length as uint64)
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  if a.Length as uint64 == 0 { return; }
  var i:uint64 := 1;
  while i < a.Length as uint64
    invariant 0 < i <= a.Length as uint64
    invariant NeighborSorted_COperationNumber(a, 0, i)
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var j:uint64 := i;
    while 0 < j && a[j-1].n > a[j].n
      invariant 0 <= j <= i
      invariant NeighborSorted_COperationNumber(a, 0, j)
      invariant NeighborSorted_COperationNumber(a, j, i+1)
      invariant 0 < j < i ==> a[j-1].n <= a[j+1].n
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
      // The proof of correctness uses the totality property here.
      // It implies that if two elements are not previously in
      // sorted order, they will be after swapping them.
      a[j], a[j-1] := a[j-1], a[j];
      j := j - 1;
    }
    i := i + 1;
  }
  lemma_NeighborSortedImpliesSortedCOperationNumber(a, 0, a.Length as uint64);
}

}
