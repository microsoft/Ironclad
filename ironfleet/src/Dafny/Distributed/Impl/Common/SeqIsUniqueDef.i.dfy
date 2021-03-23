
module Common__SeqIsUniqueDef_i {
predicate {:opaque} SeqIsUnique<X>(xs:seq<X>)
{
  forall i,j :: 0 <= i < |xs| &&  0 <= j < |xs| && xs[i] == xs[j] ==> i == j
}

} 
