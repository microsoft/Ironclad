include "Util.i.dfy"
include "NetClient.i.dfy"
include "SeqIsUnique.i.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "GenericRefinement.i.dfy"
include "../../Common/Collections/Sets.i.dfy"

module Common__NodeIdentity_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened Common__Util_i
import opened Common__NetClient_i
import opened Common__SeqIsUniqueDef_i
import opened Common__SeqIsUnique_i
import opened Concrete_NodeIdentity_i
import opened GenericRefinement_i
import opened Collections__Sets_i
import opened Math__power2_s
import opened Math__power2_i

//////////////////////////////////////////////////////////////////////////////
//  Useful for EndPoint index to node index conversions

function {:opaque} AbstractifySeqOfUint64sToSeqOfInts(s:seq<uint64>) : seq<int>
  ensures |AbstractifySeqOfUint64sToSeqOfInts(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> s[i] as int == AbstractifySeqOfUint64sToSeqOfInts(s)[i]
{
  MapSeqToSeq(s, uint64_to_int)
}

function {:opaque} AbstractifySeqOfUint64sToSetOfInts(s:seq<uint64>) : set<int>
  requires SeqIsUnique(s)
  ensures forall x :: x in s ==> (x as int in AbstractifySeqOfUint64sToSetOfInts(s))
{
  var unique_set := UniqueSeqToSet(s);
  set i | i in unique_set :: i as int
}

lemma lemma_AbstractifySeqOfUint64sToSetOfInts_properties(s:seq<uint64>)
  requires SeqIsUnique(s)
  ensures |AbstractifySeqOfUint64sToSetOfInts(s)| == |s|
  ensures forall i {:auto_trigger} :: (i in s <==> i as int in AbstractifySeqOfUint64sToSetOfInts(s))
{
  var unique_set := UniqueSeqToSet(s);
  var r_s := AbstractifySeqOfUint64sToSetOfInts(s);

  reveal AbstractifySeqOfUint64sToSetOfInts();
  lemma_MapSetCardinality(unique_set, r_s, uint64_to_int);
  lemma_seqs_set_cardinality(s, unique_set);
  lemma_seqs_set_membership(s, unique_set);
}


lemma lemma_AbstractifySeqOfUint64sToSetOfInts_append(original_seq:seq<uint64>, new_index:uint64)
  requires SeqIsUnique(original_seq)
  ensures  var r_original_set := AbstractifySeqOfUint64sToSetOfInts(original_seq);
           AbstractifySeqOfUint64sToSetOfInts(AppendToUniqueSeqMaybe(original_seq, new_index)) == r_original_set + {new_index as int}
{
  var appended_seq := AppendToUniqueSeqMaybe(original_seq, new_index);
  var r_set := AbstractifySeqOfUint64sToSetOfInts(appended_seq);
  var r_original_set := AbstractifySeqOfUint64sToSetOfInts(original_seq);
  var new_set := r_original_set + {new_index as int};
  assert new_index in appended_seq;
  assert new_index as int in r_set;
  assert forall x :: x in original_seq ==> x as int in r_original_set;
  assert forall x :: x in original_seq ==> x in appended_seq;

  forall rId | rId in r_set
    ensures rId in new_set
  {
    lemma_AbstractifySeqOfUint64sToSetOfInts_properties(appended_seq);
    lemma_AbstractifySeqOfUint64sToSetOfInts_properties(original_seq);
    reveal AbstractifySeqOfUint64sToSetOfInts();
  }

  forall rId | rId in new_set
    ensures rId in r_set
  {
    lemma_AbstractifySeqOfUint64sToSetOfInts_properties(appended_seq);
    lemma_AbstractifySeqOfUint64sToSetOfInts_properties(original_seq);
    reveal AbstractifySeqOfUint64sToSetOfInts();
  }
}

//////////////////////////////////////////////////////////////////////////////
// NodeIdentity

predicate EndPointIsAbstractable(endpoint:EndPoint)
{
  true
}

function AbstractifyEndPointToNodeIdentity(endpoint:EndPoint) : NodeIdentity
{
  endpoint
}

predicate SeqOfEndPointsIsAbstractable(endPoints:seq<EndPoint>)
{
  forall e :: e in endPoints ==> EndPointIsAbstractable(e)
}

function {:opaque} AbstractifyEndPointsToNodeIdentities(endPoints:seq<EndPoint>) : seq<NodeIdentity>
  requires forall e :: e in endPoints ==> EndPointIsAbstractable(e)
  ensures |AbstractifyEndPointsToNodeIdentities(endPoints)| == |endPoints|
  ensures forall i :: 0<=i<|endPoints| ==> AbstractifyEndPointToNodeIdentity(endPoints[i]) == AbstractifyEndPointsToNodeIdentities(endPoints)[i]
{
  if |endPoints| == 0 then []
  else [AbstractifyEndPointToNodeIdentity(endPoints[0])] + AbstractifyEndPointsToNodeIdentities(endPoints[1..])
}

lemma lemma_AbstractifyEndPointToNodeIdentity_injective(e1:EndPoint, e2:EndPoint)
  requires AbstractifyEndPointToNodeIdentity(e1) == AbstractifyEndPointToNodeIdentity(e2)
  ensures e1==e2
{
}

lemma lemma_AbstractifyEndPointToNodeIdentity_injective_forall()
  ensures forall e1, e2 {:trigger AbstractifyEndPointToNodeIdentity(e1),AbstractifyEndPointToNodeIdentity(e2)} ::
            AbstractifyEndPointToNodeIdentity(e1) == AbstractifyEndPointToNodeIdentity(e2) ==> e1 == e2;
{
  forall e1, e2 | AbstractifyEndPointToNodeIdentity(e1) == AbstractifyEndPointToNodeIdentity(e2)
    ensures e1 == e2
  {
    lemma_AbstractifyEndPointToNodeIdentity_injective(e1, e2);
  }
}

lemma lemma_seqs_set_cardinality_EndPoint(Q:seq<EndPoint>, S:set<EndPoint>)
  requires SeqIsUnique(Q)
  requires S == set e | e in Q
  ensures |Q| == |S|
  decreases |Q|
{
  lemma_seqs_set_cardinality(Q, S);
}

lemma lemma_sets_cardinality_EndPoint(S:set<EndPoint>, T:set<NodeIdentity>)
  requires forall e :: e in S ==> EndPointIsAbstractable(e)
  requires T == set e | e in S :: AbstractifyEndPointToNodeIdentity(e)
  ensures |S| == |T|
  decreases |S|
{
  if (S=={}) {
    return;
  }
  var s0 :| s0 in S;
  var Sr := S - {s0};
  var Tr := T - {AbstractifyEndPointToNodeIdentity(s0)};
  assert |S| == |Sr| + 1;
  assert |T| == |Tr| + 1;
  lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
  lemma_sets_cardinality_EndPoint(Sr, Tr);
}

lemma lemma_AbstractifyEndPointsToNodeIdentities_properties(endpoints:seq<EndPoint>)
  requires SeqIsUnique(endpoints)
  requires SeqOfEndPointsIsAbstractable(endpoints)
  ensures |AbstractifyEndPointsToNodeIdentities(endpoints)| == |endpoints|
  ensures forall e :: e in endpoints ==> AbstractifyEndPointToNodeIdentity(e) in AbstractifyEndPointsToNodeIdentities(endpoints)
  ensures forall e :: EndPointIsAbstractable(e) ==> (e in endpoints <==> AbstractifyEndPointToNodeIdentity(e) in AbstractifyEndPointsToNodeIdentities(endpoints))
{
  forall e |  EndPointIsAbstractable(e)
    ensures e in endpoints <==> AbstractifyEndPointToNodeIdentity(e) in AbstractifyEndPointsToNodeIdentities(endpoints)
  {
    if e in endpoints {
      assert AbstractifyEndPointToNodeIdentity(e) in AbstractifyEndPointsToNodeIdentities(endpoints);
    }

    if AbstractifyEndPointToNodeIdentity(e) in AbstractifyEndPointsToNodeIdentities(endpoints) {
      lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
      assert e in endpoints;
    }
  }
}

lemma lemma_AbstractifyEndPointsToNodeIdentities_injective_elements(s1:seq<EndPoint>, s2:seq<EndPoint>)
  requires forall e :: e in s1 ==> EndPointIsAbstractable(e)
  requires forall e :: e in s2 ==> EndPointIsAbstractable(e)
  requires AbstractifyEndPointsToNodeIdentities(s1) == AbstractifyEndPointsToNodeIdentities(s2)
  ensures  forall e :: e in s1 <==> e in s2
{
  reveal AbstractifyEndPointsToNodeIdentities();
  lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
}

lemma lemma_AbstractifyEndPointsToNodeIdentities_injective(s1:seq<EndPoint>, s2:seq<EndPoint>)
  requires forall e :: e in s1 ==> EndPointIsAbstractable(e)
  requires forall e :: e in s2 ==> EndPointIsAbstractable(e)
  requires AbstractifyEndPointsToNodeIdentities(s1) == AbstractifyEndPointsToNodeIdentities(s2)
  ensures  s1 == s2;
{
  reveal AbstractifyEndPointsToNodeIdentities();
  lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
}

//////////////////////////////////////////////////////////
// Reversing the process of refining a node identity
//////////////////////////////////////////////////////////

predicate NodeIdentityIsRefinable(id:NodeIdentity)
{
  true
}

// Give Dafny a symbol handle for this choose (:|) expression
function{:opaque} RefineNodeIdentityToEndPoint(id:NodeIdentity) : EndPoint
  ensures  NodeIdentityIsRefinable(id) ==> EndPointIsAbstractable(RefineNodeIdentityToEndPoint(id))
  ensures  NodeIdentityIsRefinable(id) ==> AbstractifyEndPointToNodeIdentity(RefineNodeIdentityToEndPoint(id)) == id
{
  id
}


} 
