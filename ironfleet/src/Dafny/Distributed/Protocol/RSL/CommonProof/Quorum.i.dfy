include "../Constants.i.dfy"
include "../Environment.i.dfy"

module CommonProof__Quorum_i {

import opened LiveRSL__Constants_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__Environment_i
import opened Concrete_NodeIdentity_i
import opened Collections__Sets_i
    
lemma lemma_SetOfElementsOfRangeNoBiggerThanRange(Q:set<int>, n:int)
  requires forall idx :: idx in Q ==> 0 <= idx < n
  requires 0 <= n
  ensures  |Q| <= n
  decreases n
{
  if n == 0
  {
    forall idx | idx in Q
      ensures false
    {
    }
    assert Q == {};
  }
  else if n-1 in Q
  {
    lemma_SetOfElementsOfRangeNoBiggerThanRange(Q - {n-1}, n-1);
  }
  else
  {
    lemma_SetOfElementsOfRangeNoBiggerThanRange(Q, n-1);
  }
}

lemma lemma_QuorumIndexOverlap(Q1:set<int>, Q2:set<int>, n:int) returns (common:int)
  requires forall idx :: idx in Q1 ==> 0 <= idx < n
  requires forall idx :: idx in Q2 ==> 0 <= idx < n
  requires |Q1| + |Q2| > n >= 0
  ensures  common in Q1
  ensures  common in Q2
  ensures  0 <= common < n
{
  if Q1 * Q2 == {}
  {
    lemma_SetOfElementsOfRangeNoBiggerThanRange(Q1 + Q2, n);
    assert false;
  }
  common :| common in Q1*Q2;
}

lemma lemma_GetIndicesFromNodes(nodes:set<NodeIdentity>, config:LConfiguration) returns (indices:set<int>)
  requires WellFormedLConfiguration(config)
  requires forall node :: node in nodes ==> node in config.replica_ids
  ensures  forall idx :: idx in indices ==> 0 <= idx < |config.replica_ids| && config.replica_ids[idx] in nodes
  ensures  forall node :: node in nodes ==> GetReplicaIndex(node, config) in indices
  ensures  |indices| == |nodes|
{
  indices := set idx | 0 <= idx < |config.replica_ids| && config.replica_ids[idx] in nodes;
  // var f := (idx requires 0 <= idx < |config.replica_ids| => config.replica_ids[idx]);
  var f := (idx => 
        if (idx >= 0  && idx < |config.replica_ids|)  then
            config.replica_ids[idx]
         else
           var end:NodeIdentity :| (true);end );
  forall idx1, idx2 | idx1 in indices && idx2 in indices && f(idx1) in nodes && f(idx2) in nodes && f(idx1) == f(idx2)
    ensures idx1 == idx2
  {
    assert ReplicasDistinct(config.replica_ids, idx1, idx2);
  }
  forall node | node in nodes
    ensures exists idx :: idx in indices && node == f(idx)
  {
    var idx := GetReplicaIndex(node, config);
    assert idx in indices && node == f(idx);
  }
  lemma_MapSetCardinalityOver(indices, nodes, f);
}

lemma lemma_GetIndicesFromPackets(packets:set<RslPacket>, config:LConfiguration) returns (indices:set<int>)
  requires WellFormedLConfiguration(config)
  requires forall p :: p in packets ==> p.src in config.replica_ids
  requires forall p1, p2 :: p1 in packets && p2 in packets && p1 != p2 ==> p1.src != p2.src
  ensures  forall idx :: idx in indices ==> 0 <= idx < |config.replica_ids| && exists p :: (p in packets && config.replica_ids[idx] == p.src)
  ensures  forall p :: p in packets ==> GetReplicaIndex(p.src, config) in indices
  ensures  |indices| == |packets|
{
  var nodes := set p | p in packets :: p.src;
  indices := lemma_GetIndicesFromNodes(nodes, config);
  lemma_MapSetCardinalityOver(packets, nodes, ((x:RslPacket)=>x.src));
}

}
