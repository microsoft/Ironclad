include "Types.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "../../Common/Collections/Seqs.i.dfy"

module LiveRSL__Configuration_i {
import opened LiveRSL__Types_i
import opened Collections__Sets_i
import opened Collections__Seqs_i
import opened Concrete_NodeIdentity_i

datatype LConfiguration = LConfiguration(
  clientIds:set<NodeIdentity>,
  replica_ids:seq<NodeIdentity>
  )

// Jay suggests using a less-general notion of quorum.
function LMinQuorumSize(c:LConfiguration) : int
{
  |c.replica_ids|/2+1
}

predicate ReplicasDistinct(replica_ids:seq<NodeIdentity>, i:int, j:int)
{
  0 <= i < |replica_ids| && 0 <= j < |replica_ids| && replica_ids[i] == replica_ids[j] ==> i == j
}

predicate WellFormedLConfiguration(c:LConfiguration)
{
  && 0 < |c.replica_ids|
  && (forall i, j :: ReplicasDistinct(c.replica_ids, i, j))
}

predicate IsReplicaIndex(idx:int, id:NodeIdentity, c:LConfiguration)
{
  && 0 <= idx < |c.replica_ids|
  && c.replica_ids[idx] == id
}

function GetReplicaIndex(id:NodeIdentity, c:LConfiguration):int
  requires id in c.replica_ids
  ensures  var idx := GetReplicaIndex(id, c);
           0 <= idx < |c.replica_ids| && c.replica_ids[idx] == id
{
  FindIndexInSeq(c.replica_ids, id)
}

lemma lemma_GetReplicaIndexIsUnique(c:LConfiguration, idx:int)
  requires WellFormedLConfiguration(c)
  requires 0 <= idx < |c.replica_ids|
  ensures  GetReplicaIndex(c.replica_ids[idx], c) == idx
{
  var j := GetReplicaIndex(c.replica_ids[idx], c);
  assert ReplicasDistinct(c.replica_ids, idx, j);
}

} 
