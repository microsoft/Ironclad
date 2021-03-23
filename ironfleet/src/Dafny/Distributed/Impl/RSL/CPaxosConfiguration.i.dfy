include "../../Protocol/RSL/Constants.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "PacketParsing.i.dfy"
include "ParametersState.i.dfy"

module LiveRSL__CPaxosConfiguration_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__Constants_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__ParametersState_i
import opened Common__NodeIdentity_i
import opened Common__SeqIsUniqueDef_i
import opened Common__UdpClient_i
import opened Collections__Seqs_i

datatype CPaxosConfiguration = CPaxosConfiguration(replica_ids:seq<EndPoint>)

predicate CPaxosConfigurationIsAbstractable(config:CPaxosConfiguration)
{
  && (forall e :: e in config.replica_ids ==> EndPointIsValidIPV4(e))
  && SeqIsUnique(config.replica_ids)
}

predicate CPaxosConfigurationIsValid(config:CPaxosConfiguration)
  ensures CPaxosConfigurationIsValid(config) ==> SeqIsUnique(config.replica_ids)
{
  && 0 < |config.replica_ids| < 0xffff_ffff_ffff_ffff
  && CPaxosConfigurationIsAbstractable(config)
  && LMinQuorumSize(AbstractifyCPaxosConfigurationToConfiguration(config)) <= |config.replica_ids|
}

function method PaxosEndPointIsValid(endPoint:EndPoint, config:CPaxosConfiguration) : bool
  requires CPaxosConfigurationIsValid(config)
{
  EndPointIsValidIPV4(endPoint)
}


function AbstractifyCPaxosConfigurationToConfiguration(config:CPaxosConfiguration) : LConfiguration
  requires CPaxosConfigurationIsAbstractable(config)
{
  LConfiguration({}, AbstractifyEndPointsToNodeIdentities(config.replica_ids))
}

predicate ReplicaIndexValid(index:uint64, config:CPaxosConfiguration)
{
  0 <= index as int < |config.replica_ids|
}

predicate ReplicaIndicesValid(indices:seq<uint64>, config:CPaxosConfiguration)
{
  forall i :: 0 <= i < |indices| ==> ReplicaIndexValid(indices[i], config)
}

lemma lemma_WFCPaxosConfiguration(config:CPaxosConfiguration)
  ensures && CPaxosConfigurationIsAbstractable(config)
          && 0 < |config.replica_ids|
          ==> && CPaxosConfigurationIsAbstractable(config)
              && WellFormedLConfiguration(AbstractifyCPaxosConfigurationToConfiguration(config));
{
  if CPaxosConfigurationIsAbstractable(config) && 0 < |config.replica_ids|
  {
    //lemma_CardinalityNonEmpty(config.replica_ids);
    var e := config.replica_ids[0];
    assert AbstractifyEndPointToNodeIdentity(e) in AbstractifyCPaxosConfigurationToConfiguration(config).replica_ids;
    assert 0 < |AbstractifyCPaxosConfigurationToConfiguration(config).replica_ids|;
    var r_replicaIds := AbstractifyCPaxosConfigurationToConfiguration(config).replica_ids;
    forall i, j | 0 <= i < |r_replicaIds| && 0 <= j < |r_replicaIds|
      ensures r_replicaIds[i] == r_replicaIds[j] ==> i == j
    {
      if r_replicaIds[i] == r_replicaIds[j] {
        if i != j {
          assert r_replicaIds[i] == AbstractifyEndPointToNodeIdentity(config.replica_ids[i]);
          assert r_replicaIds[j] == AbstractifyEndPointToNodeIdentity(config.replica_ids[j]);
          lemma_AbstractifyEndPointToNodeIdentity_injective(config.replica_ids[i], config.replica_ids[j]);
          assert config.replica_ids[i] == config.replica_ids[j];
          reveal_SeqIsUnique();
          assert i == j;
          assert false;
        }
      }
    }
  }
}

predicate WFCPaxosConfiguration(config:CPaxosConfiguration)
  ensures WFCPaxosConfiguration(config) ==>
            && CPaxosConfigurationIsAbstractable(config)
            && WellFormedLConfiguration(AbstractifyCPaxosConfigurationToConfiguration(config))
{
  lemma_WFCPaxosConfiguration(config);
  && CPaxosConfigurationIsAbstractable(config)
  && 0 < |config.replica_ids|
}

lemma lemma_MinQuorumSizeLessThanReplicaCount(config:CPaxosConfiguration)
  requires CPaxosConfigurationIsAbstractable(config)
  requires |config.replica_ids| > 0
  requires SeqIsUnique(config.replica_ids)
  ensures LMinQuorumSize(AbstractifyCPaxosConfigurationToConfiguration(config)) <= |config.replica_ids|
{
  assert |config.replica_ids| > 0;
  var h_config := AbstractifyCPaxosConfigurationToConfiguration(config);
  lemma_AbstractifyEndPointsToNodeIdentities_properties(config.replica_ids);
  assert |h_config.replica_ids| == |config.replica_ids|;
  assert |h_config.replica_ids| > 0;
}

method CGetReplicaIndex(replica:EndPoint, config:CPaxosConfiguration) returns (found:bool, index:uint64)
  requires CPaxosConfigurationIsValid(config)
  requires EndPointIsValidIPV4(replica)
  ensures  found ==> ReplicaIndexValid(index, config) && config.replica_ids[index] == replica
  ensures  found ==> GetReplicaIndex(AbstractifyEndPointToNodeIdentity(replica), AbstractifyCPaxosConfigurationToConfiguration(config)) == index as int
  ensures !found ==> !(replica in config.replica_ids)
  ensures !found ==> !(AbstractifyEndPointToNodeIdentity(replica) in AbstractifyEndPointsToNodeIdentities(config.replica_ids))
{
  var i:uint64 := 0;
  lemma_AbstractifyEndPointsToNodeIdentities_properties(config.replica_ids);

  while i < |config.replica_ids| as uint64
    invariant i < |config.replica_ids| as uint64
    invariant forall j :: 0 <= j < i ==> config.replica_ids[j] != replica
  {
    if replica == config.replica_ids[i] {
      found := true;
      index := i;
    
      ghost var r_replica := AbstractifyEndPointToNodeIdentity(replica);
      ghost var r_replicas := AbstractifyCPaxosConfigurationToConfiguration(config).replica_ids;
      assert r_replica == r_replicas[index];
      assert ItemAtPositionInSeq(r_replicas, r_replica, index as int);
      calc ==> {
        true;
          { reveal_SeqIsUnique(); }
        forall j :: 0 <= j < |config.replica_ids| && j != i as int ==> config.replica_ids[j] != replica;
      }

      if exists j :: 0 <= j < |r_replicas| && j != index as int && ItemAtPositionInSeq(r_replicas, r_replica, j) {
        ghost var j :| 0 <= j < |r_replicas| && j != index as int && ItemAtPositionInSeq(r_replicas, r_replica, j);
        assert r_replicas[j] == r_replica;
        assert AbstractifyEndPointToNodeIdentity(config.replica_ids[j]) == r_replica;
        lemma_AbstractifyEndPointToNodeIdentity_injective(config.replica_ids[i], config.replica_ids[j]);
        assert false;
      }
      assert forall j :: 0 <= j < |r_replicas| && j != index as int ==> !ItemAtPositionInSeq(r_replicas, r_replica, j);
      assert FindIndexInSeq(r_replicas, r_replica) == index as int;
      return;
    }

    if i == (|config.replica_ids| as uint64) - 1 {
      found := false;
      return;
    }

    i := i + 1;
  }
  found := false;
}

} 
