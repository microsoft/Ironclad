include "../Common/NodeIdentity.i.dfy"
include "CTypes.i.dfy"
include "ReplicaConstantsState.i.dfy"

module LiveRSL__MinCQuorumSize_i {
import opened Native__NativeTypes_s
import opened Common__NodeIdentity_i
import opened Common__UdpClient_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__ReplicaConstantsState_i
import opened Math__div_i

method MinCQuorumSize(config:CPaxosConfiguration) returns (quorumSize:uint64)
  requires CPaxosConfigurationIsValid(config)
  ensures quorumSize as int == LMinQuorumSize(AbstractifyCPaxosConfigurationToConfiguration(config))
  ensures quorumSize >= 0
{
  lemma_div_basics_forall();  // Needed to prove the operation below is within uint64 bounds
  quorumSize := (|config.replica_ids| as uint64)/2+1;
  ghost var c := AbstractifyCPaxosConfigurationToConfiguration(config);
  assert EndPointsAreValidIPV4(config.replica_ids);
  forall ep1, ep2 | ep1 in config.replica_ids && ep2 in config.replica_ids
                    //&& EndPointIsValidIPV4(ep1) && EndPointIsValidIPV4(ep2) 
                    && AbstractifyEndPointToNodeIdentity(ep1) == AbstractifyEndPointToNodeIdentity(ep2) 
    ensures ep1 == ep2
  {
    lemma_AbstractifyEndPointToNodeIdentity_injective(ep1, ep2);
  }
  /*
  var s := set p | p in config.replica_ids;
  lemma_SeqsSetCardinalityEndPoint(config.replica_ids, s);

  ghost var t := set e | e in s :: AbstractifyEndPointToNodeIdentity(e);
  reveal AbstractifyEndPointsToNodeIdentities();
  assert t == c.replica_ids;

  lemma_SetsCardinalityEndPoint(s, c.replica_ids);
  */
  assert |config.replica_ids| == |c.replica_ids|;

  assert quorumSize as int == (LMinQuorumSize(AbstractifyCPaxosConfigurationToConfiguration(config)));
}



} 
