include "Configuration.i.dfy"
include "Parameters.i.dfy"

module LiveRSL__Constants_i {
import opened LiveRSL__Configuration_i
import opened LiveRSL__Parameters_i

datatype LConstants = LConstants(
  config:LConfiguration,
  params:LParameters
  )

datatype LReplicaConstants = LReplicaConstants(
  my_index:int,
  all:LConstants
  )

predicate LReplicaConstantsValid(c:LReplicaConstants)
{
  0 <= c.my_index < |c.all.config.replica_ids|
}

} 
