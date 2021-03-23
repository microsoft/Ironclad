include "CPaxosConfiguration.i.dfy"

module LiveRSL__PaxosWorldState_i {
import opened LiveRSL__CPaxosConfiguration_i
import opened Native__NativeTypes_s

//////////////////////////////////////////////////////////////////////////////
// World
// TODO jonh thinks this object should be deprecated.

datatype ActionStatus = Ok | Ignore | Fail

function method f_max_uint64() : uint64
{
  0xffff_ffff_ffff_ffff
}

datatype PaxosWorldState = PaxosWorldState(good:bool, config:CPaxosConfiguration)

predicate PaxosWorldIsValid(world:PaxosWorldState)
{
  && world.good
  && CPaxosConfigurationIsValid(world.config)
}

method UpdatePaxosWorld(world:PaxosWorldState, status:ActionStatus) returns (world':PaxosWorldState)
  ensures !status.Fail? ==> world' == world
{
  if (status.Fail?)
  {
    world' := world.(good := false);
  }
  else
  {
    world' := world;
  }
}

} 
