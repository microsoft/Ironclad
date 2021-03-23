include "../../Impl/RSL/Host.i.dfy"
include "../../Common/Framework/DistributedSystem.s.dfy"

module RSL_DistributedSystem_i refines DistributedSystem_s {
  import H_s = Host_i
}
