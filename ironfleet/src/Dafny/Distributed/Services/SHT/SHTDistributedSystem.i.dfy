include "../../Impl/LiveSHT/Host.i.dfy"
include "../../Common/Framework/DistributedSystem.s.dfy"

module SHT_DistributedSystem_i refines DistributedSystem_s {

    import H_s = Host_i`All

}
