include "DistributedSystem.i.dfy"
include "../../../Services/Lock/AbstractService.s.dfy"

module Refinement_i {
    import opened DistributedSystem_i
    import opened AbstractServiceLock_s 

    function AbstractifyLS_State(ls:LS_State) : ServiceState
    {
        ServiceState'(mapdomain(ls.servers), ls.history)
    }

}
