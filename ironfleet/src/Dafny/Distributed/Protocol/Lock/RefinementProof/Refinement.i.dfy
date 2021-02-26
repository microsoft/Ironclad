include "DistributedSystem.i.dfy"
include "../../../Services/Lock/AbstractService.s.dfy"
include "../../../Common/Collections/Sets.i.dfy"

module Refinement_i {
    import opened DistributedSystem_i
    import opened AbstractServiceLock_s`All
    import opened Collections__Maps2_s
    
    function AbstractifyGLS_State(gls:GLS_State) : ServiceState
    {
        ServiceState'(mapdomain(gls.ls.servers), gls.history)
    }
}
