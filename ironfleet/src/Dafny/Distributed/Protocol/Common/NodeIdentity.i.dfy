include "NodeIdentity.s.dfy"
include "../../Common/Native/Io.s.dfy"

module Concrete_NodeIdentity_i exclusively refines Common__NodeIdentity_s {
    import opened Native__Io_s
    type NodeIdentity = EndPoint
}
