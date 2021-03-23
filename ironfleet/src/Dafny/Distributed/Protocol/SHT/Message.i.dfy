include "../Common/NodeIdentity.i.dfy"
include "Keys.i.dfy"
include "../../Services/SHT/HT.s.dfy"

module SHT__Message_i {
import opened AppInterface_i`Spec
import opened Concrete_NodeIdentity_i`Spec
import opened SHT__Keys_i
import opened SHT__HT_s

datatype Message =
      GetRequest(k_getrequest:Key)
    | SetRequest(k_setrequest:Key, v_setrequest:OptionalValue)
    | Reply(k_reply:Key, v:OptionalValue)
    | Redirect(k_redirect:Key, id:NodeIdentity)
    | Shard(kr:KeyRange, recipient:NodeIdentity)
    | Delegate(range:KeyRange, h:Hashtable)

} 
