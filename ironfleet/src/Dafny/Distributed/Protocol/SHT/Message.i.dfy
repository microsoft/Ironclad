include "../Common/NodeIdentity.s.dfy"
include "Keys.i.dfy"
include "../../Services/SHT/HT.s.dfy"

module SHT__Message_i {
import opened Common__NodeIdentity_s
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
