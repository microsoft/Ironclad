include "../../Common/Collections/Maps2.s.dfy"
include "Message.i.dfy"
include "Keys.i.dfy"

module SHT__Delegations_i {
import opened Collections__Maps2_s
import opened AppInterface_i`Spec
import opened Concrete_NodeIdentity_i`Spec
import opened SHT__HT_s
import opened SHT__Message_i
import opened SHT__Keys_i

type DelegationMap = imap<Key,NodeIdentity>

predicate DelegationMapComplete(dm:DelegationMap)
{
    forall k :: k in dm
}

function {:opaque} UpdateDelegationMap(dm:DelegationMap, newkr:KeyRange, host:NodeIdentity) : DelegationMap
    requires DelegationMapComplete(dm);
    ensures  DelegationMapComplete(UpdateDelegationMap(dm, newkr, host));
    ensures  forall k :: UpdateDelegationMap(dm, newkr, host)[k] == if KeyRangeContains(newkr, KeyPlus(k)) then host else dm[k];
{
    imap k :: if KeyRangeContains(newkr, KeyPlus(k)) then host else dm[k]
}

predicate DelegateForKeyRangeIsHost(dm:DelegationMap, kr:KeyRange, id:NodeIdentity)
    requires DelegationMapComplete(dm);
{
    forall k :: KeyRangeContains(kr, KeyPlus(k)) ==> dm[k] == id
}

// Used in proofs of refinement of implementable data structures to DelegationMap
predicate DelegationMapsAreEqualUpToKey(adm:DelegationMap, bdm:DelegationMap, khi:KeyPlus)
    requires DelegationMapComplete(adm);
    requires DelegationMapComplete(bdm);
{
    forall k :: KeyPlusLt(KeyPlus(k), khi) ==> adm[k] == bdm[k]
}

// legacy definition
function DelegateForKey(dm:DelegationMap, k:Key) : NodeIdentity
    requires DelegationMapComplete(dm);
{
    dm[k]
}


//////////////////////////////////////////////////////////////////////////////
// Functions to update a node's hash table on receipt and transmission of
// delegation messages:
//////////////////////////////////////////////////////////////////////////////

function BulkUpdateDomain(h:Hashtable, kr:KeyRange, u:Hashtable) : set<Key>
{
    // Clumsy heuristically-obviously-finite set construction
    set k | k in mapdomain(h)+mapdomain(u) && (KeyRangeContains(kr, KeyPlus(k)) ==> k in u)
}

function BulkUpdateHashtable(h:Hashtable, kr:KeyRange, u:Hashtable) : Hashtable
{
    map k {:auto_trigger} | k in BulkUpdateDomain(h, kr, u) :: if (k in u) then u[k] else h[k]
}

function BulkRemoveHashtable(h:Hashtable, kr:KeyRange) : Hashtable {
    map k | (k in h && !KeyRangeContains(kr, KeyPlus(k))) :: h[k]
}

function ExtractRange(h:Hashtable, kr:KeyRange) : Hashtable {
    map k | (k in h && KeyRangeContains(kr, KeyPlus(k))) :: h[k]
}

} 
