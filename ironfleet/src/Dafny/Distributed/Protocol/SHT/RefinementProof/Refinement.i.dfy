include "../../../Services/SHT/HT.s.dfy"
include "InvDefs.i.dfy"
include "../../../Services/SHT/AbstractService.s.dfy"
include "../Message.i.dfy"
include "../../Common/NodeIdentity.i.dfy"
include "../../../Common/Collections/Maps2.i.dfy"

module SHT__Refinement_i {
import opened SHT__HT_s
import opened SHT__InvDefs_i
import opened AbstractServiceSHT_s`All
import opened AppInterface_i`Spec
import opened SHT__Message_i
import opened SHT__SHT_i
import opened Concrete_NodeIdentity_i
import opened Collections__Maps2_i
import opened Collections__Sets_i

// Frustrating:
// a set comprehension must produce a finite set, but Dafny's heuristics can't figure out how to produce a bounded set of values for 'h'
//function RefinedDomain(s:SHT_State) : set<Key>
//    requires MapComplete(s);
//{
//    set h,k | FindHashTable(s,k)==h && k in h :: k
//}

// Workaround: Add a finite bound for 'h'. This set doesn't
// restrict RefinedDomain at all, but convinces Dafny it's finite.
function AllHashTables(s:SHT_State) : set<Hashtable>
    requires MapComplete(s);
{
    (set pkt | pkt in s.network && pkt.src in AllHostIdentities(s) 
            && pkt.msg.SingleMessage? && pkt.msg.m.Delegate? :: pkt.msg.m.h)
    +
    (set id {:auto_trigger} | id in AllHostIdentities(s) :: s.hosts[id].h)
}

// This definition is opaque because it is trigger-happy (alternating quantifiers)
function {:opaque} RefinedDomain(s:SHT_State) : set<Key>
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
    requires AllDelegationsToKnownHosts(s);
    ensures forall k :: k in RefinedDomain(s) ==> k in FindHashTable(s,k);  // Exposed to eliminate 'key may not be in domain' error in Refinement() below.
{
    set h,k | (h in AllHashTables(s)) && FindHashTable(s,k)==h && (k in h) :: k
}

/*function Refinement(s:SHT_State) : Hashtable
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
    requires AllDelegationsToKnownHosts(s);
{
    // TODO this will be a little tricky around empty values -- we must
    // be sure the domains match, which probably means ensuring that
    // we don't store empty values explicitly in either system (and then
    // making sure that's an invariant).
    map k | k in RefinedDomain(s) :: FindHashTable(s,k)[k]
}*/

function Refinement(s:SHT_State) : ServiceState
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
    requires AllDelegationsToKnownHosts(s);
{
    // TODO this will be a little tricky around empty values -- we must
    // be sure the domains match, which probably means ensuring that
    // we don't store empty values explicitly in either system (and then
    // making sure that's an invariant).
    var reqs := set h,i {:trigger h.receivedRequests[i]} | h in maprange(s.hosts) && 0 <= i < |h.receivedRequests| :: h.receivedRequests[i];
    var ss := ServiceState'(
                 MapSeqToSet(s.config.hostIds, x => x),
                 map k | k in RefinedDomain(s) :: FindHashTable(s,k)[k],
                 (reqs),
                 //+ (set p | p in s.network && p.msg.SingleMessage? && p.msg.m.SetRequest? :: AppSetRequest(p.src, p.msg.seqno, p.msg.m.k_setrequest, p.msg.m.v_setrequest)),
                 set p | p in s.network && p.msg.SingleMessage? && p.msg.m.Reply? && p.src in s.hosts :: AppReply(p.msg.seqno, p.msg.m.k_reply, p.msg.m.v)
                 );
    ss

}

} 
