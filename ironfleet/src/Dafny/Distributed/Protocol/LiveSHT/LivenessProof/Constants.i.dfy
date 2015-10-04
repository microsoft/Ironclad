include "../../../Common/Logic/Temporal/Rules.i.dfy"
include "Assumptions.i.dfy"

module LivenessProof__Constants_i {
import opened Temporal__Rules_i
import opened LivenessProof__Assumptions_i

///////////////////////////////
// INVARIANT LEMMAS
///////////////////////////////

lemma Lemma_AssumptionsMakeValidTransition(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int
    )
    requires IsValidBehaviorPrefix(b, c, i+1);
    requires 0 <= i;
    ensures  LSHT_Next(b[i], b[i+1]);
{
}

lemma Lemma_HostConstantsAllConsistent(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int,
    idx:int
    )
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    requires 0 <= idx < |b[i].hosts| || 0 <= idx < |c.hostIds| || 0 <= idx < |b[i].config.hostIds|;
    ensures  b[i].config == c;
    ensures  |b[i].config.hostIds| == |b[i].hosts|;
    ensures  var s := b[i].hosts[idx].host;
                s.me == c.hostIds[idx]
             && s.constants.rootIdentity == c.rootIdentity
             && s.constants.hostIds == c.hostIds
             && s.constants.params == c.params
{
    if i > 0 {
        Lemma_AssumptionsMakeValidTransition(b, c, i - 1);
        Lemma_HostConstantsAllConsistent(b, c, i-1, idx);
    } 
}

lemma Lemma_ConstantsAllConsistent(
    b:Behavior<LSHT_State>,
    c:SHTConfiguration,
    i:int
    )
    requires IsValidBehaviorPrefix(b, c, i);
    requires 0 <= i;
    ensures  b[i].config == c;
    ensures  |b[i].config.hostIds| == |b[i].hosts|;
    ensures  forall idx :: 0 <= idx < |c.hostIds| ==> 
             var s := b[i].hosts[idx].host;
                s.me == c.hostIds[idx]
             && s.constants.rootIdentity == c.rootIdentity
             && s.constants.hostIds == c.hostIds
             && s.constants.params == c.params;
{
    if i > 0 {
        Lemma_AssumptionsMakeValidTransition(b, c, i - 1);
        Lemma_ConstantsAllConsistent(b, c, i-1);
    } 
    forall idx | 0 <= idx < |c.hostIds|
        ensures var s := b[i].hosts[idx].host;
                s.me == c.hostIds[idx]
             && s.constants.rootIdentity == c.rootIdentity
             && s.constants.hostIds == c.hostIds
             && s.constants.params == c.params;
    {
        Lemma_HostConstantsAllConsistent(b, c, i, idx);
    }

}

}
