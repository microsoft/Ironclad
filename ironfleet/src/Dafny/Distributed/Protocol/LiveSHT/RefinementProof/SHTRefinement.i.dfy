include "../../../Common/Collections/Maps2.i.dfy"
include "SHT.i.dfy"
include "SchedulerRefinement.i.dfy"
include "EnvironmentRefinement.i.dfy"
include "../../SHT/RefinementProof/SHT.i.dfy"
include "../../../Common/Collections/Seqs.i.dfy"

module LiveSHT__SHTRefinement_i {
import opened Collections__Maps2_i
import opened Concrete_NodeIdentity_i`Spec
import opened LiveSHT__SHT_i
import opened LiveSHT__SchedulerRefinement_i
import opened LiveSHT__EnvironmentRefinement_i
import opened SHT__SHT_i
import opened SHT__Configuration_i
import opened Collections__Seqs_i

function LSHTConfiguration_Refine(c:SHTConfiguration) : SHTConfiguration
{
    c
}

function GetHostIndex(id:NodeIdentity, c:SHTConfiguration):int
    requires id in c.hostIds;
    ensures  var idx := GetHostIndex(id, c);
             0 <= idx < |c.hostIds| && c.hostIds[idx] == id;
{
    FindIndexInSeq(c.hostIds, id)
}

lemma Lemma_GetHostIndexIsUnique(c:SHTConfiguration, idx:int)
    requires WFSHTConfiguration(c);
    requires 0 <= idx < |c.hostIds|;
    ensures  GetHostIndex(c.hostIds[idx], c) == idx;
{
    var j := GetHostIndex(c.hostIds[idx], c);
    assert HostsDistinct(c.hostIds, idx, j);
}

function LSHTState_Refine(s:LSHT_State) : SHT_State
    requires LSHT_MapsComplete(s);
    ensures SHT_MapsComplete(LSHTState_Refine(s))
{
    SHT_State(LSHTConfiguration_Refine(s.config), LSHTEnvironment_Refine(s.environment),
               (map id {:trigger LScheduler_Refine(s.hosts[GetHostIndex(id, s.config)])} | id in s.config.hostIds :: LScheduler_Refine(s.hosts[GetHostIndex(id, s.config)])))
}

predicate LSHTState_RefinementInvariant(s:LSHT_State)
{
       |s.hosts| == |s.config.hostIds|
    && LSHT_MapsComplete(s)
    && (forall nodeIndex :: 0 <= nodeIndex < |s.config.hostIds| ==>
               LScheduler_RefinementInvariant(s.hosts[nodeIndex]))
}

predicate SHTNextOrStutter(ls:SHT_State, ls':SHT_State)
{
    ls == ls' || SHT_Next(ls, ls')
}

} 
