include "Host.i.dfy"
include "Parameters.i.dfy"

module SHT__Configuration_i {
import opened SHT__Host_i
import opened Protocol_Parameters_i 
import opened Concrete_NodeIdentity_i`Spec

datatype SHTConfiguration = SHTConfiguration(
    clientIds:seq<NodeIdentity>,
    hostIds:seq<NodeIdentity>,
    rootIdentity:NodeIdentity,
    params:Parameters)

predicate HostsDistinct(hostIds:seq<NodeIdentity>, i:int, j:int)
{
    0 <= i < |hostIds| && 0 <= j < |hostIds| && hostIds[i] == hostIds[j] ==> i == j
}

predicate WFSHTConfiguration(c:SHTConfiguration)
{
       0 < |c.hostIds|
    && c.rootIdentity in c.hostIds
    && (forall i, j :: HostsDistinct(c.hostIds, i, j))
}
} 
