include "../Host.i.dfy"
include "../Configuration.i.dfy"

module SHT__SHT_i {
import opened Collections__Maps2_s
import opened SHT__Host_i
import opened SHT__Configuration_i
import opened Concrete_NodeIdentity_i`Spec
import opened SHT__Network_i

datatype SHT_State = SHT_State(
    config:SHTConfiguration,
    network:Network,
    hosts:map<NodeIdentity,Host>)

predicate SHT_MapsComplete(s:SHT_State)
{
    (forall id {:auto_trigger} :: id in s.config.hostIds <==> id in s.hosts)
}

predicate SHT_Init(c:SHTConfiguration, s:SHT_State) {
       SHT_MapsComplete(s) 
    && WFSHTConfiguration(c)
    && s.config == c
    && Network_Init(s.network)
    && (forall nodeIndex :: 0 <= nodeIndex < |s.config.hostIds| ==> var id := s.config.hostIds[nodeIndex]; 
            Host_Init(s.hosts[id], id, s.config.rootIdentity, s.config.hostIds, s.config.params))
}

predicate SHT_NextPred(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>)
    requires SHT_MapsComplete(s);
    requires SHT_MapsComplete(s');
{
       id in s.config.hostIds
    && s'.config == s.config
    && Network_Receive(s.network, id, recv)
    && Host_Next(s.hosts[id], s'.hosts[id], recv, out)
    && Network_Send(s.network, s'.network, id, out)
    // All other hosts are unchanged 
    && (forall oid {:auto_trigger} :: oid in s.config.hostIds && oid!=id ==> s'.hosts[oid]==s.hosts[oid])
}

predicate SHT_NextExternal(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>)
    requires SHT_MapsComplete(s);
    requires SHT_MapsComplete(s');
{
       id !in s.config.hostIds
    && s'.config == s.config
    && Network_Send(s.network, s'.network, id, out)
    // Hosts are unchanged 
    && s'.hosts == s.hosts
}

predicate SHT_Next(s:SHT_State, s':SHT_State)
{
       SHT_MapsComplete(s)
    && SHT_MapsComplete(s')
    && s'.config == s.config
    && mapdomain(s'.hosts) == mapdomain(s.hosts)
    && ((exists id, recv, out :: SHT_NextPred(s, s', id, recv, out))
      ||(exists id, recv, out :: SHT_NextExternal(s, s', id, recv, out)))
}

} 
