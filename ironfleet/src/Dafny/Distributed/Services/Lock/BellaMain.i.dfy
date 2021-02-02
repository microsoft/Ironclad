include "../../Common/Framework/Main.s.dfy"
include "LockDistributedSystem.i.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "../../Impl/Lock/PacketParsing.i.dfy"
include "../../Impl/Lock/UdpLock.i.dfy"
include "../../Impl/Lock/Host.i.dfy"
include "AbstractService.s.dfy"
include "../../Protocol/Lock/RefinementProof/Refinement.i.dfy"
include "../../Protocol/Lock/RefinementProof/RefinementProof.i.dfy"
include "Marshall.i.dfy"

module Main_i refines Main_s {
	import opened DS_s = Lock_DistributedSystem_i
	import opened Environment_s
	import opened Concrete_NodeIdentity_i
	import opened PacketParsing_i
	import opened UdpLock_i
	import opened Host_i
	import opened AS_s = AbstractServiceLock_s
	import opened Refinement_i
	import opened RefinementProof_i
	import opened MarshallProof_i
		
	 lemma RefinementProof(config:ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<ServiceState>) 
		requires |db| > 0;
        requires DS_Init(db[0], config);
        requires forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        ensures  |db| == |sb|;
        ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].servers));
        ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
        ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i]);
	{
		var ls := DS_to_LS_State(config, db);
		var gls := LS_to_GLS_State(ls, config);
		sb := GLS_to_SB(gls, config);
	}

	lemma DS_to_LS_State(db:seq<DS_State>, config:ConcreteConfiguration) returns (ls:seq<LS_State>) 
		requires forall i :: 0 <= i < |db| - 1 ==> ds_next(i, i+1);
		requires |db| > 0;
		requires  ds_init(db[0]);
		ensures |db| == |sb|;
		ensures LS_init(ls[0], config);
		ensures forall i :: 0 <= i < |sb| - 1 ==> LS_Next(ls[i], ls[i + 1]); 
	{
		var i := 0;
		while i < |ds|
		{

			//get the HostState from the servers make to get the node
			var servers := ds[i].servers

			//initialize a LS_STATE
	        var ls_state(ds[i].environment, servers);

	        //add it to the ls sequence
	        ls := ls + ls_state;
			i := i + 1;
		}
	}  	

	lemma LS_to_GLS_State(ls:seq<LS_State>, config:ConcreteConfiguration) returns (gls:seq<GLS_State>)
		requires forall i :: 0 <= i < |ls| - 1 ==> LS_Next(i, i+1);
		requires |ls| > 0;
		requires LS_Init(ls[i], config);
		ensures |ls| == |gls|;
		ensures GLS_State_Init(gls[0], config);
		ensures forall i :: 0 <= i < |gls| - 1 ==> GLS_Next(gls[i], gls[i+1]) || gls[i] == gls[i+1];
	{
		//the init state's node would be the host
		var history := [ls[i].servers[1]];
		var i := 1;
		while i < |ls|
		{
			//find if the endpoint was a host
			history := map k | k in ls[i].servers && NodeAccept(ls[i-1].servers[k], ls[i].servers[k], //ios?) :: history[k] := ls[i].servers[k];

			//add the ls_state
			gls[i].ls := ls[i];
			i := i + 1;
		}
	}

	lemma GLS_to_SB(gls:seq<GLS_State>, 	config:ConcreteConfiguration) returns (sb:seq<ServiceState>)
		requires forall i :: 0 <= i < |gls| - 1 ==> GLS_Next(gls[i], gls[i+1]) || gls[i] == gls[i+1];
		requires |gls| > 0;
		requires GLS_Init(gls[i], config);
		ensures |gls| == |sb|;
		ensures Service_Init(sb[0], config);
		ensures forall i :: 0 <= i < |sb| - 1 ==> Service_Next(sb[i], sb[i+1]) || sb[i] == sb[i+1];
	{
		var i := 1;
		while i < |gls| 
		{
			sb[i].history := gls[i].history

			//find the host from the most recent host. 
			sb[i].host := sb[i].host + gls[i].history[|gls[i].history - 1|]

		}
	}
}
