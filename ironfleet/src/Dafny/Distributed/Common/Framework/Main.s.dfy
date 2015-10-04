include "../../Common/Native/Io.s.dfy"
//include "Host.s.dfy"
include "DistributedSystem.s.dfy"
include "AbstractService.s.dfy"
include "../Collections/Seqs.s.dfy"

abstract module Main_s {
    //import opened Host as Host_s
    import opened DistributedSystem_s
    import opened AbstractService_s
    import opened Collections__Seqs_s

    method Main(ghost env:HostEnvironment) returns (exitCode:int)
        requires env != null && env.Valid() && env.ok.ok();
        requires env.udp.history() == [];
        requires |env.constants.CommandLineArgs()| >= 2;
        modifies set x:object | true;     // Everything!
        decreases *;
    {

        var ok, host_state, config, servers, clients, id := HostInitImpl(env);
        assert ok ==> HostInit(host_state, config, id);

        while (ok) 
            invariant ok ==> HostStateInvariants(host_state, env);
            invariant ok ==> env != null && env.Valid() && env.ok.ok();
            decreases *;
        {
            ghost var old_udp_history := env.udp.history();
            ghost var old_state := host_state;

            ghost var recvs, clocks, sends, ios;
            ok, host_state, recvs, clocks, sends, ios := HostNextImpl(env, host_state);

            if ok {
                // Correctly executed one action
                assert HostNext(old_state, host_state, ios);

                // Connect the low-level IO events to the spec-level IO events
                assert recvs + clocks + sends == ios;

                // These obligations enable us to apply reduction
                assert env.udp.history() == old_udp_history + recvs + clocks + sends;
                assert forall e :: (e in recvs ==> e.LIoOpReceive?) 
                                && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) 
                                && (e in sends ==> e.LIoOpSend?);
                assert |clocks| <= 1;
            }
        }
    }

    /*
    lemma RefinementProof(config:ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<seq<<ServiceState>>)
        requires |db| > 0;
        requires DS_Init(db[0], config);
        requires forall i :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        ensures  |sb| == |db|;
        ensures  forall i :: 0 <= i < |sb| ==> |sb[i]| >= 1;
        ensures  Service_Init(sb[0][0]);
        ensures  forall i :: 0 <= i < |sb| - 1 ==> last(sb[i]) == sb[i+1][0];
        ensures  forall i,j :: 0 <= i < |sb| && 0 <= j < |sb[i]| - 1 ==> Service_Next(sb[i][j], sb[i][j+1]);
        ensures  forall i :: 0 <= i < |sb| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i][0]);
    */

    lemma RefinementProof(config:ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<ServiceState>, cm:seq<int>)
        requires |db| > 0;
        requires DS_Init(db[0], config);
        requires forall i :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        ensures  |db| == |cm|;
        ensures  cm[0] == 0;                                            // Beginnings match
        ensures  forall i :: 0 <= i < |cm| ==> 0 <= cm[i] < |sb|;       // Mappings are in bounds
        ensures  forall i :: 0 <= i < |cm| - 1 ==> cm[i] <= cm[i+1];    // Mapping is monotonic
        ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].servers));
        ensures  forall i :: 0 <= i < |sb| - 1 ==> Service_Next(sb[i], sb[i+1]);
        ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[cm[i]]);


    /*
    lemma DistributedSystemRefinesSpec_Init(s:DS_State, config:ProtocolConfiguration)
        requires DS_Init(s, config);
        requires ProtocolConfigurationInit(config, mapdomain(s.servers), s.clients);
        ensures  Spec_Init(DS_AbstractState(s), DS_AbstractConfig(config));

      // Still needs some work to talk about ios

//    lemma DistributedSystemRefinesSpec_Next(s:DS_State, s':DS_State)
//        requires DS_Next(s, s');
//        ensures  exists states :: IsAbstractStateAbstractionSequenceOf(states, DS_AbstractState(s), DS_AbstractState(s'));
*/

}
