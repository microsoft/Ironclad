include "../../Common/Framework/Host.s.dfy"
include "SchedulerImpl.i.dfy"
include "CmdLineParser.i.dfy"

module Host_i refines Host_s {
    import opened Collections__Sets_i

    import opened Common__NodeIdentity_i
    import opened Impl_Parameters_i
    import opened SHT__ConstantsState_i
    import opened LiveSHT__Environment_i
    import opened LiveSHT__Scheduler_i
    import opened LiveSHT__SchedulerImpl_i
    import opened LiveSHT__UdpSHT_i
    import opened LiveSHT__Unsendable_i
    import opened ShtCmdLineParser_i 
    export Spec
        provides Native__Io_s, Environment_s, Native__NativeTypes_s
        provides HostState
        provides ConcreteConfiguration
        provides HostInit, HostNext, ConcreteConfigInit, HostStateInvariants, ConcreteConfigurationInvariants
        provides ParseCommandLineConfiguration, ParseCommandLineId, ArbitraryObject
        provides HostInitImpl, HostNextImpl
    export All reveals *


    datatype CScheduler = CScheduler(ghost sched:LScheduler, scheduler_impl:SchedulerImpl?)

    type HostState = CScheduler
    type ConcreteConfiguration = ConstantsState

    predicate ConcreteConfigurationInvariants(config:ConcreteConfiguration) 
    {
        ConstantsStateIsValid(config)
    }

    predicate HostStateInvariants(host_state:HostState, env:HostEnvironment)
    {
        host_state.scheduler_impl != null 
     && host_state.scheduler_impl.Valid() 
     && host_state.scheduler_impl.Env() == env
     && host_state.sched == host_state.scheduler_impl.AbstractifyToLScheduler()
    }

    predicate HostInit(host_state:HostState, config:ConcreteConfiguration, id:EndPoint)
    {
        host_state.scheduler_impl != null && host_state.scheduler_impl.Valid()
     && host_state.scheduler_impl.host.constants == config
     && host_state.scheduler_impl.host.me == id
     && LScheduler_Init(host_state.sched, 
                        AbstractifyEndPointToNodeIdentity(host_state.scheduler_impl.host.me), 
                        AbstractifyEndPointToNodeIdentity(config.rootIdentity), 
                        AbstractifyEndPointsToNodeIdentities(config.hostIds), 
                        AbstractifyCParametersToParameters(config.params))
    }

    predicate HostNext(host_state:HostState, host_state':HostState, ios:seq<LIoOp<EndPoint, seq<byte>>>)
    {
           UdpEventLogIsAbstractable(ios)
        && OnlySentMarshallableData(ios)
        && (   LScheduler_Next(host_state.sched, host_state'.sched, AbstractifyRawLogToIos(ios))
            || HostNextIgnoreUnsendable(host_state.sched, host_state'.sched, ios))
    }

    predicate ConcreteConfigInit(config:ConcreteConfiguration, servers:set<EndPoint>, clients:set<EndPoint>)
    {
        ConstantsStateIsValid(config)
     && config.rootIdentity in config.hostIds
     //&& (forall i :: 0 <= i < |config.hostIds| ==> c
     && MapSeqToSet(config.hostIds, x=>x) == servers
     && (forall e :: e in servers ==> EndPointIsAbstractable(e))
     && (forall e :: e in clients ==> EndPointIsAbstractable(e))
    }

    function ParseCommandLineConfiguration(args:seq<seq<uint16>>) : (ConcreteConfiguration, set<EndPoint>, set<EndPoint>)
    {
        var sht_config := sht_config_parsing(args);
        var endpoints_set := (set e{:trigger e in sht_config.hostIds} | e in sht_config.hostIds);
        (sht_config, endpoints_set, {})
    }

    function ParseCommandLineId(ip:seq<uint16>, port:seq<uint16>) : EndPoint
    {
        sht_parse_id(ip, port)
    }
    
    method {:timeLimitMultiplier 4} HostInitImpl(ghost env:HostEnvironment) returns (ok:bool, host_state:HostState, config:ConcreteConfiguration, ghost servers:set<EndPoint>, ghost clients:set<EndPoint>, id:EndPoint)
    {
        var init_config:ConstantsState, my_index;
        ok, init_config, my_index := parse_cmd_line(env);
        if !ok { return; }
        assert env.constants == old(env.constants);
        id := init_config.hostIds[my_index];
        config := init_config;
        
        var scheduler := new SchedulerImpl();
//        calc {
//            constants.myIndex as int;
//                { reveal_SeqIsUnique(); }
//            my_index as int;
//        }

        assert env.Valid() && env.ok.ok();
        
        ok := scheduler.Host_Init_Impl(config, id, env);
        
        if !ok { return; }
        host_state := CScheduler(scheduler.AbstractifyToLScheduler(), scheduler);
        servers := set e | e in config.hostIds;
        clients := {};
        assert env.constants == old(env.constants);
        ghost var args := env.constants.CommandLineArgs();
        ghost var tuple := ParseCommandLineConfiguration(args[0..|args|-2]);
        ghost var parsed_config, parsed_servers, parsed_clients := tuple.0, tuple.1, tuple.2;
        //assert config.config == parsed_config.config;
        assert config.params == parsed_config.params;
        //assert config == parsed_config[me := parsed_config.hostIds[my_index]];
        assert servers == parsed_servers; 
        assert clients == parsed_clients;
        assert ConcreteConfigInit(parsed_config, parsed_servers, parsed_clients);
        assert HostInit(host_state, config, id);
        assert config == parsed_config && servers == parsed_servers && clients == parsed_clients && ConcreteConfigInit(parsed_config, parsed_servers, parsed_clients);
    }
    
    predicate EventsConsistent(recvs:seq<UdpEvent>, clocks:seq<UdpEvent>, sends:seq<UdpEvent>) 
    {
        forall e :: (e in recvs  ==> e.LIoOpReceive?) 
                 && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) 
                 && (e in sends  ==> e.LIoOpSend?)
    }

    ghost method RemoveRecvs(events:seq<UdpEvent>) returns (recvs:seq<UdpEvent>, rest:seq<UdpEvent>) 
        ensures forall e :: e in recvs ==> e.LIoOpReceive?;
        ensures events == recvs + rest;
        ensures rest != [] ==> !rest[0].LIoOpReceive?;
    {
        recvs := [];
        rest := [];

        var i := 0;
        while i < |events| 
            invariant 0 <= i <= |events|;
            invariant forall e :: e in recvs ==> e.LIoOpReceive?;
            //invariant events == recvs + events[i..];
            invariant recvs == events[0..i];
        {
            if !events[i].LIoOpReceive? {
                rest := events[i..];
                return;
            }
            recvs := recvs + [events[i]];
            i := i + 1;
        }
    }

    predicate UdpEventsReductionCompatible(events:seq<UdpEvent>)
    {
        forall i :: 0 <= i < |events| - 1 ==> events[i].LIoOpReceive? || events[i+1].LIoOpSend?
    }


    lemma RemainingEventsAreSends(events:seq<UdpEvent>)
        requires UdpEventsReductionCompatible(events);
        requires |events| > 0;
        requires !events[0].LIoOpReceive?;
        ensures  forall e :: e in events[1..] ==> e.LIoOpSend?;
    {
        if |events| == 1 {
        } else {
            assert events[1].LIoOpSend?;
            RemainingEventsAreSends(events[1..]);
        }
    }

    ghost method PartitionEvents(events:seq<UdpEvent>) returns (recvs:seq<UdpEvent>, clocks:seq<UdpEvent>, sends:seq<UdpEvent>)
        requires UdpEventsReductionCompatible(events);
        ensures  events == recvs + clocks + sends;
        ensures  EventsConsistent(recvs, clocks, sends);
        ensures  |clocks| <= 1;
    {
        var rest;
        recvs, rest := RemoveRecvs(events);
        assert events[|recvs|..] == rest;
        if |rest| > 0 && (rest[0].LIoOpReadClock? || rest[0].LIoOpTimeoutReceive?) {
            clocks := [rest[0]];
            sends := rest[1..];
            RemainingEventsAreSends(rest);
        } else {
            clocks := [];
            sends := rest;
            if |rest| > 0 {
                RemainingEventsAreSends(rest);
            }
        }
    }

    /*lemma ProtocolIosRespectReduction(s:LScheduler, s':LScheduler, ios:seq<LSHTIo>)
        requires LScheduler_Next(s, s', ios);
        ensures  LIoOpSeqCompatibleWithReduction(ios);
    {
    }*/

    lemma UdpEventsRespectReduction(s:LScheduler, s':LScheduler, 
                                    ios:seq<LSHTIo>, events:seq<UdpEvent>)
        requires LIoOpSeqCompatibleWithReduction(ios);
        requires RawIoConsistentWithSpecIO(events, ios);
        ensures UdpEventsReductionCompatible(events);
    {
        lemma_AbstractifyRawLogToIos_properties(events, ios);
        assert UdpEventsReductionCompatible(events);
    }

    method {:timeLimitMultiplier 3} HostNextImpl(ghost env:HostEnvironment, host_state:HostState) 
        returns (ok:bool, host_state':HostState, 
                 ghost recvs:seq<UdpEvent>, ghost clocks:seq<UdpEvent>, ghost sends:seq<UdpEvent>, 
                 ghost ios:seq<LIoOp<EndPoint, seq<byte>>>)
    {
        var okay, udpEventLog, abstract_ios := host_state.scheduler_impl.Host_Next_main();
        if okay {
//            calc { 
//                Q_LScheduler_Next(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios);
//                    { reveal_Q_LScheduler_Next(); }
//                LScheduler_Next(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios);
//            }

            assert AbstractifyRawLogToIos(udpEventLog) == abstract_ios;
            if LScheduler_Next(host_state.sched, host_state.scheduler_impl.AbstractifyToLScheduler(), abstract_ios)
            {
                //ProtocolIosRespectReduction(host_state.sched, host_state.scheduler_impl.AbstractifyToLScheduler(), abstract_ios);
                assert LIoOpSeqCompatibleWithReduction(abstract_ios);
            }
            UdpEventsRespectReduction(host_state.sched, host_state.scheduler_impl.AbstractifyToLScheduler(), abstract_ios, udpEventLog);
            recvs, clocks, sends := PartitionEvents(udpEventLog);
            ios := recvs + clocks + sends; //abstract_ios;
            assert ios == udpEventLog;
            host_state' := CScheduler(host_state.scheduler_impl.AbstractifyToLScheduler(), host_state.scheduler_impl);
        } else {
            recvs := [];
            clocks := [];
            sends := [];
        }
        ok := okay;
    }

}
