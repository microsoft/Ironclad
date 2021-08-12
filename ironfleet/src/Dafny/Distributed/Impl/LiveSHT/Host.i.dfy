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
    import opened LiveSHT__NetSHT_i
    import opened LiveSHT__Unsendable_i
    import opened CmdLineParser_i
    import opened ShtCmdLineParser_i 
    export Spec
        provides Native__Io_s, Environment_s, Native__NativeTypes_s
        provides HostState
        provides ConcreteConfiguration
        provides HostInit, HostNext, ConcreteConfigInit, HostStateInvariants, ConcreteConfigToServers
        provides ParseCommandLineConfiguration, ArbitraryObject
        provides HostInitImpl, HostNextImpl
    export All reveals *


    datatype CScheduler = CScheduler(ghost sched:LScheduler, scheduler_impl:SchedulerImpl?)

    type HostState = CScheduler
    type ConcreteConfiguration = ConstantsState

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
           NetEventLogIsAbstractable(ios)
        && OnlySentMarshallableData(ios)
        && (   LScheduler_Next(host_state.sched, host_state'.sched, AbstractifyRawLogToIos(ios))
            || HostNextIgnoreUnsendable(host_state.sched, host_state'.sched, ios))
    }

    predicate ConcreteConfigInit(config:ConcreteConfiguration)
    {
        ConstantsStateIsValid(config)
     && config.rootIdentity in config.hostIds
     //&& (forall i :: 0 <= i < |config.hostIds| ==> c
    }

    function ConcreteConfigToServers(config:ConcreteConfiguration) : set<EndPoint>
    {
      MapSeqToSet(config.hostIds, x=>x)
    }

    function ParseCommandLineConfiguration(args:seq<seq<byte>>) : ConcreteConfiguration
    {
       sht_cmd_line_parsing(args)
    }
    
    method {:timeLimitMultiplier 4} HostInitImpl(
      ghost env:HostEnvironment,
      netc:NetClient,
      args:seq<seq<byte>>
      ) returns (
      ok:bool,
      host_state:HostState
      )
    {
        var config:ConstantsState, my_index:uint64;
        var id := EndPoint(netc.MyPublicKey());
        ok, config, my_index := parse_cmd_line(id, args);
        if !ok { return; }
        assert config.hostIds[my_index] in config.hostIds;
        
        var scheduler := new SchedulerImpl();
//        calc {
//            constants.myIndex as int;
//                { reveal_SeqIsUnique(); }
//            my_index as int;
//        }

        assert env.Valid() && env.ok.ok();
        
        ok := scheduler.Host_Init_Impl(config, my_index, id, netc, env);
        
        if !ok { return; }
        host_state := CScheduler(scheduler.AbstractifyToLScheduler(), scheduler);
        assert ConcreteConfigInit(config);
        assert HostInit(host_state, config, id);
    }
    
    predicate EventsConsistent(recvs:seq<NetEvent>, clocks:seq<NetEvent>, sends:seq<NetEvent>) 
    {
        forall e :: (e in recvs  ==> e.LIoOpReceive?) 
                 && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) 
                 && (e in sends  ==> e.LIoOpSend?)
    }

    ghost method RemoveRecvs(events:seq<NetEvent>) returns (recvs:seq<NetEvent>, rest:seq<NetEvent>) 
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

    predicate NetEventsReductionCompatible(events:seq<NetEvent>)
    {
        forall i :: 0 <= i < |events| - 1 ==> events[i].LIoOpReceive? || events[i+1].LIoOpSend?
    }


    lemma RemainingEventsAreSends(events:seq<NetEvent>)
        requires NetEventsReductionCompatible(events);
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

    ghost method PartitionEvents(events:seq<NetEvent>) returns (recvs:seq<NetEvent>, clocks:seq<NetEvent>, sends:seq<NetEvent>)
        requires NetEventsReductionCompatible(events);
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

    lemma NetEventsRespectReduction(s:LScheduler, s':LScheduler, 
                                    ios:seq<LSHTIo>, events:seq<NetEvent>)
        requires LIoOpSeqCompatibleWithReduction(ios);
        requires RawIoConsistentWithSpecIO(events, ios);
        ensures NetEventsReductionCompatible(events);
    {
        lemma_AbstractifyRawLogToIos_properties(events, ios);
        assert NetEventsReductionCompatible(events);
    }

    method {:timeLimitMultiplier 3} HostNextImpl(ghost env:HostEnvironment, host_state:HostState) 
        returns (ok:bool, host_state':HostState, 
                 ghost recvs:seq<NetEvent>, ghost clocks:seq<NetEvent>, ghost sends:seq<NetEvent>, 
                 ghost ios:seq<LIoOp<EndPoint, seq<byte>>>)
    {
        var okay, netEventLog, abstract_ios := host_state.scheduler_impl.Host_Next_main();
        if okay {
//            calc { 
//                Q_LScheduler_Next(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios);
//                    { reveal_Q_LScheduler_Next(); }
//                LScheduler_Next(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios);
//            }

            assert AbstractifyRawLogToIos(netEventLog) == abstract_ios;
            if LScheduler_Next(host_state.sched, host_state.scheduler_impl.AbstractifyToLScheduler(), abstract_ios)
            {
                //ProtocolIosRespectReduction(host_state.sched, host_state.scheduler_impl.AbstractifyToLScheduler(), abstract_ios);
                assert LIoOpSeqCompatibleWithReduction(abstract_ios);
            }
            NetEventsRespectReduction(host_state.sched, host_state.scheduler_impl.AbstractifyToLScheduler(), abstract_ios, netEventLog);
            recvs, clocks, sends := PartitionEvents(netEventLog);
            ios := recvs + clocks + sends; //abstract_ios;
            assert ios == netEventLog;
            host_state' := CScheduler(host_state.scheduler_impl.AbstractifyToLScheduler(), host_state.scheduler_impl);
        } else {
            recvs := [];
            clocks := [];
            sends := [];
        }
        ok := okay;
    }

}
