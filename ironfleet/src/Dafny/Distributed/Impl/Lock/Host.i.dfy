include "../../Common/Framework/Host.s.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "NodeImpl.i.dfy"
include "CmdLineParser.i.dfy"

module Host_i refines Host_s {
    import opened Collections__Sets_i
    import opened Protocol_Node_i
    import opened NodeImpl_i
    import opened CmdLineParser_i
    import opened LockCmdLineParser_i
    import opened Types_i
    import opened Impl_Node_i
    import opened NetLock_i
    export Spec
        provides Native__Io_s, Environment_s, Native__NativeTypes_s
        provides HostState
        provides ConcreteConfiguration
        provides HostInit, HostNext, ConcreteConfigInit, HostStateInvariants, ConcreteConfigurationInvariants
        provides ParseCommandLineConfiguration, ArbitraryObject
        provides HostInitImpl, HostNextImpl
    export All reveals *

    datatype CScheduler = CScheduler(ghost node:Node, node_impl:NodeImpl)

    type HostState = CScheduler
    type ConcreteConfiguration = Config

    predicate ConcreteConfigurationInvariants(config:ConcreteConfiguration) 
    {
        ValidConfig(config)
    }

    predicate HostStateInvariants(host_state:HostState, env:HostEnvironment)
    {
     && host_state.node_impl.Valid() 
     && host_state.node_impl.Env() == env
     && host_state.node == AbstractifyCNode(host_state.node_impl.node)
    }

    predicate HostInit(host_state:HostState, config:ConcreteConfiguration, id:EndPoint)
    {
     && host_state.node_impl.Valid()
     && host_state.node_impl.node.config == config
     && host_state.node_impl.node.config[host_state.node_impl.node.my_index] == id
     && NodeInit(host_state.node, 
                 host_state.node_impl.node.my_index as int,
                 config)
    }

    predicate HostNext(host_state:HostState, host_state':HostState, ios:seq<LIoOp<EndPoint, seq<byte>>>)
    {
         NodeNext(host_state.node, host_state'.node, AbstractifyRawLogToIos(ios))
      && OnlySentMarshallableData(ios)
    }

    predicate ConcreteConfigInit(config:ConcreteConfiguration, servers:set<EndPoint>, clients:set<EndPoint>)
    {
        ValidConfig(config)
     && MapSeqToSet(config, x=>x) == servers
    }

    function ParseCommandLineConfiguration(args:seq<seq<byte>>) : (ConcreteConfiguration, set<EndPoint>, set<EndPoint>)
    {
        var lock_config := lock_config_parsing(args);
        var endpoints_set := (set e{:trigger e in lock_config} | e in lock_config);
        (lock_config, endpoints_set, {})
    }
    
    method HostInitImpl(
      ghost env:HostEnvironment,
      netc:NetClient,
      args:seq<seq<byte>>
      ) returns (
      ok:bool,
      host_state:HostState,
      config:ConcreteConfiguration,
      ghost servers:set<EndPoint>,
      ghost clients:set<EndPoint>,
      id:EndPoint
      )
    {
        var my_index;
        var node_impl := new NodeImpl();
        host_state := CScheduler(AbstractifyCNode(node_impl.node), node_impl);

        id := EndPoint(netc.MyPublicKey());
        ok, config, my_index := ParseCmdLine(id, args);
        if !ok { return; }
        
        ok := node_impl.InitNode(config, my_index, netc, env);
        
        if !ok { return; }
        host_state := CScheduler(AbstractifyCNode(node_impl.node), node_impl);
        servers := set e | e in config;
        clients := {};
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

    lemma NetEventsRespectReduction(s:Node, s':Node, ios:seq<LockIo>, events:seq<NetEvent>)
        requires LIoOpSeqCompatibleWithReduction(ios);
        requires AbstractifyRawLogToIos(events) == ios;
        ensures NetEventsReductionCompatible(events);
    {
        //reveal_AbstractifyRawLogToIos();
        assert AbstractifyRawLogToIos(events) == ios;
        forall i | 0 <= i < |events| - 1 
            ensures events[i].LIoOpReceive? || events[i+1].LIoOpSend?;
        {
            assert AbstractifyRawLogToIos(events)[i] == ios[i];
            assert AbstractifyRawLogToIos(events)[i+1] == ios[i+1];
        }
    }

    method HostNextImpl(ghost env:HostEnvironment, host_state:HostState) 
        returns (ok:bool, host_state':HostState, 
                 ghost recvs:seq<NetEvent>, ghost clocks:seq<NetEvent>, ghost sends:seq<NetEvent>, 
                 ghost ios:seq<LIoOp<EndPoint, seq<byte>>>)
    {
        var okay, netEventLog, abstract_ios := host_state.node_impl.HostNextMain();
        if okay {
            NetEventsRespectReduction(host_state.node, AbstractifyCNode(host_state.node_impl.node), abstract_ios, netEventLog);
            recvs, clocks, sends := PartitionEvents(netEventLog);
            ios := recvs + clocks + sends; 
            assert ios == netEventLog;
            host_state' := CScheduler(AbstractifyCNode(host_state.node_impl.node), host_state.node_impl);
        } else {
            recvs := [];
            clocks := [];
            sends := [];
            host_state' := host_state;
        }
        ok := okay;
    }
}
