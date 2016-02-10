include "../../Common/Framework/Main.s.dfy"
include "../../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "../../Impl/Lock/PacketParsing.i.dfy"
include "../../Impl/Lock/UdpLock.i.dfy"
include "../../Impl/Lock/Host.i.dfy"
include "AbstractService.s.dfy"
include "../../Protocol/Lock/RefinementProof/Refinement.i.dfy"
include "../../Protocol/Lock/RefinementProof/RefinementProof.i.dfy"
include "Marshall.i.dfy"

module Main_i exclusively refines Main_s {
    import opened DistributedSystem_i
    import opened Environment_s
    import opened Concrete_NodeIdentity_i
    import opened PacketParsing_i
    import opened UdpLock_i
    import opened Host_i
    import opened AbstractServiceLock_s
    import opened Refinement_i
    import opened RefinementProof_i
    import opened MarshallProof_i

    predicate IsValidBehavior(config:ConcreteConfiguration, db:seq<DS_State>)
        reads *;
    {
           |db| > 0
        && DS_Init(db[0], config)
        && forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1])
    }

    predicate IsValidBehaviorLs(config:ConcreteConfiguration, db:seq<LS_State>)
        reads *;
    {
           |db| > 0
        && LS_Init(db[0], config)
        && forall i {:trigger LS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> LS_Next(db[i], db[i+1])
    }

    function AbstractifyConcretePacket(p:LPacket<EndPoint,seq<byte>>) : LPacket<NodeIdentity, LockMessage>
    {
        LPacket(p.dst, p.src, AbstractifyCMessage(DemarshallData(p.msg)))
    }

    predicate LEnvStepIsAbstractable(step:LEnvStep<EndPoint,seq<byte>>)
    {
        match step {
            case LEnvStepHostIos(actor, ios) => true
            case LEnvStepDeliverPacket(p) => true
            case LEnvStepAdvanceTime => true
            case LEnvStepStutter => true 
        }
    }

    function AbstractifyConcreteEnvStep(step:LEnvStep<EndPoint,seq<byte>>) : LEnvStep<NodeIdentity, LockMessage>
        requires LEnvStepIsAbstractable(step);
    {
        match step {
            case LEnvStepHostIos(actor, ios) => LEnvStepHostIos(actor, AbstractifyRawLogToIos(ios))
            case LEnvStepDeliverPacket(p) => LEnvStepDeliverPacket(AbstractifyConcretePacket(p))
            case LEnvStepAdvanceTime => LEnvStepAdvanceTime()
            case LEnvStepStutter => LEnvStepStutter() 
        }
    }

    predicate ConcreteEnvironmentIsAbstractable(ds_env:LEnvironment<EndPoint,seq<byte>>)
    {
        LEnvStepIsAbstractable(ds_env.nextStep)
    }

    function AbstractifyConcreteSentPackets(sent:set<LPacket<EndPoint,seq<byte>>>) : set<LPacket<NodeIdentity, LockMessage>>
    {
        set p | p in sent :: AbstractifyConcretePacket(p)
    }

    function AbstractifyConcreteEnvironment(ds_env:LEnvironment<EndPoint,seq<byte>>) : LEnvironment<NodeIdentity, LockMessage>
        requires ConcreteEnvironmentIsAbstractable(ds_env);
    {
        LEnvironment(ds_env.time,
                     AbstractifyConcreteSentPackets(ds_env.sentPackets),
                     map [],
                     AbstractifyConcreteEnvStep(ds_env.nextStep))
    }

    function AbstractifyConcreteReplicas(replicas:map<EndPoint,HostState>, replica_order:seq<EndPoint>) : map<EndPoint,Node>
        requires forall i :: 0 <= i < |replica_order| ==> replica_order[i] in replicas;
        requires SeqIsUnique(replica_order);
        ensures  |AbstractifyConcreteReplicas(replicas, replica_order)| == |replica_order|;
        ensures  forall i :: 0 <= i < |replica_order| ==> replica_order[i] in AbstractifyConcreteReplicas(replicas, replica_order);
        ensures  forall i :: 0 <= i < |replica_order| ==> 
                 AbstractifyConcreteReplicas(replicas, replica_order)[replica_order[i]] == replicas[replica_order[i]].node;
        ensures forall e :: e in AbstractifyConcreteReplicas(replicas, replica_order) <==> e in replica_order;
    {
        if |replica_order| == 0 then map[]
        else
            lemma_UniqueSeq_SubSeqsUnique(replica_order, [replica_order[0]], replica_order[1..]);
            assert SeqIsUnique(replica_order[1..]);
            reveal_SeqIsUnique();
            assert replica_order[0] !in replica_order[1..];
            assert replica_order[0] !in AbstractifyConcreteReplicas(replicas, replica_order[1..]);
            
            var rest := AbstractifyConcreteReplicas(replicas, replica_order[1..]);
            rest[replica_order[0] := replicas[replica_order[0]].node]
    }

    function AbstractifyConcreteClients(clients:set<EndPoint>) : set<NodeIdentity>
    {
        set e | e in clients :: e
    }

    predicate DsStateIsAbstractable(ds:DS_State) 
    {
           ValidConfig(ds.config)
        && (forall r :: r in ds.config ==> r in ds.servers)
    }

    function AbstractifyDsState(ds:DS_State) : LS_State
        requires DsStateIsAbstractable(ds);
    {
        LS_State(AbstractifyConcreteEnvironment(ds.environment),
                    AbstractifyConcreteReplicas(ds.servers, ds.config))
    }

    lemma lemma_DeduceTransitionFromDsBehavior(
        config:ConcreteConfiguration,
        db:seq<DS_State>,
        i:int
        )
        requires IsValidBehavior(config, db);
        requires 0 <= i < |db| - 1;
        ensures  DS_Next(db[i], db[i+1]);
    {
    }
    
    lemma lemma_DsNextOffset(db:seq<DS_State>, index:int)
        requires |db| > 0;
        requires 0 < index < |db|;
        requires forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        ensures  DS_Next(db[index-1], db[index]);
    {
        var i := index - 1;
        assert DS_Next(db[i], db[i+1]); // OBSERVE trigger for the forall
    }

    lemma lemma_DsConsistency(config:ConcreteConfiguration, db:seq<DS_State>, i:int)
        requires IsValidBehavior(config, db);
        requires 0 <= i < |db|;
        ensures  db[i].config == config;
        ensures  Collections__Maps2_s.mapdomain(db[i].servers) == Collections__Maps2_s.mapdomain(db[0].servers);
    {
        if i == 0 {
        } else {
            lemma_DsConsistency(config, db, i-1);
            lemma_DeduceTransitionFromDsBehavior(config, db, i-1);

            assert forall server :: server in db[i-1].servers ==> server in db[i].servers;
            assert forall server :: server in db[i].servers ==> server in db[i-1].servers;

            forall server | server in Collections__Maps2_s.mapdomain(db[i-1].servers)
                ensures server in Collections__Maps2_s.mapdomain(db[i].servers)
            {
                assert server in db[i-1].servers;
                assert server in db[i].servers;
                
            }

            forall server | server in Collections__Maps2_s.mapdomain(db[i].servers)
                ensures server in Collections__Maps2_s.mapdomain(db[i-1].servers)
            {
                assert server in db[i].servers;
                assert server in db[i-1].servers;
            }
        }
    }

    lemma lemma_IsValidEnvStep(de:LEnvironment<EndPoint, seq<byte>>, le:LEnvironment<NodeIdentity, LockMessage>)
        requires IsValidLEnvStep(de, de.nextStep);
        requires de.nextStep.LEnvStepHostIos?;
        requires ConcreteEnvironmentIsAbstractable(de);
        requires AbstractifyConcreteEnvironment(de) == le;
        ensures  IsValidLEnvStep(le, le.nextStep);
    {
        var id := de.nextStep.actor;
        var ios := de.nextStep.ios;
        var r_ios := le.nextStep.ios;

        assert LIoOpSeqCompatibleWithReduction(r_ios);
            
        forall io | io in r_ios
            ensures IsValidLIoOp(io, id, le);
        {
            var j :| 0 <= j < |r_ios| && r_ios[j] == io;
            assert r_ios[j] == AstractifyUdpEventToLockIo(ios[j]);
            assert IsValidLIoOp(ios[j], id, de);
        }
    }

    lemma lemma_IosRelations(ios:seq<LIoOp<EndPoint, seq<byte>>>, r_ios:seq<LIoOp<NodeIdentity, LockMessage>>)
        returns (sends:set<LPacket<EndPoint, seq<byte>>>, r_sends:set<LPacket<NodeIdentity, LockMessage>>) 
        requires r_ios == AbstractifyRawLogToIos(ios);
        ensures    sends == (set io | io in ios && io.LIoOpSend? :: io.s);
        ensures  r_sends == (set io | io in r_ios && io.LIoOpSend? :: io.s);
        ensures  r_sends == AbstractifyConcreteSentPackets(sends);
    {
          sends := (set io | io in ios && io.LIoOpSend? :: io.s);
        r_sends := (set io | io in r_ios && io.LIoOpSend? :: io.s);
        var refined_sends := AbstractifyConcreteSentPackets(sends);

        forall r | r in refined_sends
            ensures r in r_sends;
        {
            var send :| send in sends && AbstractifyConcretePacket(send) == r;
            var io :| io in ios && io.LIoOpSend? && io.s == send;
            assert AstractifyUdpEventToLockIo(io) in r_ios;
        }

        forall r | r in r_sends
            ensures r in refined_sends;
        {
            var r_io :| r_io in r_ios && r_io.LIoOpSend? && r_io.s == r; 
            var j :| 0 <= j < |r_ios| && r_ios[j] == r_io;
            assert AstractifyUdpEventToLockIo(ios[j]) == r_io;
            assert ios[j] in ios;
            assert ios[j].s in sends;
        }
    }

    lemma lemma_LEnvironmentNextHost(de :LEnvironment<EndPoint, seq<byte>>, le :LEnvironment<NodeIdentity, LockMessage>,
                                      de':LEnvironment<EndPoint, seq<byte>>, le':LEnvironment<NodeIdentity, LockMessage>)
        requires ConcreteEnvironmentIsAbstractable(de);
        requires ConcreteEnvironmentIsAbstractable(de');
        requires AbstractifyConcreteEnvironment(de)  == le;
        requires AbstractifyConcreteEnvironment(de') == le';
        requires de.nextStep.LEnvStepHostIos?;
        requires LEnvironment_Next(de, de');
        ensures  LEnvironment_Next(le, le');
    {
        lemma_IsValidEnvStep(de, le);
        var id := de.nextStep.actor;
        var ios := de.nextStep.ios;
        var r_ios := le.nextStep.ios;

        assert LEnvironment_PerformIos(de, de', id, ios);

        var sends, r_sends := lemma_IosRelations(ios, r_ios);
        assert de.sentPackets + sends == de'.sentPackets;
        assert le.sentPackets + r_sends == le'.sentPackets;

        assert forall r_io :: r_io in r_ios && r_io.LIoOpReceive? ==> r_io.r in le.sentPackets;

        assert LEnvironment_PerformIos(le, le', id, r_ios);
    }

    lemma {:timeLimitMultiplier 2} RefinementToLSState(config:ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<LS_State>)
        requires |db| > 0;
        requires DS_Init(db[0], config);
        requires forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        ensures  |sb| == |db|;
        ensures  LS_Init(sb[0], db[0].config);
        ensures  forall i {:trigger LS_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> LS_Next(sb[i], sb[i+1]);
        ensures forall i :: 0 <= i < |db| ==> DsStateIsAbstractable(db[i]) && sb[i] == AbstractifyDsState(db[i]);
    {
        if |db| == 1 {
            var ls := AbstractifyDsState(db[0]);
            sb := [ ls ];
            assert (forall id :: id in db[0].servers ==> HostInit(db[0].servers[id], config, id));
            reveal_SeqIsUnique();
        } else {
            lemma_DeduceTransitionFromDsBehavior(config, db, |db|-2);
            lemma_DsConsistency(config, db, |db|-2);
            lemma_DsConsistency(config, db, |db|-1);
            var ls := AbstractifyDsState(db[|db|-2]);
            var ls' := AbstractifyDsState(last(db));
            var rest := RefinementToLSState(config, all_but_last(db));
            
            sb := rest + [ls'];
            forall i | 0 <= i < |sb| - 1 
                ensures LS_Next(sb[i], sb[i+1]);
            {
                if (0 <= i < |sb|-2) {
                    assert LS_Next(sb[i], sb[i+1]);
                } else {
                    if !db[i].environment.nextStep.LEnvStepHostIos? {
                        assert LS_Next(sb[i], sb[i+1]);
                    } else {
                        lemma_LEnvironmentNextHost(db[i].environment, ls.environment, db[i+1].environment, ls'.environment);
                        assert LS_Next(sb[i], sb[i+1]);
                    }
                }
            }
        }
    }

    lemma lemma_DeduceTransitionFromLsBehavior(
        config:ConcreteConfiguration,
        db:seq<LS_State>,
        i:int
        )
        requires IsValidBehaviorLs(config, db);
        requires 0 <= i < |db| - 1;
        ensures  LS_Next(db[i], db[i+1]);
    {
    }

    lemma lemma_LsConsistency(config:ConcreteConfiguration, lb:seq<LS_State>, i:int)
        requires IsValidBehaviorLs(config, lb);
        requires 0 <= i < |lb|;
        ensures  Collections__Maps2_s.mapdomain(lb[i].servers) == Collections__Maps2_s.mapdomain(lb[0].servers);
        ensures forall e :: e in lb[i].servers ==> e in lb[0].servers && lb[i].servers[e].config == lb[0].servers[e].config;
    {
        if i == 0 {
        } else {
            lemma_LsConsistency(config, lb, i-1);
            lemma_DeduceTransitionFromLsBehavior(config, lb, i-1);

            assert forall server :: server in lb[i-1].servers ==> server in lb[i].servers;
            assert forall server :: server in lb[i].servers ==> server in lb[i-1].servers;

            forall server | server in Collections__Maps2_s.mapdomain(lb[i-1].servers)
                ensures server in Collections__Maps2_s.mapdomain(lb[i].servers)
            {
                assert server in lb[i-1].servers;
                assert server in lb[i].servers;
            }

            forall server | server in Collections__Maps2_s.mapdomain(lb[i].servers)
                ensures server in Collections__Maps2_s.mapdomain(lb[i-1].servers)
            {
                assert server in lb[i].servers;
                assert server in lb[i-1].servers;
            }
        }
    }
    lemma {:timeLimitMultiplier 2} MakeGLSBehaviorFromLS(config:ConcreteConfiguration, db:seq<LS_State>) returns (sb:seq<GLS_State>)
        requires |db| > 0;
        requires LS_Init(db[0], config);
        requires forall i {:trigger LS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> LS_Next(db[i], db[i+1]);
        ensures  |sb| == |db|;
        ensures  GLS_Init(sb[0], config);
        ensures  forall i {:trigger GLS_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> GLS_Next(sb[i], sb[i+1]);
        ensures forall i :: 0 <= i < |db| ==> sb[i].ls == db[i];
    {
        if (|db| == 1) {
            sb := [GLS_State(db[0], [config[0]])];
        } else {
            var rest := MakeGLSBehaviorFromLS(config, all_but_last(db));
            var last_history := last(rest).history;
            var ls := db[|db|-2];
            var ls' := db[|db|-1];
            if ls.environment.nextStep.LEnvStepHostIos? && ls.environment.nextStep.actor in ls.servers {
                var id := ls.environment.nextStep.actor;
                var ios := ls.environment.nextStep.ios;
                lemma_DeduceTransitionFromLsBehavior(config, db, |db|-2);
                assert LS_Next(ls, ls');
                assert LS_NextOneServer(ls, ls', id, ios);
                var node := ls.servers[id];
                var node' := ls'.servers[id];
                assert NodeNext(node, node', ios);
                var new_history:seq<EndPoint>;
                if NodeGrant(node, node', ios) && node.held && node.epoch < 0xFFFF_FFFF_FFFF_FFFF{
                    new_history := last_history + [node.config[(node.my_index+1) % |node.config|]];
                } else {
                    new_history := last_history;
                }
                sb := rest + [GLS_State(db[|db|-1], new_history)];
                assert GLS_Next(sb[|sb|-2], sb[|sb|-1]);
            } else {
                
                sb := rest + [GLS_State(db[|db|-1], last_history)];
            }
        }
    }

    lemma {:timeLimitMultiplier 2} RefinementToServiceState(config:ConcreteConfiguration, glb:seq<GLS_State>) returns (sb:seq<ServiceState>)
        requires |glb| > 0;
        requires GLS_Init(glb[0], config);
        requires forall i {:trigger GLS_Next(glb[i], glb[i+1])} :: 0 <= i < |glb| - 1 ==> GLS_Next(glb[i], glb[i+1]);
        ensures  |sb| == |glb|;
        ensures  Service_Init(sb[0], MapSeqToSet(config, x=>x));
        ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
        ensures  forall i :: 0 <= i < |glb| ==> sb[i] == AbstractifyGLS_State(glb[i]);
        ensures  forall i :: 0 <= i < |sb| ==> sb[i].hosts == sb[0].hosts;
        ensures  sb[|sb|-1] == AbstractifyGLS_State(glb[|glb|-1]);
    {
        if |glb| == 1 {
            sb := [AbstractifyGLS_State(glb[0])];
            lemma_InitRefines(glb[0], config);
            assert Service_Init(AbstractifyGLS_State(glb[0]), MapSeqToSet(config, x=>x));
        } else {
            var rest := RefinementToServiceState(config, all_but_last(glb));
            var gls := last(all_but_last(glb));
            var gls' := last(glb);

            lemma_LS_NextAbstract(glb, config, |glb|-2);
            sb := rest + [AbstractifyGLS_State(gls')];
            if (AbstractifyGLS_State(gls) == AbstractifyGLS_State(gls')) {
                assert sb[|sb|-2] == sb[|sb|-1];
            } else {
                assert Service_Next(sb[|sb|-2], sb[|sb|-1]);
            }
        }
    }

    lemma lemma_LockedPacketImpliesTransferPacket(
        config:ConcreteConfiguration,
        lb:seq<LS_State>,
        i:int,
        p:LockPacket
        )
        requires IsValidBehaviorLs(config, lb);
        requires 0 <= i < |lb|;
        requires p in lb[i].environment.sentPackets;
        requires p.src in lb[i].servers;
        requires p.msg.Locked?;
        ensures exists q :: q in lb[i].environment.sentPackets
                         && q.msg.Transfer?
                         && q.src in lb[i].servers
                         && q.msg.transfer_epoch == p.msg.locked_epoch
                         && q.dst == p.src;
    {
        if i == 0 {
            return;
        }
        lemma_DeduceTransitionFromLsBehavior(config, lb, i-1);
        lemma_LsConsistency(config, lb, i);
        assert Collections__Maps2_s.mapdomain(lb[i].servers) == Collections__Maps2_s.mapdomain(lb[0].servers);
        assert LS_Init(lb[0], config);
        
        if p in lb[i-1].environment.sentPackets {
            lemma_LockedPacketImpliesTransferPacket(config, lb, i-1, p);
        } else {
            var s := lb[i-1];
            var s' := lb[i];
            assert LS_Next(lb[i-1], lb[i]);
            if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers {
                assert LS_NextOneServer(s, s', s.environment.nextStep.actor, s.environment.nextStep.ios);
                var id := s.environment.nextStep.actor;
                var node := s.servers[id];
                var node' := s'.servers[id];
                var ios := s.environment.nextStep.ios;
                if NodeAccept(node, node', ios) {
                    var packet := ios[0].r;
                    assert IsValidLIoOp(ios[0], id, s.environment);
                    assert packet in lb[i].environment.sentPackets
                         && packet.msg.Transfer?
                         && packet.msg.transfer_epoch == p.msg.locked_epoch
                         && packet.dst == p.src
                         && packet.src in node.config;
                    
                    assert node.config == lb[0].servers[id].config == lb[i].servers[id].config;
                    assert forall e :: e in lb[i].servers[id].config <==> e in Collections__Maps2_s.mapdomain(lb[i].servers);
                    assert packet.src in lb[i].servers;
                }
            }
        }
    }

    lemma lemma_PacketSentByServerIsDemarshallable(
        config:ConcreteConfiguration,
        db:seq<DS_State>,
        i:int,
        p:LPacket<EndPoint, seq<byte>>
        )
        requires IsValidBehavior(config, db);
        requires 0 <= i < |db|;
        requires p.src in config;
        requires p in db[i].environment.sentPackets;
        ensures  Demarshallable(p.msg, CMessageGrammar());
    {
        if i == 0 {
            return;
        }

        if p in db[i-1].environment.sentPackets {
            lemma_PacketSentByServerIsDemarshallable(config, db, i-1, p);
            return;
        }

        lemma_DeduceTransitionFromDsBehavior(config, db, i-1);
        lemma_DsConsistency(config, db, i-1);
    }

    lemma RefinementProof(config:ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<ServiceState>)
        /*
        requires |db| > 0;
        requires DS_Init(db[0], config);
        requires forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        ensures  |db| == |sb|;
        ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].servers));
        ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
        ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i]);
        */
    {
        var lsb := RefinementToLSState(config, db);
        var glsb := MakeGLSBehaviorFromLS(config, lsb);
        sb := RefinementToServiceState(config, glsb);
        //assert forall i :: 0 <= i < |sb| - 1 ==> Service_Next(sb[i], sb[i+1]);
        
        forall i | 0 <= i < |db|
            ensures Service_Correspondence(db[i].environment.sentPackets, sb[i]);
        {
            var ls := lsb[i];
            var gls := glsb[i];
            var ss := sb[i];
            var history := MakeLockHistory(glsb, config, i);
            assert history == gls.history;
            forall p, epoch | 
                            p in db[i].environment.sentPackets 
                         && p.src in ss.hosts 
                         && p.dst in ss.hosts 
                         && p.msg == MarshallLockMsg(epoch) 
                ensures 2 <= epoch <= |ss.history|
                     && p.src == ss.history[epoch-1];
            {
                var ap := AbstractifyConcretePacket(p);
                assert p.src in sb[0].hosts;
                lemma_PacketSentByServerIsDemarshallable(config, db, i, p);
                assert Demarshallable(p.msg, CMessageGrammar());
                lemma_ParseMarshallLockedAbstract(p.msg, epoch, ap.msg);
                lemma_LockedPacketImpliesTransferPacket(config, lsb, i, ap);
                var q :| q in ls.environment.sentPackets
                         && q.msg.Transfer?
                         && q.msg.transfer_epoch == ap.msg.locked_epoch
                         && q.dst == p.src;
                assert q in gls.ls.environment.sentPackets;
            }
        }
    }
    
}
