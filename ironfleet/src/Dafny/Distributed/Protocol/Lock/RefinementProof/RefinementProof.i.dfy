include "Refinement.i.dfy"
include "../../../Common/Collections/Sets.i.dfy"
include "../../../Common/Collections/Maps.i.dfy"
include "../../../Common/Logic/Option.i.dfy"

module RefinementProof_i {
    import opened Refinement_i
    import opened Collections__Sets_i
    import opened Collections__Maps_i
    import opened Logic__Option_i

    lemma lemma_InitRefines(ls:LS_State, config:Config) 
        requires LS_Init(ls, config);
        ensures  Service_Init(AbstractifyLS_State(ls), UniqueSeqToSet(config));
    {
        assert config[0] in config; // OBSERVE: triggers the exists in Service_Init
    }

    predicate IsValidBehavior(lb:seq<LS_State>, config:Config)
    {
        |lb| > 0
     && LS_Init(lb[0], config)
     && (forall i :: 0 <= i < |lb| - 1 ==> LS_Next(lb[i], lb[i+1]))
    }

    lemma lemma_LS_Next(lb:seq<LS_State>, config:Config, i:int)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb| - 1;
        ensures  LS_Next(lb[i], lb[i+1]);
    {
    }

    lemma lemma_LSConsistent(lb:seq<LS_State>, config:Config, i:int)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|;
        ensures  |lb[i].servers| == |config|;
        ensures  forall e :: e in config <==> e in lb[i].servers;
        ensures  mapdomain(lb[i].servers) == mapdomain(lb[0].servers);
        ensures  forall id :: id in config ==> lb[0].servers[id].config == lb[i].servers[id].config;
    {
        if i == 0 {
            calc {
                UniqueSeqToSet(config);
                mapdomain(lb[0].servers);
            }
            lemma_seqs_set_cardinality(config, mapdomain(lb[0].servers));
            calc {
                |mapdomain(lb[0].servers)|;
                    { lemma_MapSizeIsDomainSize(mapdomain(lb[0].servers), lb[0].servers); }
                |lb[0].servers|;
            }
        } else {
            lemma_LS_Next(lb, config, i - 1);
            lemma_LSConsistent(lb, config, i - 1);
        }
    }

    lemma lemma_LSNodeConsistent(lb:seq<LS_State>, config:Config, i:int, candidate:EndPoint, e:EndPoint)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|;
        requires e in lb[i].servers;
        ensures  candidate in lb[i].servers <==> candidate in lb[i].servers[e].config;
    {
        if i == 0 {
        } else {
            lemma_LS_Next(lb, config, i-1);
            lemma_LSConsistent(lb, config, i-1);
            lemma_LSNodeConsistent(lb, config, i-1, candidate, e);
        }
    }

    /*
    lemma lemma_FindLockNode(lb:seq<LS_State>, config:Config, i:int)
        returns (found:bool, endpoint:EndPoint)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|;
        ensures  found ==> endpoint in lb[i].servers && lb[i].servers[endpoint].held;
        ensures  !found ==> (forall e :: e in lb[i].servers ==> !lb[i].servers[e].held);
    {
        lemma_LSConsistent(lb, config, i);
        found := false;
        var j := 0;
        while j < |config|
            invariant 0 <= j <= |config|;
            invariant !found ==> forall k :: 0 <= k < j ==> !lb[i].servers[config[k]].held;
        {
            endpoint := config[j];
            if lb[i].servers[endpoint].held {
                found := true;
                return;
            }
            j := j + 1;
        }
    }

    */


    lemma lemma_HistoryIncrement(lb:seq<LS_State>, config:Config, i:int)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb| - 1;
        ensures  |lb[i].history| + 1 == |lb[i+1].history|
              || lb[i].history == lb[i+1].history;
    { }

    lemma lemma_HistorySize(lb:seq<LS_State>, config:Config, i:int)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|;
        ensures  1 <= |lb[i].history| <= i + 1;
    { 
        if i == 0 {
        } else {
            lemma_HistorySize(lb, config, i - 1);
            lemma_HistoryIncrement(lb, config, i - 1);
        }
    }

    lemma lemma_HistoryMembership(lb:seq<LS_State>, config:Config, i:int)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|;
        ensures  1 <= |lb[i].history| <= i + 1;
        ensures  last(lb[i].history) in lb[i].servers;
    {
        lemma_HistorySize(lb, config, i);

        if i == 0 { 
        } else {
            lemma_LS_Next(lb, config, i - 1);
            lemma_LSConsistent(lb, config, i - 1);
            lemma_LSConsistent(lb, config, i);
            lemma_HistoryMembership(lb, config, i-1);
        }
    }

    lemma lemma_LS_NextAbstract(lb:seq<LS_State>, config:Config, i:int)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb| - 1;
        ensures  ServiceNext(AbstractifyLS_State(lb[i]), AbstractifyLS_State(lb[i+1]))
               || AbstractifyLS_State(lb[i]) == AbstractifyLS_State(lb[i+1]);
    {
        lemma_LSConsistent(lb, config, i);
        lemma_LSConsistent(lb, config, i+1);

        if i == 0 {
            assert lb[i].servers[config[0]].held;
        } else {
            lemma_HistorySize(lb, config, i);
            assert |lb[i].history| > 0;
            lemma_HistoryMembership(lb, config, i);
            assert last(lb[i].history) in lb[i].servers;
            if exists e :: NodeAcquiresLock(e, lb[i], lb[i+1]) {
                var e :| NodeAcquiresLock(e, lb[i], lb[i+1]);
                assert e in AbstractifyLS_State(lb[i]).hosts;
                assert ServiceNext(AbstractifyLS_State(lb[i]), AbstractifyLS_State(lb[i+1]));
            } else {
                assert AbstractifyLS_State(lb[i]) == AbstractifyLS_State(lb[i+1]);
            }
        }
    }

    ///////////////////////////////////////////////////////////////////
    ///  Everything above here is useful for proving the refinement
    ///  of Init and Next.  Everything below is an attempt to establish
    ///  properties needed for CorrespondenceNext
    ///////////////////////////////////////////////////////////////////

    predicate NodeEpochDominates(s:LS_State, e:EndPoint, e':EndPoint)
        requires e in s.servers && e' in s.servers;
    {
        s.servers[e].epoch > s.servers[e'].epoch
    }

    predicate TransferPkt(s:LS_State, p:LockPacket) 
    {
        p in s.environment.sentPackets && p.src in s.servers && p.msg.Transfer?
    }

    lemma SetSingleton<T>(s:set<T>, x:T)
        requires x in s;
        requires |s| == 1;
        ensures forall y :: y in s ==> x == y;
    {
        forall y | y in s
            ensures x == y;
        {
            ThingsIKnowAboutASingletonSet(s, x, y);
        }
    }

    predicate NodeEpochWeaklyDominates(servers:map<EndPoint,Node>, e:EndPoint)
        requires e in servers ;
    {
        forall e' :: e' in servers ==> servers[e].epoch >= servers[e'].epoch
    }

    predicate TransferPacket(packet:LockPacket, servers:map<EndPoint,Node>)
    {
        packet.src in servers && packet.msg.Transfer?
    }

    function MaxEpochPacket(packets:set<LockPacket>, servers:map<EndPoint,Node>) : Option<LockPacket>
    {
        if exists p {:trigger TransferPacket(p,servers)} :: 
                  p in packets && TransferPacket(p, servers) then
            var p :| p in packets && TransferPacket(p, servers);  // Note that this line isn't needed in Dafny official
            Some(p)
        else
            None()
    }

    function MaxEpochServer(servers:map<EndPoint,Node>) : Option<EndPoint>
    {
        if exists e {:trigger NodeEpochWeaklyDominates(servers, e)} :: 
                  e in servers && NodeEpochWeaklyDominates(servers, e) then
            var e :| e in servers && NodeEpochWeaklyDominates(servers, e);  // Note that this line isn't needed in Dafny official
            Some(e)
        else 
            None()
    }

    function max(a:int, b:int) : int 
    {
        if a > b then a else b
    }

    function MaxEpoch(packets:set<LockPacket>, servers:map<EndPoint,Node>) : int
    {
        var p := MaxEpochPacket(packets, servers);
        var e := MaxEpochServer(servers);
        if p.None? && e.None? then
            0
        else if p.None? then
            servers[e.v].epoch
        else if e.None? then
            p.v.msg.transfer_epoch
        else 
            max(p.v.msg.transfer_epoch, servers[e.v].epoch)
    }


    /*function maxEpochPacket(s:LS_State, packets:set<LockPacket>) : (LockPacket)
        requires exists p :: p in packets && p.src in s.servers && p.msg.Transfer?;
        requires packets <= s.environment.sentPackets;
        ensures TransferPkt(s, maxEpochPacket(s, packets));
        ensures forall p :: p in packets && p.src in s.servers && p.msg.Transfer? ==> maxEpochPacket(s, packets).msg.transfer_epoch >= p.msg.transfer_epoch;
        decreases |packets|;
    {
        var all_p := set p | p in packets && p.src in s.servers && p.msg.Transfer? :: p;
        assert exists p :: p in packets && p.src in s.servers && p.msg.Transfer?;
        var p :| p in packets && p.src in s.servers && p.msg.Transfer?;
        assert p in all_p;
        assert |all_p| > 0;
        var q :| q in all_p;
        
        assert q in packets;
        if |all_p| == 1 then
            SetSingleton(all_p, q);
            assert forall p :: p in all_p ==> p == q;
            assert forall p :: p in packets && p.src in s.servers && p.msg.Transfer? ==> p in all_p;
            assert forall p :: p in packets && p.src in s.servers && p.msg.Transfer? ==> q.msg.transfer_epoch >= p.msg.transfer_epoch;
            q
        else 
            assert |all_p| >= 2;
            assert |all_p-{q}| >= 1;
            var max_rest := maxEpochPacket(s, packets - {q});
            assert TransferPkt(s, max_rest);
            if q.msg.transfer_epoch > max_rest.msg.transfer_epoch then
                assert forall p :: p in packets && p.src in s.servers && p.msg.Transfer? ==> q.msg.transfer_epoch >= p.msg.transfer_epoch; q
            else
                assert forall p :: p in packets && p.src in s.servers && p.msg.Transfer? ==> max_rest.msg.transfer_epoch >= p.msg.transfer_epoch; max_rest
    }

    function maxEpochServer(s:LS_State, servers:map<EndPoint,Node>) : (EndPoint)
        requires |servers| > 0;
        requires mapdomain(servers) <= mapdomain(s.servers);
        ensures maxEpochServer(s, servers) in servers;
        ensures forall h :: h in servers ==> servers[maxEpochServer(s, servers)].epoch >= servers[h].epoch;
    {
        var h :| h in servers;
        if |servers| == 1 then
            lemma_MapSizeIsDomainSize(mapdomain(servers), servers);
            assert |mapdomain(servers)| == 1;
            SetSingleton(mapdomain(servers), h);
            assert forall g :: g in servers ==> servers[h].epoch >= servers[g].epoch;
            h
        else
            var max_rest := maxEpochServer(s, RemoveElt(servers, h));
            if servers[h].epoch > servers[max_rest].epoch then
                h
            else
                max_rest

    }

    function maxEpoch(s:LS_State, packets:set<LockPacket>, servers:map<EndPoint,Node>) : int
        requires exists p :: p in packets && p.src in s.servers && p.msg.Transfer?;
        requires packets <= s.environment.sentPackets;
        requires |servers| > 0;
        requires mapdomain(servers) <= mapdomain(s.servers);
        ensures forall p :: p in packets && p.src in s.servers && p.msg.Transfer? ==> maxEpoch(s, packets, servers) >= p.msg.transfer_epoch;
        ensures forall h :: h in servers ==> maxEpoch(s, packets, servers) >= servers[h].epoch;
    {
        var p := maxEpochPacket(s, packets);
        var h := maxEpochServer(s, servers);
        if p.msg.transfer_epoch > servers[h].epoch then
            p.msg.transfer_epoch
        else
            servers[h].epoch
    }*/

    /*predicate UniquePacketHoldsLock(s:LS_State)
    {
        var maxEpoch := MaxEpoch(s.environment.sentPackets, s.servers);
        (exists p ::    p in s.environment.sentPackets && p.msg.Transfer? && p.src in s.servers && p.msg.transfer_epoch == maxEpoch
                    && (forall q :: q in s.environment.sentPackets && q.msg.Transfer? && q.src in s.servers && q != p ==> q.msg.transfer_epoch < maxEpoch)
        )
    }

    predicate NoHostHoldsLock(s:LS_State)
    {
        var maxEpoch := MaxEpoch(s.environment.sentPackets, s.servers);
        forall h :: h in s.servers ==> s.servers[h].epoch < maxEpoch
    }

    predicate NoPacketHoldsLock(s:LS_State)
    {
        var maxEpoch := MaxEpoch(s.environment.sentPackets, s.servers);
        forall p :: p in s.environment.sentPackets && p.msg.Transfer? && p.src in s.servers ==> p.msg.transfer_epoch <= maxEpoch
    }

    predicate UniqueHostHoldsLock(s:LS_State)
    {
        var maxEpoch := MaxEpoch(s.environment.sentPackets, s.servers);
        (exists h ::    h in s.servers && s.servers[h].epoch == maxEpoch
                    && (forall g :: g in s.servers && g != h ==> s.servers[h].epoch < s.servers[h].epoch)
        )
    }

    predicate LockIsClaimedByHostOrMessage(s:LS_State)
    {
        (UniquePacketHoldsLock(s) && NoHostHoldsLock(s))
        || (UniqueHostHoldsLock(s) && NoPacketHoldsLock(s))
    }*/

    lemma MakeLockHistory(lb:seq<LS_State>, config:Config, i:int) returns (history:seq<EndPoint>)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|-1;
        ensures |history| > 0;
        ensures forall p :: p in lb[i].environment.sentPackets && p.msg.Transfer? && p.src in lb[i].servers 
                        ==> 2 <= p.msg.transfer_epoch <= |history|;
        ensures forall p :: p in lb[i].environment.sentPackets && p.msg.Transfer? && p.src in lb[i].servers 
                        ==> history[p.msg.transfer_epoch-1] == p.dst;
        ensures forall h,j :: h in lb[i].servers && 0 <= j < |history|-1 && history[j] == h ==> j+1 <= lb[i].servers[h].epoch;
        ensures forall h :: h in lb[i].servers && h != last(history) ==> !lb[i].servers[h].held;
        ensures forall h :: h in lb[i].servers && lb[i].servers[h].held ==> lb[i].servers[h].epoch == |history|;
    {
        if i == 0 {
            history := [config[0]];
        } else {
            var prevHistory := MakeLockHistory(lb, config, i-1);
            lemma_LS_Next(lb, config, i-1);
            lemma_LSConsistent(lb, config, i-1);
            lemma_LSConsistent(lb, config, i);
            var s := lb[i-1];
            var s' := lb[i];
            assert LEnvironment_Next(s.environment, s'.environment);
            if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers {
                var id := s.environment.nextStep.actor;
                var ios := s.environment.nextStep.ios;
                if NodeGrant(s.servers[id], s'.servers[id], ios) {
                    if s.servers[id].held && s.servers[id].epoch < 0xFFFF_FFFF_FFFF_FFFF {
                        history := prevHistory + [ios[0].s.dst];
                    } else {
                        history := prevHistory;
                    }
                } else {
                    history := prevHistory;
                    if   !ios[0].LIoOpTimeoutReceive? 
                      && !s.servers[id].held 
                      && ios[0].r.src in s.servers[id].config
                      && ios[0].r.msg.Transfer? 
                      && ios[0].r.msg.transfer_epoch > s.servers[id].epoch {
                        history := prevHistory;
                        var p := ios[0].r;
                        assert IsValidLIoOp(ios[0], id, s.environment);     // trigger
                        assert p.dst == id;
                    }
                }
            } else {
                history := prevHistory;
            }
        }
    }
    /*lemma lemma_LockIsClaimedByHostOrMessage(lb:seq<LS_State>, config:Config, i:int)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|-1;
        requires LockIsClaimedByHostOrMessage(lb[i]);
        ensures LockIsClaimedByHostOrMessage(lb[i+1]);
    {
        lemma_LS_Next(lb, config, i);
        lemma_LSConsistent(lb, config, i);
        var s := lb[i];
        var s' := lb[i+1];
        assert LEnvironment_Next(s.environment, s'.environment);

        if s.environment.nextStep.LEnvStepHostIos? {
            
            if s.environment.nextStep.actor in s.servers {
                assert LS_NextOneServer(s, s', s.environment.nextStep.actor, s.environment.nextStep.ios);
                var id := s.environment.nextStep.actor;
                var ios := s.environment.nextStep.ios;
                assert NodeNext(s.servers[id], s'.servers[id], ios);
                if NodeGrant(s.servers[id], s'.servers[id], ios) {
                    assume false;
                } else {
                    //assert LockIsClaimedByHostOrMessage(lb[i+1]);
                    assume false;
                }
            } else {
                assert s'.servers == s.servers;
                //assume false;
                if UniquePacketHoldsLock(s) && NoHostHoldsLock(s) {
                    assert NoHostHoldsLock(s');
                    assert UniquePacketHoldsLock(s');
                    assert LockIsClaimedByHostOrMessage(lb[i+1]);
                } else {
                    assert UniqueHostHoldsLock(s) && NoPacketHoldsLock(s);
                    assert UniqueHostHoldsLock(s');
                    assert NoPacketHoldsLock(s');
                    assert LockIsClaimedByHostOrMessage(lb[i+1]);
                }
            }
        } else {
            assert LockIsClaimedByHostOrMessage(lb[i+1]);
        }
    }

    lemma lemma_NodeEpochVsTransferPacket(lb:seq<LS_State>, config:Config, i:int, e:EndPoint)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|;
        requires e in lb[i].servers;
        requires lb[i].servers[e].held;
        decreases i,1;
        ensures  forall p  :: TransferPkt(lb[i], p) ==> lb[i].servers[e].epoch >= p.msg.transfer_epoch;
    {
        lemma_LSConsistent(lb, config, i);
        if i == 0 {
        } else {
            lemma_LS_Next(lb, config, i-1);
            lemma_LSConsistent(lb, config, i-1);
            var s := lb[i-1];
            if lb[i-1].servers[e].held {
                lemma_NodeEpochVsTransferPacket(lb, config, i - 1, e);
                lemma_ThereCanOnlyBeOne(lb, config, i-1, e);
                //lemma_ThereCanOnlyBeOne(lb, config, i, e);
            } else {
                assert lb[i-1].environment.nextStep.actor == e;
                forall e' | e' != e && e' in lb[i].servers
                    ensures !lb[i].servers[e'].held;
                    ensures !lb[i-1].servers[e'].held;
                {
                    lemma_ThereCanOnlyBeOne(lb, config, i-1, e);
                    lemma_ThereCanOnlyBeOne(lb, config, i, e);
                } 
                var transfer_pkt := lemma_LockInTransit(lb, config, i-1);
            }
        }
    }*/

/*    lemma lemma_NodeEpochs(lb:seq<LS_State>, config:Config, i:int, e:EndPoint)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|;
        requires e in lb[i].servers;
        requires lb[i].servers[e].held;
        decreases i,-1;
        ensures  forall e' :: e' in lb[i].servers && e' != e ==> NodeEpochDominates(lb[i], e, e');

    {
        lemma_LSConsistent(lb, config, i);
        if i == 0 {
        } else {
            lemma_LS_Next(lb, config, i-1);
            lemma_LSConsistent(lb, config, i-1);
            var s := lb[i-1];
            if lb[i-1].servers[e].held {
                lemma_NodeEpochs(lb, config, i - 1, e);
                lemma_ThereCanOnlyBeOne(lb, config, i-1, e);
                //lemma_ThereCanOnlyBeOne(lb, config, i, e);
            } else {
                assert lb[i-1].environment.nextStep.actor == e;
                forall e' | e' != e && e' in lb[i].servers
                    //ensures !lb[i].servers[e'].held;
                    ensures !lb[i-1].servers[e'].held;
                {
                    //lemma_ThereCanOnlyBeOne(lb, config, i, e);
                    lemma_ThereCanOnlyBeOne(lb, config, i-1, e);
                } 
                var transfer_pkt := lemma_LockInTransit(lb, config, i-1);
            }
        }
    }
*/

/*    lemma lemma_ThereCanOnlyBeOne(lb:seq<LS_State>, config:Config, i:int, e:EndPoint)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|;
        requires e in lb[i].servers;
        decreases i,0;
        ensures  lb[i].servers[e].held ==> (forall e' :: e' in lb[i].servers && e' != e ==> !lb[i].servers[e'].held);

    {
        if lb[i].servers[e].held {
            lemma_LSConsistent(lb, config, i);
            if i == 0 {
            } else {
                lemma_LS_Next(lb, config, i-1);
                lemma_LSConsistent(lb, config, i-1);
                var s := lb[i-1];
                var s' := lb[i];
                if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers {
                    if s.environment.nextStep.actor == e {
                        if s.servers[e].held {
                            lemma_ThereCanOnlyBeOne(lb, config, i - 1, e);
                        } else {
                            if exists e' :: e' in s.servers && s.servers[e'].held {
                                var e' :| e' in s.servers && s.servers[e'].held;
                                lemma_ThereCanOnlyBeOne(lb, config, i-1, e');
                                assert s'.servers[e'].held;
                                lemma_NodeEpochVsTransferPacket(lb, config, i-1, e');
                                lemma_NodeEpochs(lb, config, i, e);
                                lemma_NodeEpochs(lb, config, i, e');
                                assert false;
                            } else {
                            }
                        }
                    } else {
                    }
                }
            }
        }
    }
*/

/*    lemma lemma_LockInTransit(lb:seq<LS_State>, config:Config, i:int) returns (p:LockPacket)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|;
        requires forall e :: e in lb[i].servers ==> !lb[i].servers[e].held;
        ensures  TransferPkt(lb[i], p);
        ensures  forall e :: e in lb[i].servers ==> p.msg.transfer_epoch > lb[i].servers[e].epoch;
        ensures  forall p' :: TransferPkt(lb[i], p') ==> p.msg.transfer_epoch > p'.msg.transfer_epoch;
    
    

    lemma lemma_NodeEpochBounds(lb:seq<LS_State>, config:Config, i:int, e:EndPoint)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|;
        requires e in lb[i].servers;
        ensures  0 <= lb[i].servers[e].epoch < |lb[i].history|;
    {
        lemma_LSConsistent(lb, config, i);
        if i == 0 {
        } else {
            lemma_LS_Next(lb, config, i-1);
            lemma_LSConsistent(lb, config, i-1);
            var s := lb[i-1];
            lemma_NodeEpochBounds(lb, config, i-1, e);
            if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers {
                var e := s.environment.nextStep.actor;
                var n  := lb[i-1].servers[e];
                var n' := lb[i].servers[e];
                var ios := s.environment.nextStep.ios;
                if NodeAccept(n, n', ios) {
                    if   ios[0].LIoOpReceive? && !n.held && ios[0].r.src in n.config
                      && ios[0].r.msg.Transfer? && ios[0].r.msg.transfer_epoch > n.epoch {
                        lemma_LSNodeConsistent(lb, config, i-1, ios[0].r.src, e);
                        lemma_TransferPacketBounds(lb, config, i-1, ios[0].r);
                        assert NodeAcquiresLock(e, lb[i-1], lb[i]);
                        assert |lb[i].history| == |lb[i-1].history| + 1;
                    } else {
                    }
                } else {
                }
            } else {
            }
        }
    }

    lemma lemma_TransferPacketBounds(lb:seq<LS_State>, config:Config, i:int, p:LockPacket)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|;
        requires p.msg.Transfer? && p in lb[i].environment.sentPackets && p.src in lb[i].servers; 
        ensures  0 < p.msg.transfer_epoch <= |lb[i].history|;
        ensures  last(lb[i].history) in lb[i].servers;
        ensures  p.msg.transfer_epoch == |lb[i].history| ==> !lb[i].servers[last(lb[i].history)].held;
    {
        lemma_LSConsistent(lb, config, i);
        if i == 0 {
        } else {
            lemma_LS_Next(lb, config, i-1);
            lemma_LSConsistent(lb, config, i-1);
            lemma_HistoryMembership(lb, config, i);
            if p in lb[i-1].environment.sentPackets {
                lemma_TransferPacketBounds(lb, config, i - 1, p);
                if p.msg.transfer_epoch == |lb[i].history| { 
                    if lb[i].history == lb[i-1].history {
                        var prev' := lb[i].servers[last(lb[i].history)];
                        if prev'.held {
                            assert NodeAcquiresLock(last(lb[i].history), lb[i-1], lb[i]);
                        }
                    } else {
                    }
                }
            } else {
                lemma_NodeEpochBounds(lb, config, i - 1, lb[i-1].environment.nextStep.actor);
                var s := lb[i-1];
                var s' := lb[i];
                if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers {
                    if p.msg.transfer_epoch == |lb[i].history| { 
                        assert p.src == s.environment.nextStep.actor;
                        assert !lb[i].servers[p.src].held;
                        assert s'.history == s.history;
                        assert last(lb[i].history) == p.src;
                    } else {
                    }

                } else {
                }

            }
        }
    }

    lemma lemma_LockedPacketBounds(lb:seq<LS_State>, config:Config, i:int, p:LockPacket)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|;
        requires p.msg.Locked? && p in lb[i].environment.sentPackets && p.src in lb[i].servers; 
        ensures  0 <= p.msg.locked_epoch < |lb[i].history|;
    {
        if i == 0 {
        } else {
            lemma_LS_Next(lb, config, i-1);
            lemma_LSConsistent(lb, config, i);
            lemma_LSConsistent(lb, config, i-1);
            if p in lb[i-1].environment.sentPackets {
                lemma_LockedPacketBounds(lb, config, i - 1, p);
            } else {
                if lb[i-1].environment.nextStep.ios[0].r.src in lb[i-1].servers {
                    lemma_TransferPacketBounds(lb, config, i-1, lb[i-1].environment.nextStep.ios[0].r);
                }
                lemma_NodeEpochBounds(lb, config, i-1, lb[i-1].environment.nextStep.actor);

                var s := lb[i-1];
                if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers {
                    var e := s.environment.nextStep.actor;
                    var n  := lb[i-1].servers[e];
                    var n' := lb[i].servers[e];
                    var ios := s.environment.nextStep.ios;
                    if NodeAccept(n, n', ios) {
                        if   ios[0].LIoOpReceive? && !n.held && ios[0].r.src in n.config
                          && ios[0].r.msg.Transfer? && ios[0].r.msg.transfer_epoch > n.epoch {
                            lemma_LSNodeConsistent(lb, config, i-1, ios[0].r.src, e);
                            lemma_TransferPacketBounds(lb, config, i-1, ios[0].r);
                            assert NodeAcquiresLock(e, lb[i-1], lb[i]);
                            assert |lb[i].history| == |lb[i-1].history| + 1;
                        } else {
                        }
                    } else {
                    }
                } else {
                }
            }
        }
    }

    lemma lemma_ThereCanOnlyBeOne(lb:seq<LS_State>, config:Config, i:int, e:EndPoint)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|;
        requires e in lb[i].servers;
        ensures  lb[i].servers[e].held ==> (forall e' :: e' in lb[i].servers && e' != e ==> !lb[i].servers[e'].held);
    {
        lemma_LSConsistent(lb, config, i);
        if i == 0 {
        } else {
            lemma_LS_Next(lb, config, i-1);
            lemma_LSConsistent(lb, config, i-1);

            var s  := lb[i-1];
            var s' := lb[i];
            if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers {
                if e == s.environment.nextStep.actor {
                    var ios := s.environment.nextStep.ios;
                    var n  := s.servers[e];
                    var n' := s'.servers[e];
                    if exists e' :: e' != e && e' in s.servers && s.servers[e'].held {
                        var e' :| e' != e && e' in s.servers && s.servers[e'].held;
                        lemma_ThereCanOnlyBeOne(lb, config, i-1, e');
                        assert !s.servers[e'].held;
                    }
//                    forall e' | e' in lb[i].servers && e' != e
//                        ensures !lb[i].servers[e'].held;
//                    {
//                        assert lb[i].servers[e'] == lb[i-1].servers[e'];
//                        assert !lb[i-1].servers[e'].held;
//                    }
                } else {
                    lemma_ThereCanOnlyBeOne(lb, config, i-1, e);
                }
            }
        }
    }



    lemma lemma_HeldHistory(lb:seq<LS_State>, config:Config, i:int, e:EndPoint)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|;
        requires e in lb[i].servers;
        requires lb[i].servers[e].held;
        ensures  |lb[i].history| > 0;
        ensures  last(lb[i].history) == e;
    {
        lemma_LSConsistent(lb, config, i);
        if i == 0 {
        } else {
            lemma_LS_Next(lb, config, i-1);
            lemma_HistorySize(lb, config, i);
            lemma_LSConsistent(lb, config, i-1);

            var s  := lb[i-1];
            var s' := lb[i];
            if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers {
                if e == s.environment.nextStep.actor {
                    var ios := s.environment.nextStep.ios;
                    var n  := s.servers[e];
                    var n' := s'.servers[e];

                    if NodeGrant(n, n', ios) {
                        if n.epoch < 0xFFFF_FFFF_FFFF_FFFF {
                            assert n' == lb[i].servers[e];
                            assert lb[i].servers[e].held;
                            assert n'.held;
                            assert !n'.held;
                            assert false;
                        } else {
                            assert forall e' :: e' != e ==> !NodeAcquiresLock(e', lb[i-1], lb[i]);
                            lemma_HeldHistory(lb, config, i-1, e);
                            assert lb[i].history == lb[i-1].history;
                            assert last(lb[i].history) == e;
                        }
                    } else {
                        assert NodeAccept(n, n', ios);
                        if   ios[0].LIoOpReceive? && !n.held && ios[0].r.src in n.config
                          && ios[0].r.msg.Transfer? && ios[0].r.msg.transfer_epoch > n.epoch {
                            lemma_LSNodeConsistent(lb, config, i-1, ios[0].r.src, e);
                            lemma_TransferPacketBounds(lb, config, i-1, ios[0].r);
                            assert NodeAcquiresLock(e, lb[i-1], lb[i]);
                        } else {
                            lemma_HeldHistory(lb, config, i-1, e);
                        }
                        assert last(lb[i].history) == e;
                    }
                } else {
                    lemma_HeldHistory(lb, config, i-1, e);
                    lemma_ThereCanOnlyBeOne(lb, config, i-1, e);
                    lemma_ThereCanOnlyBeOne(lb, config, i, e);
                    assert last(lb[i].history) == e;
                }
            } else {
                lemma_HeldHistory(lb, config, i-1, e);
                assert last(lb[i].history) == e;
            }
        }
    }

    lemma lemma_LockedPacket(lb:seq<LS_State>, config:Config, i:int, p:LockPacket)
        requires IsValidBehavior(lb, config);
        requires 0 <= i < |lb|;
        requires p.msg.Locked? && p in lb[i].environment.sentPackets && p.src in lb[i].servers; 
        ensures  0 <= p.msg.locked_epoch < |lb[i].history|;
        ensures  p.src == lb[i].history[p.msg.locked_epoch];
    {
        lemma_LSConsistent(lb, config, i);
        lemma_LockedPacketBounds(lb, config, i, p);
        if i == 0 {

        } else {
            lemma_LS_Next(lb, config, i-1);
            lemma_HistorySize(lb, config, i);
            lemma_LSConsistent(lb, config, i-1);
            var s  := lb[i-1];
            var s' := lb[i];
            if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers {
                var e := s.environment.nextStep.actor;
                var ios := s.environment.nextStep.ios;
                var n  := s.servers[e];
                var n' := s'.servers[e];

                if NodeGrant(n, n', ios) {
                    lemma_LockedPacket(lb, config, i - 1, p);
                } else {
                    if p in lb[i-1].environment.sentPackets {
                        lemma_LockedPacket(lb, config, i - 1, p);
                    } else {
                        if NodeAccept(n, n', ios) {
                            if   ios[0].LIoOpReceive? && !n.held && ios[0].r.src in n.config
                              && ios[0].r.msg.Transfer? && ios[0].r.msg.transfer_epoch > n.epoch {
                                lemma_LSNodeConsistent(lb, config, i-1, ios[0].r.src, e);
                                lemma_TransferPacketBounds(lb, config, i-1, ios[0].r);
                                assert NodeAcquiresLock(e, lb[i-1], lb[i]);
                                assert |lb[i].history| == |lb[i-1].history| + 1;
                                assert e == p.src;
                                assert last(lb[i].history) == e;
                                var transfer_packet := ios[0].r;
                                lemma_TransferPacketBounds(lb, config, i, transfer_packet);
                                assert |lb[i].history| - 1 <= transfer_packet.msg.transfer_epoch;
                                assert transfer_packet.msg.transfer_epoch == |lb[i].history| - 1;
                                assert p.msg.locked_epoch == |lb[i].history| - 1;
                            } else {
                            }
                        } else {
                        }
                    }
                }
            } else {
                lemma_LockedPacket(lb, config, i - 1, p);
            }
        }

    }

    */
}
