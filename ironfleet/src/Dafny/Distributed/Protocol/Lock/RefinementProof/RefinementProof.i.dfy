include "Refinement.i.dfy"
include "../../../Common/Collections/Sets.i.dfy"
include "../../../Common/Collections/Maps.i.dfy"
include "../../../Common/Logic/Option.i.dfy"

module RefinementProof_i {
    import opened Refinement_i
    import opened Collections__Sets_i
    import opened Collections__Maps_i
    import opened Logic__Option_i

    lemma lemma_InitRefines(gls:GLS_State, config:Config) 
        requires GLS_Init(gls, config);
        ensures  Service_Init(AbstractifyGLS_State(gls), UniqueSeqToSet(config));
    {
        assert config[0] in config; // OBSERVE: triggers the exists in Service_Init
        var s := AbstractifyGLS_State(gls);
        calc {
            s.hosts;
            mapdomain(gls.ls.servers);
            UniqueSeqToSet(config);
        }

        assert config[0] in config; // OBSERVE
        assert config[0] in UniqueSeqToSet(config);
    }

    predicate IsValidBehavior(glb:seq<GLS_State>, config:Config)
    {
        |glb| > 0
     && GLS_Init(glb[0], config)
     && (forall i {:trigger GLS_Next(glb[i], glb[i+1])} :: 0 <= i < |glb| - 1 ==> GLS_Next(glb[i], glb[i+1]))
    }

    lemma lemma_LS_Next(glb:seq<GLS_State>, config:Config, i:int)
        requires IsValidBehavior(glb, config);
        requires 0 <= i < |glb| - 1;
        ensures  GLS_Next(glb[i], glb[i+1]);
    {
    }

    lemma lemma_LSConsistent(glb:seq<GLS_State>, config:Config, i:int)
        requires IsValidBehavior(glb, config);
        requires 0 <= i < |glb|;
        ensures  |glb[i].ls.servers| == |config|;
        ensures  forall e :: e in config <==> e in glb[i].ls.servers;
        ensures  mapdomain(glb[i].ls.servers) == mapdomain(glb[0].ls.servers);
        ensures  forall id :: id in config ==> glb[0].ls.servers[id].config == glb[i].ls.servers[id].config;
    {
        if i == 0 {
            calc {
                UniqueSeqToSet(config);
                mapdomain(glb[0].ls.servers);
            }
            lemma_seqs_set_cardinality(config, mapdomain(glb[0].ls.servers));
            calc {
                |mapdomain(glb[0].ls.servers)|;
                    { lemma_MapSizeIsDomainSize(mapdomain(glb[0].ls.servers), glb[0].ls.servers); }
                |glb[0].ls.servers|;
            }
        } else {
            lemma_LS_Next(glb, config, i - 1);
            lemma_LSConsistent(glb, config, i - 1);
        }
    }

    lemma lemma_LSNodeConsistent(glb:seq<GLS_State>, config:Config, i:int, candidate:EndPoint, e:EndPoint)
        requires IsValidBehavior(glb, config);
        requires 0 <= i < |glb|;
        requires e in glb[i].ls.servers;
        ensures  candidate in glb[i].ls.servers <==> candidate in glb[i].ls.servers[e].config;
    {
        if i == 0 {
        } else {
            lemma_LS_Next(glb, config, i-1);
            lemma_LSConsistent(glb, config, i-1);
            lemma_LSNodeConsistent(glb, config, i-1, candidate, e);
        }
    }

    lemma lemma_HistoryIncrement(glb:seq<GLS_State>, config:Config, i:int)
        requires IsValidBehavior(glb, config);
        requires 0 <= i < |glb| - 1;
        ensures  |glb[i].history| + 1 == |glb[i].history|
              || glb[i].history == glb[i].history;
    { }

    lemma lemma_HistorySize(glb:seq<GLS_State>, config:Config, i:int)
        requires IsValidBehavior(glb, config);
        requires 0 <= i < |glb|;
        ensures  1 <= |glb[i].history| <= i + 1;
    { 
        if i == 0 {
            var locked_packets := set p | p in glb[i].ls.environment.sentPackets && p.msg.Locked?;
            assert |locked_packets| == 0;
            assert exists host :: host in (glb[i]).ls.servers && (glb[i]).ls.servers[host].held;
            assert |glb[i].history| == 1;
        } else {
            lemma_HistorySize(glb, config, i - 1);
            lemma_HistoryIncrement(glb, config, i - 1);
            assert GLS_Next(glb[i-1], glb[i]);
        }
    }

    lemma lemma_HistoryMembership(glb:seq<GLS_State>, config:Config, i:int)
        requires IsValidBehavior(glb, config);
        requires 0 <= i < |glb|;
        ensures  1 <= |glb[i].history| <= i + 1;
        ensures  last(glb[i].history) in glb[i].ls.servers;
    {
        lemma_HistorySize(glb, config, i);

        if i == 0 { 
        } else {
            lemma_LS_Next(glb, config, i - 1);
            lemma_LSConsistent(glb, config, i - 1);
            lemma_LSConsistent(glb, config, i);
            lemma_HistoryMembership(glb, config, i-1);
        }
    }

    lemma lemma_LS_NextAbstract(glb:seq<GLS_State>, config:Config, i:int)
        requires IsValidBehavior(glb, config);
        requires 0 <= i < |glb| - 1;
        ensures  Service_Next(AbstractifyGLS_State(glb[i]), AbstractifyGLS_State(glb[i+1]))
               || AbstractifyGLS_State(glb[i]) == AbstractifyGLS_State(glb[i+1]);
    {
        lemma_LSConsistent(glb, config, i);
        lemma_LSConsistent(glb, config, i+1);
        assert GLS_Next(glb[i], glb[i+1]);
        if i == 0 {
            assert glb[i].ls.servers[config[0]].held;
        } else {
            lemma_HistorySize(glb, config, i);
            assert |glb[i].history| > 0;
            lemma_HistoryMembership(glb, config, i);
            assert last(glb[i].history) in glb[i].ls.servers;
        }
    }

    ///////////////////////////////////////////////////////////////////
    ///  Everything above here is useful for proving the refinement
    ///  of Init and Next.  The lemma below establishes properties
    ///  needed to prove Service_Correspondence.
    ///////////////////////////////////////////////////////////////////

    lemma MakeLockHistory(glb:seq<GLS_State>, config:Config, i:int) returns (history:seq<EndPoint>)
        requires IsValidBehavior(glb, config);
        requires 0 <= i < |glb|;
        ensures |history| > 0;
        ensures forall p :: p in glb[i].ls.environment.sentPackets && p.msg.Transfer? && p.src in glb[i].ls.servers 
                        ==> 2 <= p.msg.transfer_epoch <= |history|;
        ensures forall p :: p in glb[i].ls.environment.sentPackets && p.msg.Transfer? && p.src in glb[i].ls.servers 
                        ==> history[p.msg.transfer_epoch-1] == p.dst;
        ensures forall h,j :: h in glb[i].ls.servers && 0 <= j < |history|-1 && history[j] == h ==> j+1 <= glb[i].ls.servers[h].epoch;
        ensures forall h :: h in glb[i].ls.servers && h != last(history) ==> !glb[i].ls.servers[h].held;
        ensures forall h :: h in glb[i].ls.servers && glb[i].ls.servers[h].held ==> glb[i].ls.servers[h].epoch == |history|;
        ensures history == glb[i].history;
    {
        if i == 0 {
            history := [config[0]];
        } else {
            var prevHistory := MakeLockHistory(glb, config, i-1);
            lemma_LS_Next(glb, config, i-1);
            lemma_LSConsistent(glb, config, i-1);
            lemma_LSConsistent(glb, config, i);
            var s := glb[i-1];
            var s' := glb[i];
            assert LEnvironment_Next(s.ls.environment, s'.ls.environment);
            
            if s.ls.environment.nextStep.LEnvStepHostIos? && s.ls.environment.nextStep.actor in s.ls.servers {
                var id := s.ls.environment.nextStep.actor;
                var ios := s.ls.environment.nextStep.ios;
                
                if NodeGrant(s.ls.servers[id], s'.ls.servers[id], ios) {
                    if s.ls.servers[id].held && s.ls.servers[id].epoch < 0xFFFF_FFFF_FFFF_FFFF {
                        history := prevHistory + [ios[0].s.dst];
                    } else {
                        history := prevHistory;
                    }
                } else {
                    history := prevHistory;
                    
                    if   !ios[0].LIoOpTimeoutReceive? 
                      && !s.ls.servers[id].held 
                      && ios[0].r.src in s.ls.servers[id].config
                      && ios[0].r.msg.Transfer? 
                      && ios[0].r.msg.transfer_epoch > s.ls.servers[id].epoch {
                        var p := ios[0].r;
                        assert IsValidLIoOp(ios[0], id, s.ls.environment);     // trigger
                        assert p.dst == id;
                    }
                }
            } else {
                history := prevHistory;
            }
        }
    }
}
