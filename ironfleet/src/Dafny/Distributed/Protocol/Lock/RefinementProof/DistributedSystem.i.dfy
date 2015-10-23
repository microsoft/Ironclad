include "../Node.i.dfy"
include "../../../Impl/Common/SeqIsUnique.i.dfy"
include "../../../Common/Collections/Seqs.i.dfy"
//include "../../../Common/Framework/DistributedSystem.s.dfy"

module DistributedSystem_i {
    import opened Protocol_Node_i
    //import opened DistributedSystem_s
    import opened Common__SeqIsUnique_i
    import opened Collections__Seqs_i

//    function FindLock(nodes:map<EndPoint,Node>, history:seq<EndPoint>) : EndPoint
//    {
//        if exists e :: e in nodes && nodes[e].held then
//            var e :| e in nodes && nodes[e].held;
//            e
//        else if |history| > 0 then
//            last(history)
//        else 
//            EndPoint([],0)      // Should (provably) never reach here
//    }

    /////////////////////////////////////////
    // LS_State
    /////////////////////////////////////////
    
    datatype LS_State = LS_State(
        environment:LockEnvironment,
        servers:map<EndPoint,Node>,
        history:seq<EndPoint>
        )

    predicate LS_Init(s:LS_State, config:Config)
    {
           LEnvironment_Init(s.environment)
        && |config| > 0
        && SeqIsUnique(config)
        && (forall e :: e in config <==> e in s.servers)
        && (forall index :: 0 <= index < |config| ==> NodeInit(s.servers[config[index]], index, config))
        && s.history == [config[0]]
    }
    
    predicate LS_NextOneServer(s:LS_State, s':LS_State, id:EndPoint, ios:seq<LockIo>)
        requires id in s.servers;
    {
           id in s'.servers
        && NodeNext(s.servers[id], s'.servers[id], ios)
        && s'.servers == s.servers[id := s'.servers[id]]
    }

    predicate NodeAcquiresLock(e:EndPoint, s:LS_State, s':LS_State)
    {
        e in s.servers && e in s'.servers && !s.servers[e].held && s'.servers[e].held
    }

    predicate LS_Next(s:LS_State, s':LS_State)
    {
           LEnvironment_Next(s.environment, s'.environment)
        //&& ValidPhysicalEnvironmentStep(s.environment.nextStep)
        //&& s'.history == s.history + [FindLock(s.servers, s.history)]
        && (if exists e :: NodeAcquiresLock(e, s, s') then
                var e :| NodeAcquiresLock(e, s, s');
                s'.history == s.history + [e]
            else
                s'.history == s.history)
        && if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers then
               LS_NextOneServer(s, s', s.environment.nextStep.actor, s.environment.nextStep.ios)
           else
               s'.servers == s.servers
    }
}

