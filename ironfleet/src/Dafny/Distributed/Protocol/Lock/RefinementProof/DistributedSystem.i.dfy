include "../Node.i.dfy"
include "../../../Impl/Common/SeqIsUnique.i.dfy"
include "../../../Common/Collections/Seqs.i.dfy"
//include "../../../Common/Framework/DistributedSystem.s.dfy"

module DistributedSystem_i {
    import opened Protocol_Node_i
    import opened Common__SeqIsUnique_i
    import opened Collections__Seqs_i

    /////////////////////////////////////////
    // LS_State
    /////////////////////////////////////////
    
    datatype LS_State = LS_State(
        environment:LockEnvironment,
        servers:map<EndPoint,Node>
        )

    predicate LS_Init(s:LS_State, config:Config)
    {
           LEnvironment_Init(s.environment)
        && |config| > 0
        && SeqIsUnique(config)
        && (forall e :: e in config <==> e in s.servers)
        && (forall index :: 0 <= index < |config| ==> NodeInit(s.servers[config[index]], index, config))
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
        && if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers then
               LS_NextOneServer(s, s', s.environment.nextStep.actor, s.environment.nextStep.ios)
           else
               s'.servers == s.servers
    }

    /////////////////////////////////////////////
    // GLS_State: an LS_State augmented with
    // a history field. This history field is
    // initialized and updated according to
    // GLS_Init and GLS_Next
    /////////////////////////////////////////////

    datatype GLS_State = GLS_State(
        ls:LS_State,
        history:seq<EndPoint>
    )

    predicate GLS_Init(s:GLS_State, config:Config)
    {
           LS_Init(s.ls, config)
        && s.history == [config[0]]
    }

    /////////////////////////////////////////////////////////
    // GLS_Next is defined according to LS_Next. When a node 
    // sends a grant message, the destination of that message
    // (as computed in NodeGrant), is appended to the history
    /////////////////////////////////////////////////////////

    predicate GLS_Next(s:GLS_State, s':GLS_State)
    {
           LS_Next(s.ls, s'.ls)
        && (if    s.ls.environment.nextStep.LEnvStepHostIos? && s.ls.environment.nextStep.actor in s.ls.servers
               && NodeGrant(s.ls.servers[s.ls.environment.nextStep.actor], s'.ls.servers[s.ls.environment.nextStep.actor], s.ls.environment.nextStep.ios)
               && s.ls.servers[s.ls.environment.nextStep.actor].held && s.ls.servers[s.ls.environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF then
               s'.history == s.history + [s.ls.servers[s.ls.environment.nextStep.actor].config[(s.ls.servers[s.ls.environment.nextStep.actor].my_index + 1) % |s.ls.servers[s.ls.environment.nextStep.actor].config|]]
            else
               s'.history == s.history
            )
    }
}   

