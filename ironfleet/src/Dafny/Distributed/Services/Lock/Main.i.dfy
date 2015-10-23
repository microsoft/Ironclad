include "../../Common/Framework/Main.s.dfy"
include "../../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "../../Impl/Lock/PacketParsing.i.dfy"
include "../../Impl/Lock/UdpLock.i.dfy"

module Main_i exclusively refines Main_s {
    import opened DistributedSystem_i
    import opened Environment_s
    import opened Concrete_NodeIdentity_i
    import opened PacketParsing_i
    import opened UdpLock_i

    type ConcreteConfiguration = Config

    predicate IsValidBehavior(config:ConcreteConfiguration, db:seq<DS_State>)
        reads *;
    {
           |db| > 0
        && DS_Init(db[0], config)
        && forall i :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1])
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
        //requires forall p :: p in sent ==> LPacketIsAbstractable(p);
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

    

    function AbstractifyConcreteConfiguration(ds_config:ConcreteConfiguration) : Config
        //requires ConstantsStateIsValid(ds_config);
    {
        ds_config
    }

    lemma {:timeLimitMultiplier 2} RefinementToLSState(config:ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<LS_State>)
        requires |db| > 0;
        requires DS_Init(db[0], config);
        requires LEnvStepIsAbstractable(last(db).environment.nextStep);
        requires forall i :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        ensures  |sb| == |db|;
        ensures  LS_Init(sb[0], AbstractifyConcreteConfiguration(db[0].config));
        ensures  forall i :: 0 <= i < |sb| - 1 ==> LS_Next(sb[i], sb[i+1]);
        ensures forall i :: 0 <= i < |db| ==> DsStateIsAbstractable(db[i]) 
                                           && sb[i] == AbstractifyDsState(db[i]);
        //ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i]);
    {
    }

    lemma RefinementProofForFixedBehavior(config:ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<ServiceState>, cm:seq<int>)
        requires |db| > 0;
        requires DS_Init(db[0], config);
        requires forall i :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        requires last(db).environment.nextStep.LEnvStepStutter?;
        ensures  |db| == |cm|;
        ensures  cm[0] == 0;                                            // Beginnings match
        ensures  forall i :: 0 <= i < |cm| ==> 0 <= cm[i] < |sb|;       // Mappings are in bounds
        ensures  forall i :: 0 <= i < |cm| - 1 ==> cm[i] <= cm[i+1];    // Mapping is monotonic
        ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].servers));
        ensures  forall i :: 0 <= i < |sb| - 1 ==> Service_Next(sb[i], sb[i+1]);
        ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[cm[i]]);
    
}