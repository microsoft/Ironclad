include "../../Common/Framework/Main.s.dfy"
include "../../Impl/RSL/Host.i.dfy"
include "../../Protocol/RSL/RefinementProof/Refinement.i.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "RSLDistributedSystem.i.dfy"
include "AbstractService.s.dfy"
include "Marshall.i.dfy"

module Main_i refines Main_s {

import opened Native__NativeTypes_s
import opened Host = Host_i
import opened DS_s = RSL_DistributedSystem_i
import opened DirectRefinement__Refinement_i
import opened Concrete_NodeIdentity_i
import opened AS_s = AbstractServiceRSL_s
import opened MarshallProof_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__Constants_i
import opened LiveRSL__ConstantsState_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Message_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__Replica_i
import opened LiveRSL__Types_i
import opened LiveRSL__UdpRSL_i
import opened LiveRSL__Unsendable_i
import opened Collections__Maps2_s
import opened Collections__Sets_i
import opened Common__GenericMarshalling_i
import opened Common__NodeIdentity_i
import opened Common__SeqIsUniqueDef_i
import opened DirectRefinement__StateMachine_i
import opened Environment_s
import opened Math__mod_auto_i

predicate IsValidBehavior(config:ConcreteConfiguration, db:seq<DS_State>)
  reads *
{
  && |db| > 0
  && DS_Init(db[0], config)
  && forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1])
}   

predicate LPacketIsAbstractable(cp:LPacket<EndPoint,seq<byte>>)
{
  CMessageIsAbstractable(PaxosDemarshallData(cp.msg))
}

function AbstractifyConcretePacket(p:LPacket<EndPoint,seq<byte>>) : LPacket<NodeIdentity, RslMessage>
  requires LPacketIsAbstractable(p)
{
  LPacket(p.dst, p.src, AbstractifyCMessageToRslMessage(PaxosDemarshallData(p.msg)))
}

predicate LEnvStepIsAbstractable(step:LEnvStep<EndPoint,seq<byte>>)
{
  match step {
    case LEnvStepHostIos(actor, ios) => UdpEventLogIsAbstractable(ios)
    case LEnvStepDeliverPacket(p) => LPacketIsAbstractable(p)
    case LEnvStepAdvanceTime => true
    case LEnvStepStutter => true
  }
}

function AbstractifyConcreteEnvStep(step:LEnvStep<EndPoint,seq<byte>>) : LEnvStep<NodeIdentity, RslMessage>
  requires LEnvStepIsAbstractable(step)
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
  && (forall p :: p in ds_env.sentPackets ==> LPacketIsAbstractable(p))
  && LEnvStepIsAbstractable(ds_env.nextStep)
}

function AbstractifyConcreteSentPackets(sent:set<LPacket<EndPoint,seq<byte>>>) : set<LPacket<NodeIdentity, RslMessage>>
  requires forall p :: p in sent ==> LPacketIsAbstractable(p)
{
  set p | p in sent :: AbstractifyConcretePacket(p)
}

function AbstractifyConcreteEnvironment(ds_env:LEnvironment<EndPoint,seq<byte>>) : LEnvironment<NodeIdentity, RslMessage>
  requires ConcreteEnvironmentIsAbstractable(ds_env)
{
  LEnvironment(ds_env.time,
               AbstractifyConcreteSentPackets(ds_env.sentPackets),
               map [],
               AbstractifyConcreteEnvStep(ds_env.nextStep))
}

function AbstractifyConcreteReplicas(replicas:map<EndPoint,HostState>, replica_order:seq<EndPoint>) : seq<LScheduler>
  requires forall r :: r in replica_order ==> r in replicas
  ensures  |AbstractifyConcreteReplicas(replicas, replica_order)| == |replica_order|
  ensures  forall i :: 0 <= i < |replica_order| ==>
             AbstractifyConcreteReplicas(replicas, replica_order)[i] == replicas[replica_order[i]].sched
{
  if replica_order == [] then []
  else
    [replicas[replica_order[0]].sched] + AbstractifyConcreteReplicas(replicas, replica_order[1..])
}

function AbstractifyConcreteClients(clients:set<EndPoint>) : set<NodeIdentity>
{
  set e | e in clients :: e
}

predicate DsStateIsAbstractable(ds:DS_State)
{
  && ConstantsStateIsAbstractable(ds.config)
  && ConcreteEnvironmentIsAbstractable(ds.environment)
  && (forall r :: r in ds.config.config.replica_ids ==> r in ds.servers)
}

function AbstractifyDsState(ds:DS_State) : RslState
  requires DsStateIsAbstractable(ds)
{
  RslState(AbstractifyConstantsStateToLConstants(ds.config),
           AbstractifyConcreteEnvironment(ds.environment),
           AbstractifyConcreteReplicas(ds.servers, ds.config.config.replica_ids),
           AbstractifyConcreteClients(ds.clients))
}

lemma lemma_DeduceTransitionFromDsBehavior(
  config:ConcreteConfiguration,
  db:seq<DS_State>,
  i:int
  )
  requires IsValidBehavior(config, db)
  requires 0 <= i < |db| - 1
  ensures  DS_Next(db[i], db[i+1])
{
}

lemma lemma_DsNextOffset(db:seq<DS_State>, index:int)
  requires |db| > 0
  requires 0 < index < |db|
  requires forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1])
  ensures  DS_Next(db[index-1], db[index])
{
  var i := index - 1;
  assert DS_Next(db[i], db[i+1]); // OBSERVE trigger for the forall
}

lemma lemma_DsConsistency(config:ConcreteConfiguration, db:seq<DS_State>, i:int)
  requires IsValidBehavior(config, db)
  requires 0 <= i < |db|
  ensures  db[i].config == config
  ensures  mapdomain(db[i].servers) == mapdomain(db[0].servers)
  ensures  db[i].clients == db[0].clients
{
  if i == 0 {
  } else {
    lemma_DsConsistency(config, db, i-1);
    lemma_DeduceTransitionFromDsBehavior(config, db, i-1);

    assert forall server :: server in db[i-1].servers ==> server in db[i].servers;
    assert forall server :: server in db[i].servers ==> server in db[i-1].servers;

    forall server | server in mapdomain(db[i-1].servers)
      ensures server in mapdomain(db[i].servers)
    {
      assert server in db[i-1].servers;
      assert server in db[i].servers;
    }

    forall server | server in mapdomain(db[i].servers)
      ensures server in mapdomain(db[i-1].servers)
    {
      assert server in db[i].servers;
      assert server in db[i-1].servers;
    }
  }
}

lemma lemma_LSchedulerNextPreservesConstants(
  s:LScheduler,
  s':LScheduler,
  ios:seq<RslIo>
  )
  requires LSchedulerNext(s, s', ios)
  ensures  s.replica.constants == s.replica.constants
  ensures  s.replica.proposer.constants == s.replica.proposer.constants
  ensures  s.replica.acceptor.constants == s.replica.acceptor.constants
  ensures  s.replica.learner.constants == s.replica.learner.constants
  ensures  s.replica.executor.constants == s.replica.executor.constants
{
}

lemma {:timeLimitMultiplier 2} lemma_DsConstantsAllConsistent(config:ConcreteConfiguration, db:seq<DS_State>, i:int, id:EndPoint)
  requires IsValidBehavior(config, db)
  requires 0 <= i < |db|
  requires id in db[i].servers
  ensures  db[i].config == config
  ensures  db[i].servers[id].sched.replica.constants.all == AbstractifyConstantsStateToLConstants(config)
  ensures  db[i].servers[id].sched.replica.proposer.constants.all == AbstractifyConstantsStateToLConstants(config)
  ensures  db[i].servers[id].sched.replica.acceptor.constants.all == AbstractifyConstantsStateToLConstants(config)
  ensures  db[i].servers[id].sched.replica.learner.constants.all == AbstractifyConstantsStateToLConstants(config)
  ensures  db[i].servers[id].sched.replica.executor.constants.all == AbstractifyConstantsStateToLConstants(config)
{
  if i == 0
  {
    assert DS_Init(db[0], config);
    return;
  }

  lemma_DsConsistency(config, db, i-1);
  lemma_DsConsistency(config, db, i);
  lemma_DeduceTransitionFromDsBehavior(config, db, i-1);

  assert mapdomain(db[i].servers) == mapdomain(db[0].servers) == mapdomain(db[i-1].servers);

  lemma_DsConstantsAllConsistent(config, db, i-1, id);

  var s := db[i-1].servers[id].sched;
  var s' := db[i].servers[id].sched;

  if s' == s
  {
    return;
  }

  var ios :| DS_NextOneServer(db[i-1], db[i], id, ios);
  var rios := AbstractifyRawLogToIos(ios);
  assert LSchedulerNext(s, s', rios) || HostNextIgnoreUnsendable(s, s', ios);
  if LSchedulerNext(s, s', rios)
  {
    lemma_LSchedulerNextPreservesConstants(s, s', rios);
  }
  else
  {
    assert s'.replica == s.replica;
  }
}

lemma lemma_PacketSentByServerIsMarshallable(
  config:ConcreteConfiguration,
  db:seq<DS_State>,
  i:int,
  p:LPacket<EndPoint, seq<byte>>
  )
  requires IsValidBehavior(config, db)
  requires 0 <= i < |db|
  requires p.src in config.config.replica_ids
  requires p in db[i].environment.sentPackets
  ensures  UdpPacketBound(p.msg)
  ensures  Marshallable(PaxosDemarshallData(p.msg))
{
  if i == 0 {
    return;
  }

  if p in db[i-1].environment.sentPackets {
    lemma_PacketSentByServerIsMarshallable(config, db, i-1, p);
    return;
  }

  lemma_DeduceTransitionFromDsBehavior(config, db, i-1);
  lemma_DsConsistency(config, db, i-1);
  assert LEnvironment_Next(db[i-1].environment, db[i].environment);
  assert db[i-1].environment.nextStep.LEnvStepHostIos?;
  var io := LIoOpSend(p);
  var ios := db[i-1].environment.nextStep.ios;
  assert io in ios;
  assert IsValidLIoOp(io, db[i-1].environment.nextStep.actor, db[i-1].environment);
  assert db[i-1].environment.nextStep.actor == p.src;
  assert DS_NextOneServer(db[i-1], db[i], p.src, ios);
  assert OnlySentMarshallableData(ios);
  assert UdpPacketBound(io.s.msg);
  assert Marshallable(PaxosDemarshallData(io.s.msg));
}

lemma lemma_SentPacketIsValidPhysicalPacket(
  config:ConcreteConfiguration,
  db:seq<DS_State>,
  i:int,
  p:LPacket<EndPoint, seq<byte>>
  )
  requires IsValidBehavior(config, db)
  requires 0 <= i < |db|
  requires p in db[i].environment.sentPackets
  ensures  ValidPhysicalPacket(p)
{
  if i == 0 {
    return;
  }

  if p in db[i-1].environment.sentPackets {
    lemma_SentPacketIsValidPhysicalPacket(config, db, i-1, p);
    return;
  }

  lemma_DeduceTransitionFromDsBehavior(config, db, i-1);
  assert LEnvironment_Next(db[i-1].environment, db[i].environment);
  assert db[i-1].environment.nextStep.LEnvStepHostIos?;
  var io := LIoOpSend(p);
  assert io in db[i-1].environment.nextStep.ios;
  assert ValidPhysicalEnvironmentStep(db[i-1].environment.nextStep);
}

lemma lemma_UdpEventIsAbstractable(
  config:ConcreteConfiguration,
  db:seq<DS_State>,
  i:int,
  udp_event:UdpEvent
  )
  requires IsValidBehavior(config, db)
  requires 0 <= i < |db| - 1
  requires db[i].environment.nextStep.LEnvStepHostIos?
  requires udp_event in db[i].environment.nextStep.ios
  ensures  UdpEventIsAbstractable(udp_event)
{
  if udp_event.LIoOpTimeoutReceive? || udp_event.LIoOpReadClock? {
    return;
  }

  lemma_DeduceTransitionFromDsBehavior(config, db, i);
  assert ValidPhysicalEnvironmentStep(db[i].environment.nextStep);
  assert ValidPhysicalIo(udp_event);
}

lemma lemma_DsIsAbstractable(config:ConcreteConfiguration, db:seq<DS_State>, i:int)
  requires IsValidBehavior(config, db)
  requires 0 <= i < |db|
  requires LEnvStepIsAbstractable(last(db).environment.nextStep)
  ensures  DsStateIsAbstractable(db[i])
{
  lemma_DsConsistency(config, db, i);

  forall p | p in db[i].environment.sentPackets
    ensures LPacketIsAbstractable(p)
  {
    lemma_SentPacketIsValidPhysicalPacket(config, db, i, p);
  }

  if i == |db|-1
  {
    return;
  }

  var step := db[i].environment.nextStep;
  if step.LEnvStepHostIos? {
    forall io | io in step.ios
      ensures UdpEventIsAbstractable(io)
    {
      lemma_UdpEventIsAbstractable(config, db, i, io);
    }
    assert UdpEventLogIsAbstractable(step.ios);
  }
  else if step.LEnvStepDeliverPacket? {
    lemma_DeduceTransitionFromDsBehavior(config, db, i);
    assert IsValidLEnvStep(db[i].environment, step);
    assert step.p in db[i].environment.sentPackets;
    lemma_SentPacketIsValidPhysicalPacket(config, db, i, step.p);
  }
}

lemma lemma_IosRelations(ios:seq<LIoOp<EndPoint, seq<byte>>>, r_ios:seq<LIoOp<NodeIdentity, RslMessage>>)
        returns (sends:set<LPacket<EndPoint, seq<byte>>>, r_sends:set<LPacket<NodeIdentity, RslMessage>>)
  requires UdpEventLogIsAbstractable(ios)
  requires forall io :: io in ios && io.LIoOpSend? ==> LPacketIsAbstractable(io.s)
  requires r_ios == AbstractifyRawLogToIos(ios)
  ensures    sends == (set io | io in ios && io.LIoOpSend? :: io.s)
  ensures  r_sends == (set io | io in r_ios && io.LIoOpSend? :: io.s)
  ensures  forall send :: send in sends ==> LPacketIsAbstractable(send)
  ensures  r_sends == AbstractifyConcreteSentPackets(sends)
{
  sends := (set io | io in ios && io.LIoOpSend? :: io.s);
  r_sends := (set io | io in r_ios && io.LIoOpSend? :: io.s);
  var refined_sends := AbstractifyConcreteSentPackets(sends);

  forall r | r in refined_sends
    ensures r in r_sends
  {
    var send :| send in sends && AbstractifyConcretePacket(send) == r;
    var io :| io in ios && io.LIoOpSend? && io.s == send;
    assert AbstractifyUdpEventToRslIo(io) in r_ios;
  }

  forall r | r in r_sends
    ensures r in refined_sends
  {
    var r_io :| r_io in r_ios && r_io.LIoOpSend? && r_io.s == r;
    var j :| 0 <= j < |r_ios| && r_ios[j] == r_io;
    assert AbstractifyUdpEventToRslIo(ios[j]) == r_io;
    assert ios[j] in ios;
    assert ios[j].s in sends;
  }
}

lemma lemma_IsValidEnvStep(de:LEnvironment<EndPoint, seq<byte>>, le:LEnvironment<NodeIdentity, RslMessage>)
  requires IsValidLEnvStep(de, de.nextStep)
  requires de.nextStep.LEnvStepHostIos?
  requires ConcreteEnvironmentIsAbstractable(de)
  requires AbstractifyConcreteEnvironment(de) == le
  ensures  IsValidLEnvStep(le, le.nextStep)
{
  var id := de.nextStep.actor;
  var ios := de.nextStep.ios;
  var r_ios := le.nextStep.ios;

  assert LIoOpSeqCompatibleWithReduction(r_ios);

  forall io | io in r_ios
    ensures IsValidLIoOp(io, id, le)
  {
    var j :| 0 <= j < |r_ios| && r_ios[j] == io;
    assert r_ios[j] == AbstractifyUdpEventToRslIo(ios[j]);
    assert IsValidLIoOp(ios[j], id, de);
  }
}

lemma lemma_LEnvironmentNextHost(de :LEnvironment<EndPoint, seq<byte>>, le :LEnvironment<NodeIdentity, RslMessage>,
                                 de':LEnvironment<EndPoint, seq<byte>>, le':LEnvironment<NodeIdentity, RslMessage>)
  requires ConcreteEnvironmentIsAbstractable(de)
  requires ConcreteEnvironmentIsAbstractable(de')
  requires AbstractifyConcreteEnvironment(de)  == le
  requires AbstractifyConcreteEnvironment(de') == le'
  requires de.nextStep.LEnvStepHostIos?
  requires LEnvironment_Next(de, de')
  ensures  LEnvironment_Next(le, le')
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

lemma lemma_RefinementOfUnsendablePacketHasLimitedPossibilities(
  p:LPacket<EndPoint, seq<byte>>,
  g:G,
  rp:RslPacket
  )
  requires g == CMessage_grammar()
  requires ValidGrammar(g)
  requires !Demarshallable(p.msg, g) || !Marshallable(parse_Message(DemarshallFunc(p.msg, g)))
  requires UdpPacketIsAbstractable(p)
  requires rp == AbstractifyUdpPacketToRslPacket(p)
  ensures  || rp.msg.RslMessage_Invalid?
           || rp.msg.RslMessage_1b?
           || rp.msg.RslMessage_2a?
           || rp.msg.RslMessage_2b?
           || rp.msg.RslMessage_AppStateSupply?
{
}

lemma lemma_IgnoringUnsendableGivesEmptySentPackets(ios:seq<RslIo>)
  requires |ios| == 1
  requires ios[0].LIoOpReceive?
  ensures  ExtractSentPacketsFromIos(ios) == []
{
  reveal ExtractSentPacketsFromIos();
}

lemma lemma_IgnoringInvalidMessageIsLSchedulerNext(
  s:LScheduler,
  s':LScheduler,
  ios:seq<RslIo>
  )
  requires s.nextActionIndex == 0
  requires s' == s.(nextActionIndex := (s.nextActionIndex + 1) % LReplicaNumActions())
  requires |ios| == 1
  requires ios[0].LIoOpReceive?
  requires ios[0].r.msg.RslMessage_Invalid?
  ensures  LSchedulerNext(s, s', ios)
{
  var sent_packets := ExtractSentPacketsFromIos(ios);
  lemma_IgnoringUnsendableGivesEmptySentPackets(ios);
  assert LReplicaNextProcessInvalid(s.replica, s'.replica, ios[0].r, sent_packets);
  assert LReplicaNextProcessPacketWithoutReadingClock(s.replica, s'.replica, ios);
  assert LReplicaNextProcessPacket(s.replica, s'.replica, ios);
}

lemma lemma_IgnoringCertainMessageTypesFromNonServerIsLSchedulerNext(
  config:ConcreteConfiguration,
  db:seq<DS_State>,
  i:int,
  id:EndPoint,
  s:LScheduler,
  s':LScheduler,
  ios:seq<RslIo>
  )
  requires IsValidBehavior(config, db)
  requires 0 <= i < |db| - 1
  requires id in db[i].servers
  requires id in db[i+1].servers
  requires s == db[i].servers[id].sched
  requires s' == db[i+1].servers[id].sched
  requires s.nextActionIndex == 0
  requires s' == s.(nextActionIndex := (s.nextActionIndex + 1) % LReplicaNumActions())
  requires |ios| == 1
  requires ios[0].LIoOpReceive?
  requires || ios[0].r.msg.RslMessage_1b?
           || ios[0].r.msg.RslMessage_2a?
           || ios[0].r.msg.RslMessage_2b?
           || ios[0].r.msg.RslMessage_AppStateSupply?
  requires ios[0].r.src !in config.config.replica_ids
  ensures  LSchedulerNext(s, s', ios)
{
  lemma_DsConstantsAllConsistent(config, db, i, id);
  var sent_packets := ExtractSentPacketsFromIos(ios);
  lemma_IgnoringUnsendableGivesEmptySentPackets(ios);
  assert LReplicaNextProcessPacketWithoutReadingClock(s.replica, s'.replica, ios);
  assert LReplicaNextProcessPacket(s.replica, s'.replica, ios);
}

lemma lemma_HostNextIgnoreUnsendableIsLSchedulerNext(
  config:ConcreteConfiguration,
  db:seq<DS_State>,
  i:int,
  id:EndPoint,
  ios:seq<LIoOp<EndPoint, seq<byte>>>
  )
  requires IsValidBehavior(config, db)
  requires 0 <= i < |db| - 1
  requires db[i].environment.nextStep == LEnvStepHostIos(id, ios)
  requires id in db[i].servers
  requires id in db[i+1].servers
  requires LEnvironment_Next(db[i].environment, db[i+1].environment)
  requires ValidPhysicalEnvironmentStep(db[i].environment.nextStep)
  requires HostNextIgnoreUnsendable(db[i].servers[id].sched, db[i+1].servers[id].sched, ios)
  requires UdpEventLogIsAbstractable(ios)
  ensures  LSchedulerNext(db[i].servers[id].sched, db[i+1].servers[id].sched, AbstractifyRawLogToIos(ios))
{
  var p := ios[0].r;
  var rp := AbstractifyUdpPacketToRslPacket(p);
  var g := CMessage_grammar();
  assert !Demarshallable(p.msg, g) || !Marshallable(parse_Message(DemarshallFunc(p.msg, g)));
  assert IsValidLIoOp(ios[0], id, db[i].environment);

  if p.src in config.config.replica_ids
  {
    lemma_PacketSentByServerIsMarshallable(config, db, i, p);
    assert false;
  }

  lemma_UdpEventIsAbstractable(config, db, i, ios[0]);
  lemma_CMessageGrammarValid();
  assert ValidPhysicalIo(ios[0]);
  assert |p.msg| < 0x1_0000_0000_0000_0000;
  assert ValidGrammar(g);

  var rios := AbstractifyRawLogToIos(ios);
  assert |rios| == 1;
  assert rios[0].r == rp;

  var s := db[i].servers[id].sched;
  var s' := db[i+1].servers[id].sched;

  assert s.nextActionIndex == 0;
  calc {
    s'.nextActionIndex;
    1;
      { lemma_mod_auto(LReplicaNumActions()); }
    (s.nextActionIndex + 1) % LReplicaNumActions();
  }

  lemma_RefinementOfUnsendablePacketHasLimitedPossibilities(p, g, rp);

  if rp.msg.RslMessage_Invalid? {
    lemma_IgnoringInvalidMessageIsLSchedulerNext(s, s', rios);
  }
  else {
    lemma_DsConsistency(config, db, i);
    lemma_IgnoringCertainMessageTypesFromNonServerIsLSchedulerNext(config, db, i, id, s, s', rios);
  }
}

lemma {:timeLimitMultiplier 2} lemma_RslNext(
  config:ConcreteConfiguration,
  db:seq<DS_State>,
  i:int,
  ls:RslState,
  ls':RslState
  )
  requires IsValidBehavior(config, db)
  requires 0 <= i < |db| - 1
  requires DsStateIsAbstractable(db[i])
  requires DsStateIsAbstractable(db[i+1])
  requires ls  == AbstractifyDsState(db[i])
  requires ls' == AbstractifyDsState(db[i+1])
  requires forall id :: id in db[i].servers ==> id in db[i].config.config.replica_ids
  ensures  RslNext(ls, ls')
{
  var ds := db[i];
  var ds' := db[i+1];

  lemma_DeduceTransitionFromDsBehavior(config, db, i);

  if !ds.environment.nextStep.LEnvStepHostIos? {
    return;
  }

  lemma_LEnvironmentNextHost(db[i].environment, ls.environment, db[i+1].environment, ls'.environment);

  var id := ds.environment.nextStep.actor;
  var ios := ds.environment.nextStep.ios;
  var r_ios := AbstractifyRawLogToIos(ios);
  var replicas := ds.config.config.replica_ids;

  assert id in ds.servers <==> id in replicas;

  if id !in ds.servers {
    assert RslNextOneExternal(ls, ls', id, r_ios);
    assert RslNext(ls, ls');
    return;
  }

  var index :| 0 <= index < |replicas| && replicas[index] == id;

  assert ls.environment.nextStep == LEnvStepHostIos(id, r_ios);

  assert || LSchedulerNext(ds.servers[id].sched, ds'.servers[id].sched, r_ios)
         || HostNextIgnoreUnsendable(ds.servers[id].sched, ds'.servers[id].sched, ios);
  if HostNextIgnoreUnsendable(ds.servers[id].sched, ds'.servers[id].sched, ios)
  {
    lemma_HostNextIgnoreUnsendableIsLSchedulerNext(config, db, i, id, ios);
  }
  assert LSchedulerNext(ds.servers[id].sched, ds'.servers[id].sched, r_ios);

  assert LEnvironment_Next(ds.environment, ds'.environment);
  lemma_LEnvironmentNextHost(ds.environment, ls.environment, ds'.environment, ls'.environment);
  assert LEnvironment_Next(ls.environment, ls'.environment);

  reveal SeqIsUnique();
  forall other_idx | other_idx != index && 0 <= other_idx < |replicas|
    ensures replicas[other_idx] != replicas[index]
  {
    assert ReplicasDistinct(ls.constants.config.replica_ids, index, other_idx);
  }
  assert RslNextOneReplica(ls, ls', index, r_ios);

  assert RslNext(ls, ls');
}

lemma lemma_GetImplBehaviorRefinement(config:ConcreteConfiguration, db:seq<DS_State>)
  returns (protocol_behavior:seq<RslState>, c:LConstants)
  requires IsValidBehavior(config, db)
  requires LEnvStepIsAbstractable(last(db).environment.nextStep)
  ensures |protocol_behavior| == |db|
  ensures protocol_behavior[0].constants == AbstractifyConstantsStateToLConstants(config)
  ensures RslInit(c, protocol_behavior[0])
  ensures forall i :: 0 <= i < |db| ==> DsStateIsAbstractable(db[i]) && protocol_behavior[i] == AbstractifyDsState(db[i]);
  ensures forall i {:trigger RslNext(protocol_behavior[i], protocol_behavior[i+1])} :: 0 <= i < |protocol_behavior| - 1 ==>
              RslNext(protocol_behavior[i], protocol_behavior[i+1])
{
  c := AbstractifyConstantsStateToLConstants(config);
  if |db| == 1 {
    lemma_DsIsAbstractable(config, db, 0);
    var ls := AbstractifyDsState(db[0]);
    protocol_behavior := [ ls ];

    // Prove RslMapsComplete
    calc {
      |ls.replicas|;
      |AbstractifyConcreteReplicas(db[0].servers, db[0].config.config.replica_ids)|;
      |db[0].config.config.replica_ids|;
      |AbstractifyEndPointsToNodeIdentities(db[0].config.config.replica_ids)|;
      |AbstractifyConstantsStateToLConstants(db[0].config).config.replica_ids|;
      |ls.constants.config.replica_ids|;
    }

    calc {
      ls.constants;
      AbstractifyConstantsStateToLConstants(db[0].config);
      AbstractifyConstantsStateToLConstants(config);
      c;
    }

    forall i | 0 <= i < |c.config.replica_ids|
      ensures LSchedulerInit(ls.replicas[i], LReplicaConstants(i, c))
    {
      reveal SeqIsUnique();
    }
  } else {
    lemma_DsConsistency(config, db, |db|-1);
    lemma_DeduceTransitionFromDsBehavior(config, db, |db|-2);
    lemma_DsIsAbstractable(config, db, |db|-1);
    lemma_DsIsAbstractable(config, db, |db|-2);
    
    var ls' := AbstractifyDsState(last(db));
    var rest, c' := lemma_GetImplBehaviorRefinement(config, all_but_last(db));
    protocol_behavior := rest + [ls'];

    // Help with sequence indexing
    forall i | 0 <= i < |db|
      ensures DsStateIsAbstractable(db[i])
      ensures protocol_behavior[i] == AbstractifyDsState(db[i])
    {
      lemma_DsIsAbstractable(config, db, i);
      if i < |db| - 1 {
        assert db[i] == all_but_last(db)[i];
        assert protocol_behavior[i] == AbstractifyDsState(all_but_last(db)[i]);
        assert protocol_behavior[i] == AbstractifyDsState(db[i]);
      } else {
        assert protocol_behavior[i] == ls';
        assert i == |db| - 1;
        assert db[i] == last(db);
        assert protocol_behavior[i] == AbstractifyDsState(db[i]);
      }
    }

    // Prove the crucial ensures
    forall i | 0 <= i < |protocol_behavior| - 1
      ensures RslNext(protocol_behavior[i], protocol_behavior[i+1])
    {
      if i < |protocol_behavior| - 2 {
        // Induction hypothesis
        assert RslNext(protocol_behavior[i], protocol_behavior[i+1]);
      } else {
        forall id | id in db[i].servers
          ensures id in db[i].config.config.replica_ids
        {
          calc ==> {
            id in db[i].servers;
            id in mapdomain(db[i].servers);
              { lemma_DsConsistency(config, db, i); }
            id in mapdomain(db[0].servers);
            id in db[0].config.config.replica_ids;
              { lemma_DsConsistency(config, db, i); }
            id in db[i].config.config.replica_ids;
          }
        }
        lemma_RslNext(config, db, i, protocol_behavior[i], protocol_behavior[i+1]);
        assert RslNext(protocol_behavior[i], protocol_behavior[i+1]);
      }
    }
  }
}

function RenameToAppRequest(request:Request) : AppRequest
{
  AppRequest(request.client, request.seqno, request.request)
}

function RenameToAppReply(reply:Reply) : AppReply
{
  AppReply(reply.client, reply.seqno, reply.reply)
}

function RenameToAppRequests(requests:set<Request>) : set<AppRequest>
{
  set r | r in requests :: RenameToAppRequest(r)
}

function RenameToAppReplies(replies:set<Reply>) : set<AppReply>
{
  set r | r in replies :: RenameToAppReply(r)
}

function RenameToAppBatch(batch:seq<Request>) : seq<AppRequest>
  ensures |RenameToAppBatch(batch)| == |batch|
  ensures forall i :: 0 <= i < |batch| ==> RenameToAppBatch(batch)[i] == RenameToAppRequest(batch[i])
{
  if |batch| == 0 then [] else RenameToAppBatch(all_but_last(batch)) + [RenameToAppRequest(last(batch))]
}

function RenameToServiceState(rs:RSLSystemState) : ServiceState
{
  ServiceState'(rs.server_addresses, rs.app, RenameToAppRequests(rs.requests), RenameToAppReplies(rs.replies))
}

function RenameToServiceStates(rs:seq<RSLSystemState>) : seq<ServiceState>
  ensures |rs| == |RenameToServiceStates(rs)|
  ensures forall i :: 0 <= i < |rs| ==> RenameToServiceState(rs[i]) == RenameToServiceStates(rs)[i]
{
  if rs == [] then []
  else [RenameToServiceState(rs[0])] + RenameToServiceStates(rs[1..])
}

lemma lemma_ServiceNextDoesntChangeServerAddresses(s:ServiceState, s':ServiceState)
  requires s == s' || Service_Next(s, s')
  ensures  s'.serverAddresses == s.serverAddresses
{
  if s == s' {
    return;
  }

  var intermediate_states:seq<ServiceState>, batch :| StateSequenceReflectsBatchExecution(s, s', intermediate_states, batch);
  var i := 0;
  while i < |batch|
    invariant 0 <= i <= |batch|
    invariant intermediate_states[i].serverAddresses == s.serverAddresses
  {
    assert ServiceExecutesAppRequest(intermediate_states[i], intermediate_states[i+1], batch[i]);
    assert intermediate_states[i+1].serverAddresses == intermediate_states[i].serverAddresses == s.serverAddresses;
    i := i + 1;
  }

  assert intermediate_states[i] == last(intermediate_states) == s';
}

lemma lemma_ServiceStateServerAddressesNeverChange(sb:seq<ServiceState>, server_addresses:set<NodeIdentity>, i:int)
  requires |sb| > 0
  requires Service_Init(sb[0], server_addresses)
  requires forall j {:trigger Service_Next(sb[j], sb[j+1])} :: 0 <= j < |sb| - 1 ==> sb[j] == sb[j+1] || Service_Next(sb[j], sb[j+1])
  requires 0 <= i < |sb|
  ensures  sb[i].serverAddresses == server_addresses
{
  if i == 0 {
    return;
  }

  var j := i-1;
  assert sb[j] == sb[j+1] || Service_Next(sb[j], sb[j+1]);
  assert i == j+1;
  assert sb[i-1] == sb[i] || Service_Next(sb[i-1], sb[i]);
  lemma_ServiceNextDoesntChangeServerAddresses(sb[i-1], sb[i]);
  assert sb[i].serverAddresses == sb[i-1].serverAddresses;
  lemma_ServiceStateServerAddressesNeverChange(sb, server_addresses, i-1);
}

lemma lemma_RslSystemNextImpliesServiceNext(
  rs:RSLSystemState,
  rs':RSLSystemState,
  s:ServiceState,
  s':ServiceState'
  )
  requires s == RenameToServiceState(rs)
  requires s' == RenameToServiceState(rs')
  requires RslSystemNext(rs, rs')
  ensures  Service_Next(s, s')
{
  var intermediate_states, batch :| RslStateSequenceReflectsBatchExecution(rs, rs', intermediate_states, batch);
  var intermediate_states_renamed := RenameToServiceStates(intermediate_states);
  var batch_renamed := RenameToAppBatch(batch);
  assert StateSequenceReflectsBatchExecution(s, s', intermediate_states_renamed, batch_renamed);
}

lemma lemma_RefinementProofForFixedBehavior(config:ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<ServiceState>)
  requires IsValidBehavior(config, db)
  requires last(db).environment.nextStep.LEnvStepStutter?
  ensures  |db| == |sb|
  ensures  Service_Init(sb[0], mapdomain(db[0].servers))
  ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1])
  ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i])
{
  var protocol_behavior, lconstants := lemma_GetImplBehaviorRefinement(config, db);
  var rs := lemma_GetBehaviorRefinement(protocol_behavior, lconstants);
  sb := RenameToServiceStates(rs);

  var server_addresses := MapSeqToSet(config.config.replica_ids, x=>x);
  assert Service_Init(sb[0], server_addresses);

  forall i {:trigger Service_Next(sb[i], sb[i+1])} | 0 <= i < |sb| - 1
    ensures sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1])
  {
    lemma_RslSystemNextImpliesServiceNext(rs[i], rs[i+1], sb[i], sb[i+1]);
  }

  forall i | 0 <= i < |db|
    ensures Service_Correspondence(db[i].environment.sentPackets, sb[i])
  {
    var concretePkts := db[i].environment.sentPackets;
    var serviceState := sb[i];

    var rsl := rs[i];
    var ps := protocol_behavior[i];
    assert RslSystemRefinement(ps, rsl);
    assert RenameToServiceState(rsl) == serviceState;

    forall p, seqno, reply | p in concretePkts && p.src in serviceState.serverAddresses && p.msg == MarshallServiceReply(seqno, reply)
      ensures AppReply(p.dst, seqno, reply) in serviceState.replies;
    {
      var abstract_p := AbstractifyConcretePacket(p);
      lemma_ServiceStateServerAddressesNeverChange(sb, server_addresses, i);
      assert serviceState.serverAddresses == server_addresses;
      assert p.src in config.config.replica_ids;
      lemma_PacketSentByServerIsMarshallable(config, db, i, p);
      lemma_ParseMarshallReply(p.msg, seqno, reply, abstract_p.msg);

      assert abstract_p in ps.environment.sentPackets && abstract_p.src in rsl.server_addresses && abstract_p.msg.RslMessage_Reply?;
      var r := Reply(abstract_p.dst, abstract_p.msg.seqno_reply, abstract_p.msg.reply);
      assert r in rsl.replies;
      var service_reply := RenameToAppReply(r);
      assert service_reply == AppReply(p.dst, seqno, reply);
      assert service_reply in serviceState.replies;
    }

    forall req | req in serviceState.requests
      ensures exists p :: p in concretePkts && p.dst in serviceState.serverAddresses
                                     && p.msg == MarshallServiceRequest(req.seqno, req.request)
                                     && p.src == req.client
    {
      var r_req :| r_req in rsl.requests && RenameToAppRequest(r_req) == req;
      var abstract_p :| && abstract_p in ps.environment.sentPackets
                        && abstract_p.dst in rsl.server_addresses
                        && abstract_p.msg.RslMessage_Request?
                        && r_req == Request(abstract_p.src, abstract_p.msg.seqno_req, abstract_p.msg.val);

      assert ps.environment.sentPackets == AbstractifyConcreteSentPackets(concretePkts);
      var concrete_p :| concrete_p in concretePkts && AbstractifyConcretePacket(concrete_p) == abstract_p;
      assert concrete_p.dst in serviceState.serverAddresses;
      assert concrete_p.src == req.client;
      lemma_ParseMarshallRequest(concrete_p.msg, abstract_p.msg);
      assert concrete_p.msg == MarshallServiceRequest(req.seqno, req.request);
    }
  }
}

lemma lemma_FixFinalEnvStep(config:ConcreteConfiguration, db:seq<DS_State>) returns (db':seq<DS_State>)
  requires IsValidBehavior(config, db)
  ensures  |db'| == |db|
  ensures  DS_Init(db'[0], config)
  ensures  forall i {:trigger DS_Next(db'[i], db'[i+1])} :: 0 <= i < |db'| - 1 ==> DS_Next(db'[i], db'[i+1])
  ensures  last(db').environment.nextStep.LEnvStepStutter?
  ensures  forall i :: 0 <= i < |db'| - 1 ==> db'[i] == db[i]
  ensures  last(db') == last(db).(environment := last(db').environment)
  ensures  last(db').environment == last(db).environment.(nextStep := LEnvStepStutter())
{
  var sz := |db|;
  db' := all_but_last(db) + [last(db).(environment := last(db).environment.(nextStep := LEnvStepStutter()))];
  assert |db'| == |db|;
  forall i | 0 <= i < |db'| - 1
    ensures DS_Next(db'[i], db'[i+1])
  {
    lemma_DeduceTransitionFromDsBehavior(config, db, i);
    if i == sz - 2
    {
      assert DS_Next(db'[i], db'[i+1]);
    }
  }
}

lemma RefinementProof(config:DS_s.H_s.ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<ServiceState>)
{
  var db' := lemma_FixFinalEnvStep(config, db);
  sb := lemma_RefinementProofForFixedBehavior(config, db');
}

}
