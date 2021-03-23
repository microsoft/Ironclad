include "../Collections/Maps2.s.dfy"
include "../Logic/Temporal/Temporal.s.dfy"

module Environment_s {
import opened Collections__Maps2_s
import opened Temporal__Temporal_s

datatype LPacket<IdType, MessageType(==)> = LPacket(dst:IdType, src:IdType, msg:MessageType)

datatype LIoOp<IdType, MessageType(==)> = LIoOpSend(s:LPacket<IdType, MessageType>)
                                        | LIoOpReceive(r:LPacket<IdType, MessageType>)
                                        | LIoOpTimeoutReceive()
                                        | LIoOpReadClock(t:int)

datatype LEnvStep<IdType, MessageType(==)> = LEnvStepHostIos(actor:IdType, ios:seq<LIoOp<IdType, MessageType>>)
                                           | LEnvStepDeliverPacket(p:LPacket<IdType, MessageType>)
                                           | LEnvStepAdvanceTime()
                                           | LEnvStepStutter()

datatype LHostInfo<IdType, MessageType(==)> = LHostInfo(queue:seq<LPacket<IdType, MessageType>>)

datatype LEnvironment<IdType, MessageType(==)> = LEnvironment(time:int,
                                                              sentPackets:set<LPacket<IdType, MessageType>>,
                                                              hostInfo:map<IdType, LHostInfo<IdType, MessageType>>,
                                                              nextStep:LEnvStep<IdType, MessageType>)
                                        
predicate IsValidLIoOp<IdType, MessageType>(io:LIoOp, actor:IdType, e:LEnvironment<IdType, MessageType>)
{
  match io
    case LIoOpSend(s) => s.src == actor
    case LIoOpReceive(r) => r.dst == actor
    case LIoOpTimeoutReceive => true
    case LIoOpReadClock(t) => true
}

predicate LIoOpOrderingOKForAction<IdType, MessageType>(
  io1:LIoOp<IdType, MessageType>,
  io2:LIoOp<IdType, MessageType>
  )
{
  io1.LIoOpReceive? || io2.LIoOpSend?
}

predicate LIoOpSeqCompatibleWithReduction<IdType, MessageType>(
  ios:seq<LIoOp<IdType, MessageType>>
  )
{
  forall i {:trigger ios[i], ios[i+1]} :: 0 <= i < |ios| - 1 ==> LIoOpOrderingOKForAction(ios[i], ios[i+1])
}

predicate IsValidLEnvStep<IdType, MessageType>(e:LEnvironment<IdType, MessageType>, step:LEnvStep)
{
  match step
    case LEnvStepHostIos(actor, ios) => && (forall io :: io in ios ==> IsValidLIoOp(io, actor, e))
                                        && LIoOpSeqCompatibleWithReduction(ios)
    case LEnvStepDeliverPacket(p) => p in e.sentPackets
    case LEnvStepAdvanceTime => true
    case LEnvStepStutter => true
}

predicate LEnvironment_Init<IdType, MessageType>(
  e:LEnvironment<IdType, MessageType>
  )
{
  && |e.sentPackets| == 0
  && e.time >= 0
}

predicate LEnvironment_PerformIos<IdType, MessageType>(
  e:LEnvironment<IdType, MessageType>,
  e':LEnvironment<IdType, MessageType>,
  actor:IdType,
  ios:seq<LIoOp<IdType, MessageType>>
  )
{
  && e'.sentPackets == e.sentPackets + (set io | io in ios && io.LIoOpSend? :: io.s)
  && (forall io :: io in ios && io.LIoOpReceive? ==> io.r in e.sentPackets)
  && e'.time == e.time
}

predicate LEnvironment_AdvanceTime<IdType, MessageType>(
  e:LEnvironment<IdType, MessageType>,
  e':LEnvironment<IdType, MessageType>
  )
{
  && e'.time > e.time
  // UNCHANGED
  && e'.sentPackets == e.sentPackets
}

predicate LEnvironment_Stutter<IdType, MessageType>(
  e:LEnvironment<IdType, MessageType>,
  e':LEnvironment<IdType, MessageType>
  )
{
  && e'.time == e.time
  && e'.sentPackets == e.sentPackets
}

predicate LEnvironment_Next<IdType, MessageType>(
  e:LEnvironment<IdType, MessageType>,
  e':LEnvironment<IdType, MessageType>
  )
{
  && IsValidLEnvStep(e, e.nextStep)
  && match e.nextStep
      case LEnvStepHostIos(actor, ios) => LEnvironment_PerformIos(e, e', actor, ios)
      case LEnvStepDeliverPacket(p) => LEnvironment_Stutter(e, e') // this is only relevant for synchrony
      case LEnvStepAdvanceTime => LEnvironment_AdvanceTime(e, e')
      case LEnvStepStutter => LEnvironment_Stutter(e, e')
}

function{:opaque} EnvironmentNextTemporal<IdType,MessageType>(b:Behavior<LEnvironment<IdType, MessageType>>):temporal
  requires imaptotal(b)
  ensures forall i {:trigger sat(i, EnvironmentNextTemporal(b))} ::
              sat(i, EnvironmentNextTemporal(b)) <==> LEnvironment_Next(b[i], b[nextstep(i)])
{
  stepmap(imap i :: LEnvironment_Next(b[i], b[nextstep(i)]))
}

predicate LEnvironment_BehaviorSatisfiesSpec<IdType, MessageType>(
  b:Behavior<LEnvironment<IdType, MessageType>>
  )
{
  && imaptotal(b)
  && LEnvironment_Init(b[0])
  && sat(0, always(EnvironmentNextTemporal(b)))
}

} 
