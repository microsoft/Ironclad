include "../../Protocol/RSL/Replica.i.dfy"

module LiveRSL__QRelations_i {
import opened LiveRSL__ClockReading_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Replica_i

// This file defines opaque (Q_*) versions of high-level protocol relations
// to reduce the definition space available to combinatorially-challenged
// methods in ReplicaImpl.

predicate AllIosAreSends(ios:seq<RslIo>)
{
  forall i :: 0<=i<|ios| ==> ios[i].LIoOpSend?
}

//////////////////////////////////////////////////////////////////////////////

predicate {:opaque} Q_LReplica_Next_Process_Invalid(replica:LReplica, replica':LReplica, lpacket:RslPacket, sent_packets:seq<RslPacket>)
{ lpacket.msg.RslMessage_Invalid? && LReplicaNextProcessInvalid(replica, replica', lpacket, sent_packets) }

predicate {:opaque} Q_LReplica_Next_Process_Request(replica:LReplica, replica':LReplica, lpacket:RslPacket, sent_packets:seq<RslPacket>)
{ lpacket.msg.RslMessage_Request? && LReplicaNextProcessRequest(replica, replica', lpacket, sent_packets) }

predicate {:opaque} Q_LReplica_Next_Process_1a(replica:LReplica, replica':LReplica, lpacket:RslPacket, sent_packets:seq<RslPacket>)
{ lpacket.msg.RslMessage_1a? && LReplicaNextProcess1a(replica, replica', lpacket, sent_packets) }

predicate {:opaque} Q_LReplica_Next_Process_1b(replica:LReplica, replica':LReplica, lpacket:RslPacket, sent_packets:seq<RslPacket>)
{ lpacket.msg.RslMessage_1b? && LReplicaNextProcess1b(replica, replica', lpacket, sent_packets) }

predicate {:opaque} Q_LReplica_Next_Process_StartingPhase2(replica:LReplica, replica':LReplica, lpacket:RslPacket, sent_packets:seq<RslPacket>)
{ lpacket.msg.RslMessage_StartingPhase2? && LReplicaNextProcessStartingPhase2(replica, replica', lpacket, sent_packets) }

predicate {:opaque} Q_LReplica_Next_Process_2a(replica:LReplica, replica':LReplica, lpacket:RslPacket, sent_packets:seq<RslPacket>)
{ lpacket.msg.RslMessage_2a? && LReplicaNextProcess2a(replica, replica', lpacket, sent_packets) }

predicate {:opaque} Q_LReplica_Next_Process_2b(replica:LReplica, replica':LReplica, lpacket:RslPacket, sent_packets:seq<RslPacket>)
{ lpacket.msg.RslMessage_2b? && LReplicaNextProcess2b(replica, replica', lpacket, sent_packets) }

// TODO move this definition into Replica.i
predicate {:opaque} Q_LReplica_Next_Process_Reply(replica:LReplica, replica':LReplica, lpacket:RslPacket, sent_packets:seq<RslPacket>)
{ lpacket.msg.RslMessage_Reply? && LReplicaNextProcessReply(replica, replica', lpacket, sent_packets) }

predicate {:opaque} Q_LReplica_Next_Process_AppStateRequest(replica:LReplica, replica':LReplica, lpacket:RslPacket, sent_packets:seq<RslPacket>)
{ lpacket.msg.RslMessage_AppStateRequest? && LReplicaNextProcessAppStateRequest(replica, replica', lpacket, sent_packets) }

predicate {:opaque} Q_LReplica_Next_Process_AppStateSupply(replica:LReplica, replica':LReplica, lpacket:RslPacket, sent_packets:seq<RslPacket>)
{ lpacket.msg.RslMessage_AppStateSupply? && LReplicaNextProcessAppStateSupply(replica, replica', lpacket, sent_packets) }



predicate LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios:seq<RslIo>)
{
  && |ios| >= 1
  && ios[0].LIoOpReceive?
  && !ios[0].r.msg.RslMessage_Heartbeat?
}

predicate {:opaque} Q_LReplica_Next_ProcessPacketWithoutReadingClock(replica:LReplica, replica':LReplica, ios:seq<RslIo>)
{
  && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
  && LReplicaNextProcessPacketWithoutReadingClock(replica, replica', ios)
}

predicate Establish_Q_LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(replica:LReplica, replica':LReplica, lpacket:RslPacket, sent_packets:seq<RslPacket>, ios:seq<RslIo>)
{
  && sent_packets == ExtractSentPacketsFromIos(ios)
//  && clock == SpontaneousClock(ios)
  && (|| (lpacket.msg.RslMessage_Request? && Q_LReplica_Next_Process_Request(replica, replica', lpacket, sent_packets))
     || (lpacket.msg.RslMessage_1a? && Q_LReplica_Next_Process_1a(replica, replica', lpacket, sent_packets))
     || (lpacket.msg.RslMessage_1b? && Q_LReplica_Next_Process_1b(replica, replica', lpacket, sent_packets))
     || (lpacket.msg.RslMessage_StartingPhase2? && Q_LReplica_Next_Process_StartingPhase2(replica, replica', lpacket, sent_packets))
     || (lpacket.msg.RslMessage_2a? && Q_LReplica_Next_Process_2a(replica, replica', lpacket, sent_packets))
     || (lpacket.msg.RslMessage_2b? && Q_LReplica_Next_Process_2b(replica, replica', lpacket, sent_packets))
     || (lpacket.msg.RslMessage_Reply? && Q_LReplica_Next_Process_Reply(replica, replica', lpacket, sent_packets))
     || (lpacket.msg.RslMessage_AppStateRequest? && Q_LReplica_Next_Process_AppStateRequest(replica, replica', lpacket, sent_packets))
     || (lpacket.msg.RslMessage_AppStateSupply? && Q_LReplica_Next_Process_AppStateSupply(replica, replica', lpacket, sent_packets)))
  && sent_packets == ExtractSentPacketsFromIos(ios)
}

lemma lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica:LReplica, replica':LReplica, lpacket:RslPacket, sent_packets:seq<RslPacket>, ios:seq<RslIo>)
  requires |ios| >= 1
  requires ios[0].LIoOpReceive?
  requires !ios[0].r.msg.RslMessage_Heartbeat?
  requires lpacket == ios[0].r
  requires AllIosAreSends(ios[1..])
  requires sent_packets == ExtractSentPacketsFromIos(ios)
  requires Establish_Q_LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(replica, replica', lpacket, sent_packets, ios)
  ensures Q_LReplica_Next_ProcessPacketWithoutReadingClock(replica, replica', ios)
{
  reveal Q_LReplica_Next_Process_Invalid();
  reveal Q_LReplica_Next_Process_Request();
  reveal Q_LReplica_Next_Process_1a();
  reveal Q_LReplica_Next_Process_1b();
  reveal Q_LReplica_Next_Process_StartingPhase2();
  reveal Q_LReplica_Next_Process_2a();
  reveal Q_LReplica_Next_Process_2b();
  reveal Q_LReplica_Next_Process_Reply();
  reveal Q_LReplica_Next_Process_AppStateRequest();
  reveal Q_LReplica_Next_Process_AppStateSupply();

  reveal Q_LReplica_Next_ProcessPacketWithoutReadingClock();
}

//////////////////////////////////////////////////////////////////////////////

predicate {:opaque} Q_LReplica_Next_Spontaneous_MaybeEnterNewViewAndSend1a(replica:LReplica, replica':LReplica, sent_packets:seq<RslPacket>)
{ LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(replica, replica', sent_packets) }

predicate {:opaque} Q_LReplica_Next_Spontaneous_MaybeEnterPhase2(replica:LReplica, replica':LReplica, sent_packets:seq<RslPacket>)
{ LReplicaNextSpontaneousMaybeEnterPhase2(replica, replica', sent_packets) }

predicate {:opaque} Q_LReplica_Next_Spontaneous_TruncateLogBasedOnCheckpoints(replica:LReplica, replica':LReplica, sent_packets:seq<RslPacket>)
{ LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(replica, replica', sent_packets) }

predicate {:opaque} Q_LReplica_Next_Spontaneous_MaybeMakeDecision(replica:LReplica, replica':LReplica, sent_packets:seq<RslPacket>)
{ LReplicaNextSpontaneousMaybeMakeDecision(replica, replica', sent_packets) }

predicate {:opaque} Q_LReplica_Next_Spontaneous_MaybeExecute(replica:LReplica, replica':LReplica, sent_packets:seq<RslPacket>)
{ LReplicaNextSpontaneousMaybeExecute(replica, replica', sent_packets) }

lemma lemma_EstablishQLReplicaNoReceiveNextFromNoClock(replica:LReplica, replica':LReplica, sent_packets:seq<RslPacket>, nextActionIndex:int, ios:seq<RslIo>)
  requires sent_packets == ExtractSentPacketsFromIos(ios)
  requires SpontaneousIos(ios, 0)
  requires
    || (nextActionIndex==1 && Q_LReplica_Next_Spontaneous_MaybeEnterNewViewAndSend1a(replica, replica', sent_packets))
    || (nextActionIndex==2 && Q_LReplica_Next_Spontaneous_MaybeEnterPhase2(replica, replica', sent_packets))
    //
    || (nextActionIndex==4 && Q_LReplica_Next_Spontaneous_TruncateLogBasedOnCheckpoints(replica, replica', sent_packets))
    || (nextActionIndex==5 && Q_LReplica_Next_Spontaneous_MaybeMakeDecision(replica, replica', sent_packets))
    || (nextActionIndex==6 && Q_LReplica_Next_Spontaneous_MaybeExecute(replica, replica', sent_packets));
  ensures Q_LReplica_NoReceive_Next(replica, nextActionIndex as int, replica', ios)
{
  reveal Q_LReplica_Next_Spontaneous_MaybeEnterNewViewAndSend1a();
  reveal Q_LReplica_Next_Spontaneous_MaybeEnterPhase2();
  //reveal Q_LReplica_Next_Spontaneous_MaybeNominateValueAndSend2a();
  reveal Q_LReplica_Next_Spontaneous_TruncateLogBasedOnCheckpoints();
  reveal Q_LReplica_Next_Spontaneous_MaybeMakeDecision();
  reveal Q_LReplica_Next_Spontaneous_MaybeExecute();

  assert LReplicaNoReceiveNext(replica, nextActionIndex as int, replica', ios);
  reveal Q_LReplica_NoReceive_Next();
  assert Q_LReplica_NoReceive_Next(replica, nextActionIndex as int, replica', ios);
}

//////////////////////////////////////////////////////////////////////////////

predicate {:opaque} Q_LReplica_Next_ReadClock_MaybeNominateValueAndSend2a(replica:LReplica, replica':LReplica, clock:ClockReading, sent_packets:seq<RslPacket>)
{ LReplicaNextReadClockMaybeNominateValueAndSend2a(replica, replica', clock, sent_packets) }


predicate {:opaque} Q_LReplica_Next_ReadClock_CheckForViewTimeout(replica:LReplica, replica':LReplica, clock:ClockReading, sent_packets:seq<RslPacket>)
{
  LReplicaNextReadClockCheckForViewTimeout(replica, replica', clock, sent_packets)
}

predicate {:opaque} Q_LReplica_Next_ReadClock_CheckForQuorumOfViewSuspicions(replica:LReplica, replica':LReplica, clock:ClockReading, sent_packets:seq<RslPacket>)
{
  LReplicaNextReadClockCheckForQuorumOfViewSuspicions(replica, replica', clock, sent_packets)
}

predicate {:opaque} Q_LReplica_Next_ReadClock_MaybeSendHeartbeat(replica:LReplica, replica':LReplica, clock:ClockReading, sent_packets:seq<RslPacket>)
{
  LReplicaNextReadClockMaybeSendHeartbeat(replica, replica', clock, sent_packets)
}

predicate {:opaque} Q_LReplica_NoReceive_Next(replica:LReplica, nextActionIndex:int, replica':LReplica, ios:seq<RslIo>)
{
  LReplicaNoReceiveNext(replica, nextActionIndex, replica', ios)
}

predicate {:opaque} Q_LReplica_Next_ProcessPacket(replica:LReplica, replica':LReplica, ios:seq<RslIo>)
{
  LReplicaNextProcessPacket(replica, replica', ios)
}

lemma lemma_EstablishQLReplicaNextProcessPacket(replica:LReplica, replica':LReplica, ios:seq<RslIo>)
  requires Q_LReplica_Next_ProcessPacketWithoutReadingClock(replica, replica', ios)
  ensures Q_LReplica_Next_ProcessPacket(replica, replica', ios)
{
  reveal Q_LReplica_Next_ProcessPacketWithoutReadingClock();
  reveal Q_LReplica_Next_ProcessPacket();
}

lemma lemma_EstablishQLReplicaNextProcessPacketFromTimeout(replica:LReplica, replica':LReplica, ios:seq<RslIo>)
  requires |ios|==1
  requires ios[0].LIoOpTimeoutReceive?
  requires replica==replica'
  ensures Q_LReplica_Next_ProcessPacket(replica, replica', ios)
{
  reveal Q_LReplica_Next_ProcessPacket();
}

predicate {:opaque} Q_LScheduler_Next(s:LScheduler, s':LScheduler, ios:seq<RslIo>)
{
  LSchedulerNext(s, s', ios)
}

predicate Establish_Q_LReplica_NoReceive_Next_preconditions(replica:LReplica, replica':LReplica, clock:ClockReading, sent_packets:seq<RslPacket>, nextActionIndex:int, ios:seq<RslIo>)
{
  && SpontaneousIos(ios, 1)
  && sent_packets == ExtractSentPacketsFromIos(ios)
  && clock == SpontaneousClock(ios)
  && (|| (nextActionIndex==3 && Q_LReplica_Next_ReadClock_MaybeNominateValueAndSend2a(replica, replica', clock, sent_packets))
     || (nextActionIndex==7 && Q_LReplica_Next_ReadClock_CheckForViewTimeout(replica, replica', clock, sent_packets))
     || (nextActionIndex==8 && Q_LReplica_Next_ReadClock_CheckForQuorumOfViewSuspicions(replica, replica', clock, sent_packets))
     || (nextActionIndex==9 && Q_LReplica_Next_ReadClock_MaybeSendHeartbeat(replica, replica', clock, sent_packets)))
  && sent_packets == ExtractSentPacketsFromIos(ios)
}

lemma lemma_EstablishQLReplicaNoReceiveNextFromReadClock(replica:LReplica, replica':LReplica, clock:ClockReading, sent_packets:seq<RslPacket>, nextActionIndex:int, ios:seq<RslIo>)
  requires Establish_Q_LReplica_NoReceive_Next_preconditions(replica, replica', clock, sent_packets, nextActionIndex, ios)
  ensures Q_LReplica_NoReceive_Next(replica, nextActionIndex, replica', ios)
{
  reveal Q_LReplica_Next_ReadClock_CheckForViewTimeout();
  reveal Q_LReplica_Next_ReadClock_CheckForQuorumOfViewSuspicions();
  reveal Q_LReplica_Next_ReadClock_MaybeSendHeartbeat();
  reveal Q_LReplica_Next_ReadClock_MaybeNominateValueAndSend2a();
  reveal Q_LReplica_NoReceive_Next();
//  if (nextActionIndex==7)
//  {
//    assert SpontaneousIos(ios, 1);
//    assert LReplicaNextReadClockCheckForViewTimeout(replica, replica', clock, sent_packets);
//    assert LReplicaNoReceiveNext(replica, nextActionIndex, replica', ios);
//  }
//  if (nextActionIndex==8)
//  {
//    assert SpontaneousIos(ios, 1);
//    assert LReplicaNextReadClockCheckForQuorumOfViewSuspicions(replica, replica', clock, sent_packets);
//    assert LReplicaNoReceiveNext(replica, nextActionIndex, replica', ios);
//  }
//  if (nextActionIndex==9)
//  {
//    assert SpontaneousIos(ios, 1);
//    assert LReplicaNextReadClockMaybeSendHeartbeat(replica, replica', clock, sent_packets);
//    assert LReplicaNoReceiveNext(replica, nextActionIndex, replica', ios);
//  }
}

lemma lemma_EstablishQLSchedulerNext(replica:LReplica, replica':LReplica, ios:seq<RslIo>, s:LScheduler, s':LScheduler)
  requires 0<=s.nextActionIndex<=9
  requires 0==s.nextActionIndex    ==> Q_LReplica_Next_ProcessPacket(replica, replica', ios)
  requires 0< s.nextActionIndex<=6 ==> Q_LReplica_NoReceive_Next(replica, s.nextActionIndex, replica', ios)
  requires 6< s.nextActionIndex<=9 ==> Q_LReplica_NoReceive_Next(replica, s.nextActionIndex, replica', ios)
  requires s.replica == replica
  requires s'.replica == replica'
  requires s'.nextActionIndex == (s.nextActionIndex+1)%LReplicaNumActions()
  ensures Q_LScheduler_Next(s, s', ios)
{
  reveal Q_LReplica_Next_ProcessPacket();
  reveal Q_LReplica_NoReceive_Next();
//  if (0==s.nextActionIndex) {
//    assert LReplicaNextProcessPacket(s.replica, s'.replica, ios);
//    assert LSchedulerNext(s, s', ios);
//  } else {
//    if (0< s.nextActionIndex<=6) {
//      assert Q_LReplica_NoReceive_Next(replica, s.nextActionIndex, replica', ios);
//      assert LReplicaNoReceiveNext(replica, s.nextActionIndex, replica', ios);
//      assert LSchedulerNext(s, s', ios);
//    } else if (6< s.nextActionIndex<=9) {
//      assert Q_LReplica_NoReceive_Next(replica, s.nextActionIndex, replica', ios);
//      assert LReplicaNoReceiveNext(replica, s.nextActionIndex, replica', ios);
//      assert LSchedulerNext(s, s', ios);
//    } else {
//      assert false;
//    }
//  }
//  assert LSchedulerNext(s, s', ios);
  reveal Q_LScheduler_Next();
}

} 
