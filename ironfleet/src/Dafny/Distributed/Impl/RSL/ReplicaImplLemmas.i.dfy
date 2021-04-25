include "../../Common/Collections/Seqs.i.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/RSL/Replica.i.dfy"
include "ReplicaModel.i.dfy"
include "UdpRSL.i.dfy"
include "CClockReading.i.dfy"
include "QRelations.i.dfy"

module LiveRSL__ReplicaImplLemmas_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened LiveRSL__CClockReading_i
import opened LiveRSL__ClockReading_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Message_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__QRelations_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ReplicaModel_i
import opened LiveRSL__ReplicaState_i
import opened LiveRSL__UdpRSL_i
import opened Common__NodeIdentity_i
import opened Concrete_NodeIdentity_i
import opened Logic__Option_i
import opened Environment_s

function MapSentPacketToIos(sent_packet:Option<CPacket>) : seq<RslIo>
  requires OutboundPacketsIsValid(OutboundPacket(sent_packet))
{
  match sent_packet {
    case Some(p) => [LIoOpSend(AbstractifyCPacketToRslPacket(p))]
    case None => []
  }
}
    
function {:opaque} MapSentPacketSeqToIos(sent_packets:seq<CPacket>) : seq<RslIo>
  requires OutboundPacketsIsValid(PacketSequence(sent_packets))
  requires OutboundPacketsIsAbstractable(PacketSequence(sent_packets))
  ensures |MapSentPacketSeqToIos(sent_packets)| == |sent_packets|
  ensures forall i :: 0 <= i < |sent_packets| ==> MapSentPacketSeqToIos(sent_packets)[i] == LIoOpSend(AbstractifyCPacketToRslPacket(sent_packets[i]))
{
  //lemma_MapSentPacketSeqToIos(sent_packets);
  if |sent_packets| == 0 then
  []
  else if |sent_packets| == 1 then
    [LIoOpSend(AbstractifyCPacketToRslPacket(sent_packets[0]))]
  else
    [LIoOpSend(AbstractifyCPacketToRslPacket(sent_packets[0]))] + MapSentPacketSeqToIos(sent_packets[1..])
}

lemma {:timeLimitMultiplier 3} lemma_MapSentPacketSeqToIosExtractSentPacketsFromIosEquivalence(sent_packets:OutboundPackets, ios:seq<RslIo>)
  requires sent_packets.PacketSequence?
  requires OutboundPacketsIsValid(sent_packets)
  requires OutboundPacketsIsAbstractable(sent_packets)
  requires ios == MapSentPacketSeqToIos(sent_packets.s)
  requires forall i :: 0 <= i < |sent_packets.s| ==> CPacketIsSendable(sent_packets.s[i])
  ensures AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios)
  decreases |ios|
{
  assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == AbstractifySeqOfCPacketsToSeqOfRslPackets(sent_packets.s);
  reveal ExtractSentPacketsFromIos();
  //assert |AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets)| == |ExtractSentPacketsFromIos(ios)|;
  reveal MapSentPacketSeqToIos();
  if (|ios| == 0) {
    assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
  } else if (|ios| == 1) {
    assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
  } else {
    if (ios[0].LIoOpSend?) {
      var one := ios[0];
      var rest := PacketSequence(sent_packets.s[1..]);
      assert ExtractSentPacketsFromIos(ios) == [ios[0].s] + ExtractSentPacketsFromIos(ios[1..]);
            
      lemma_MapSentPacketSeqToIosExtractSentPacketsFromIosEquivalence(rest, ios[1..]);
      reveal AbstractifySeqOfCPacketsToSeqOfRslPackets();
      assert {:split_here} true;
      calc {
        AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets);
        AbstractifySeqOfCPacketsToSeqOfRslPackets(sent_packets.s);
        [ios[0].s] + AbstractifyOutboundCPacketsToSeqOfRslPackets(rest);
        [ios[0].s] + ExtractSentPacketsFromIos(ios[1..]);
        ExtractSentPacketsFromIos(ios);
      }

    } else {
      assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
    }
    assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
  }
  //forall i | 0 <= i < |AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets)|
  //    ensures AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets)[i] == ExtractSentPacketsFromIos(ios)[i];
  //{
  //}
  assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
}

function {:opaque} BuildBroadcastIos(src:NodeIdentity, dsts:seq<NodeIdentity>, msg:RslMessage) : seq<RslIo>
  ensures |BuildBroadcastIos(src, dsts, msg)| == |dsts|
  ensures forall i :: 0<=i<|dsts| ==> BuildBroadcastIos(src, dsts, msg)[i] == LIoOpSend(LPacket(dsts[i], src, msg))
{
  if |dsts| == 0 then []
  else [ LIoOpSend(LPacket(dsts[0], src, msg)) ] + BuildBroadcastIos(src, dsts[1..], msg)
}

function MapBroadcastToIos(broadcast:CBroadcast) : seq<RslIo>
  requires CBroadcastIsAbstractable(broadcast)
{
  match broadcast
    case CBroadcast(_,_,_) => BuildBroadcastIos(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                                                AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                                                AbstractifyCMessageToRslMessage(broadcast.msg))
    case CBroadcastNop => []
}

predicate LReplica_Next_ReadClockAndProcessPacket_preconditions(ios:seq<RslIo>)
{
  && |ios| >= 1
  && ios[0].LIoOpReceive?
  && ios[0].r.msg.RslMessage_Heartbeat?
}

lemma lemma_MapSentPacketToIosExtractSentPacketsFromIosEquivalence(sent_packet:Option<CPacket>, ios:seq<RslIo>)
  requires OutboundPacketsIsValid(OutboundPacket(sent_packet))
  requires ios == MapSentPacketToIos(sent_packet)
  ensures AbstractifyOutboundCPacketsToSeqOfRslPackets(OutboundPacket(sent_packet)) == ExtractSentPacketsFromIos(ios)
{
  reveal ExtractSentPacketsFromIos();
}

lemma lemma_ExtractSentPacketsFromIos(ios:seq<RslIo>)
  requires AllIosAreSends(ios)
  ensures  |ExtractSentPacketsFromIos(ios)| == |ios|
  ensures  forall i {:auto_trigger} :: 0 <= i < |ios| ==> ExtractSentPacketsFromIos(ios)[i] == ios[i].s
{
  reveal ExtractSentPacketsFromIos();
}

lemma lemma_MapBroadcastToIosExtractSentPacketsFromIosEquivalence(broadcast:CBroadcast, ios:seq<RslIo>)
  requires CBroadcastIsAbstractable(broadcast)
  requires ios == MapBroadcastToIos(broadcast)
  requires AllIosAreSends(ios)
  ensures  AbstractifyCBroadcastToRlsPacketSeq(broadcast) == ExtractSentPacketsFromIos(ios)
{
  reveal ExtractSentPacketsFromIos();

  if broadcast.CBroadcastNop? {

  } else {
    forall i | 0 <= i < |broadcast.dsts|
      ensures AbstractifyCBroadcastToRlsPacketSeq(broadcast)[i] == ExtractSentPacketsFromIos(ios)[i]
    {
      calc {
        AbstractifyCBroadcastToRlsPacketSeq(broadcast)[i];
        BuildLBroadcast(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                        AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                        AbstractifyCMessageToRslMessage(broadcast.msg))[i];
        LPacket(AbstractifyEndPointsToNodeIdentities(broadcast.dsts)[i], 
                AbstractifyEndPointToNodeIdentity(broadcast.src), 
                AbstractifyCMessageToRslMessage(broadcast.msg));

        calc {
          LIoOpSend(LPacket(AbstractifyEndPointsToNodeIdentities(broadcast.dsts)[i], 
                            AbstractifyEndPointToNodeIdentity(broadcast.src),
                            AbstractifyCMessageToRslMessage(broadcast.msg)));
          BuildBroadcastIos(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                            AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                            AbstractifyCMessageToRslMessage(broadcast.msg))[i];
        }
          { lemma_ExtractSentPacketsFromIos(ios); }
        ExtractSentPacketsFromIos(BuildBroadcastIos(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                                                    AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                                                    AbstractifyCMessageToRslMessage(broadcast.msg)))[i];
        ExtractSentPacketsFromIos(ios)[i];
      }
    }

    calc {
      |AbstractifyCBroadcastToRlsPacketSeq(broadcast)|;
      |broadcast.dsts|;
      |ios|;
        { lemma_ExtractSentPacketsFromIos(ios); }
      |ExtractSentPacketsFromIos(ios)|;
    }
  }
}

lemma lemma_UdpEventLogToBroadcast(udpEventLog:seq<UdpEvent>, broadcast:CBroadcast, index:int)
  requires CBroadcastIsValid(broadcast)
  requires broadcast.CBroadcast?
  requires 0 <= index < |udpEventLog|
  requires SendLogReflectsBroadcast(udpEventLog, broadcast)
  ensures  udpEventLog[index].LIoOpSend?
  ensures  UdpPacketIsAbstractable(udpEventLog[index].s)
  ensures  AbstractifyUdpPacketToRslPacket(udpEventLog[index].s) == AbstractifyCBroadcastToRlsPacketSeq(broadcast)[index]
{
  calc ==> {
    true;
    SendLogReflectsBroadcast(udpEventLog, broadcast);
    SendLogReflectsBroadcastPrefix(udpEventLog, broadcast);
    SendLogMatchesRefinement(udpEventLog, broadcast, index);
    udpEventLog[index].LIoOpSend? && UdpPacketIsAbstractable(udpEventLog[index].s)
      && AbstractifyCBroadcastToRlsPacketSeq(broadcast)[index] == AbstractifyUdpPacketToRslPacket(udpEventLog[index].s);
  }
}

lemma lemma_UdpEventLogToBroadcastRefinable(udpEventLog:seq<UdpEvent>, broadcast:CBroadcast)
  requires CBroadcastIsValid(broadcast)
  requires SendLogReflectsBroadcast(udpEventLog, broadcast)
  ensures  UdpEventLogIsAbstractable(udpEventLog)
{
  if broadcast.CBroadcastNop? {
    assert udpEventLog == [];
  } else {
    forall i | 0 <= i < |udpEventLog|
      ensures UdpEventIsAbstractable(udpEventLog[i])
    {
      lemma_UdpEventLogToBroadcast(udpEventLog, broadcast, i);
    }
  }
}

lemma lemma_ExtractSentPacketsFromIosDoesNotMindSomeClutter(ios_head:seq<RslIo>, ios_tail:seq<RslIo>)
  requires forall i :: 0<=i<|ios_head| ==> !ios_head[i].LIoOpSend?
  ensures ExtractSentPacketsFromIos(ios_tail) == ExtractSentPacketsFromIos(ios_head + ios_tail)
{
  if |ios_head| == 0 {
    assert ios_head + ios_tail == ios_tail;
  } else {
    assert !ios_head[0].LIoOpSend?;
    ghost var ios := [ios_head[0]] + ios_head[1..] + ios_tail;
        
    calc {
      ExtractSentPacketsFromIos(ios_head + ios_tail);
        { assert ios_head == [ios_head[0]] + ios_head[1..]; }
      ExtractSentPacketsFromIos([ios_head[0]] + ios_head[1..] + ios_tail);
      ExtractSentPacketsFromIos(ios);
        { assert ios[0] == ios_head[0]; assert ios[1..] == ios_head[1..] + ios_tail;
          reveal ExtractSentPacketsFromIos(); }
      ExtractSentPacketsFromIos(ios_head[1..] + ios_tail);
        { lemma_ExtractSentPacketsFromIosDoesNotMindSomeClutter(ios_head[1..], ios_tail); }
      ExtractSentPacketsFromIos(ios_tail);
    }
  }
}

predicate NoClockMessage(msg:CMessage)
{
  || msg.CMessage_Request?
  || msg.CMessage_1a?
  || msg.CMessage_1b?
  || msg.CMessage_StartingPhase2?
  || msg.CMessage_2a?
  || msg.CMessage_2b?
  || msg.CMessage_Reply?
  || msg.CMessage_AppStateRequest?
  || msg.CMessage_AppStateSupply?
}

lemma lemma_YesWeHaveNoPackets()
  ensures AbstractifyOutboundCPacketsToSeqOfRslPackets(Broadcast(CBroadcastNop)) == []
{
}

lemma {:timeLimitMultiplier 3} lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(
  replica:LReplica, replica':ReplicaState, cpacket:CPacket, sent_packets:OutboundPackets,
  ios:seq<RslIo>, io0:RslIo, ios_head:seq<RslIo>, ios_tail:seq<RslIo>, 
  udpEvent0:UdpEvent, log_head:seq<UdpEvent>, log_tail:seq<UdpEvent>, udpEventLog:seq<UdpEvent>)
  // From Receive:
  requires udpEvent0.LIoOpReceive?
  requires CPacketIsAbstractable(cpacket)
  requires UdpEventIsAbstractable(udpEvent0)
  requires AbstractifyCPacketToRslPacket(cpacket) == AbstractifyUdpPacketToRslPacket(udpEvent0.r)
  requires io0 == LIoOpReceive(AbstractifyUdpPacketToRslPacket(udpEvent0.r))

  // From downcalls:
  requires ReplicaCommonPostconditions(replica, replica', sent_packets)
  requires Establish_Q_LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(replica, AbstractifyReplicaStateToLReplica(replica'), AbstractifyCPacketToRslPacket(cpacket), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios)

  // From DeliverOutboundPackets:
  requires AllIosAreSends(ios_tail)
  requires AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios_tail)
  requires RawIoConsistentWithSpecIO(log_tail, ios_tail)

  requires ios_head == [io0]
  requires log_head == [udpEvent0]
  requires ios == ios_head+ios_tail
  requires udpEventLog == log_head+log_tail
    
//  ensures AllIosAreSends(ios);  // bad idea
  //ensures Establish_Q_LReplica_NoReceive_Next_preconditions(replica, replica', clock, sent_packets, nextActionIndex, ios);
  ensures RawIoConsistentWithSpecIO(udpEventLog, ios)
  ensures Q_LReplica_Next_ProcessPacketWithoutReadingClock(replica, AbstractifyReplicaStateToLReplica(replica'), ios)
  ensures RawIoConsistentWithSpecIO(udpEventLog, ios)
  ensures forall io :: io in ios[1..] ==> io.LIoOpSend?
{
  forall io | io in ios[1..] ensures io.LIoOpSend?
  {
    var idx :| 0<=idx<|ios[1..]| && io==ios[1..][idx];  // because spec uses 'in seq' instead of indexing
    assert io == ios_tail[idx];
    assert AllIosAreSends(ios_tail);
    assert io.LIoOpSend?;
  }

  forall i | 0<=i<|udpEventLog|
    ensures UdpEventIsAbstractable(udpEventLog[i])
    ensures ios[i] == AbstractifyUdpEventToRslIo(udpEventLog[i])
  {
    if (i==0) {
      assert udpEventLog[i]==udpEvent0;
      assert UdpEventIsAbstractable(udpEventLog[i]);
      assert ios[i] == AbstractifyUdpEventToRslIo(udpEventLog[i]);
    } else {
      calc {
        udpEventLog[i];
        ([udpEvent0] + log_tail)[i];
        log_tail[i-1];
      }
      assert udpEventLog[i]==log_tail[i-1];
      assert UdpEventIsAbstractable(udpEventLog[i]);
      assert ios[i] == AbstractifyUdpEventToRslIo(udpEventLog[i]);
    }
  }
  assert UdpEventLogIsAbstractable(udpEventLog);
  assert AbstractifyRawLogToIos(udpEventLog) == ios;

  lemma_ExtractSentPacketsFromIosDoesNotMindSomeClutter(ios_head, ios_tail);

  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica, AbstractifyReplicaStateToLReplica(replica'), AbstractifyCPacketToRslPacket(cpacket), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  assert RawIoConsistentWithSpecIO(udpEventLog, ios);
}
    
lemma lemma_CombineAbstractifyUdpEventToRslIo(ios_head:seq<RslIo>, ios_tail:seq<RslIo>, ios:seq<RslIo>, log_head:seq<UdpEvent>, log_tail:seq<UdpEvent>, log:seq<UdpEvent>)
  requires |log_head| == |ios_head|
  requires forall i :: 0<=i<|log_head|
             ==> UdpEventIsAbstractable(log_head[i]) && ios_head[i] == AbstractifyUdpEventToRslIo(log_head[i])
  requires |log_tail| == |ios_tail|
  requires forall i :: 0<=i<|log_tail|
             ==> UdpEventIsAbstractable(log_tail[i]) && ios_tail[i] == AbstractifyUdpEventToRslIo(log_tail[i])
  requires ios == ios_head+ios_tail
  requires log == log_head+log_tail
  ensures forall i :: 0<=i<|log| ==> ios[i] == AbstractifyUdpEventToRslIo(log[i])
{
}

lemma lemma_UdpEventLogIsAbstractableExtend(log_head:seq<UdpEvent>, log_tail:seq<UdpEvent>, log:seq<UdpEvent>)
  requires log == log_head+log_tail
  requires UdpEventLogIsAbstractable(log_head)
  requires UdpEventLogIsAbstractable(log_tail)
  ensures UdpEventLogIsAbstractable(log)
{
}

lemma lemma_ReplicaNoReceiveReadClockNextHelper(
  replica:LReplica, replica':ReplicaState, clock:CClockReading, sent_packets:OutboundPackets, nextActionIndex:int,
  ios:seq<RslIo>, io0:RslIo, ios_head:seq<RslIo>, ios_tail:seq<RslIo>, 
  udpEvent0:UdpEvent, log_head:seq<UdpEvent>, log_tail:seq<UdpEvent>, udpEventLog:seq<UdpEvent>)
  // From ReadClock:
  requires udpEvent0.LIoOpReadClock?
  requires clock.t as int == udpEvent0.t
  requires UdpEventIsAbstractable(udpEvent0)
  requires io0 == LIoOpReadClock(clock.t as int)

  // From downcalls:
  requires ReplicaCommonPostconditions(replica, replica', sent_packets)
  requires
        var lreplica' := AbstractifyReplicaStateToLReplica(replica');
        var lclock := AbstractifyCClockReadingToClockReading(clock);
        var lsent_packets := AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets);
        && (nextActionIndex == 3 || 7 <= nextActionIndex <= 9)
        && (nextActionIndex==3 ==> Q_LReplica_Next_ReadClock_MaybeNominateValueAndSend2a(replica, lreplica', lclock, lsent_packets))
        && (nextActionIndex==7 ==> Q_LReplica_Next_ReadClock_CheckForViewTimeout(replica, lreplica', lclock, lsent_packets))
        && (nextActionIndex==8 ==> Q_LReplica_Next_ReadClock_CheckForQuorumOfViewSuspicions(replica, lreplica', lclock, lsent_packets))
        && (nextActionIndex==9 ==> Q_LReplica_Next_ReadClock_MaybeSendHeartbeat(replica, lreplica', lclock, lsent_packets))

  // From DeliverOutboundPackets:
  requires AllIosAreSends(ios_tail)
  requires AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios_tail)
  requires RawIoConsistentWithSpecIO(log_tail, ios_tail)

  requires ios_head == [io0]
  requires log_head == [udpEvent0]
  requires ios == ios_head+ios_tail
  requires udpEventLog == log_head+log_tail
    
//  ensures AllIosAreSends(ios);  // bad idea
  //ensures Establish_Q_LReplica_NoReceive_Next_preconditions(replica, replica', clock, sent_packets, nextActionIndex, ios);
  ensures RawIoConsistentWithSpecIO(udpEventLog, ios)
  ensures Q_LReplica_NoReceive_Next(replica, nextActionIndex as int, AbstractifyReplicaStateToLReplica(replica'), ios)
  ensures forall io :: io in ios[1..] ==> io.LIoOpSend?
{
  var lreplica' := AbstractifyReplicaStateToLReplica(replica');
  var lclock := AbstractifyCClockReadingToClockReading(clock);
  var lsent_packets := AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets);

  forall io | io in ios[1..] ensures io.LIoOpSend?
  {
    var idx :| 0<=idx<|ios[1..]| && io==ios[1..][idx];  // because spec uses 'in seq' instead of indexing
    assert io == ios_tail[idx];
    assert AllIosAreSends(ios_tail);
    assert io.LIoOpSend?;
  }
//  forall io | io in ios ensures io.LIoOpSend?
//  {
//    var i :| 0<=i<|ios| && io==ios[i];
//  }
//  assert AllIosAreSends(ios);

  assert io0 == AbstractifyUdpEventToRslIo(udpEvent0);
  forall i | 0<=i<|log_head| ensures UdpEventIsAbstractable(log_head[i]) && ios_head[i] == AbstractifyUdpEventToRslIo(log_head[i])
  {
    assert log_head[i] == udpEvent0;
    assert ios_head[i] == io0;
  }

  lemma_ExtractSentPacketsFromIosDoesNotMindSomeClutter(ios_head, ios_tail);
  assert forall io :: io in ios[1..] ==> io.LIoOpSend?;   // OBSERVE trigger
  ghost var log_head := [udpEvent0];
  lemma_CombineAbstractifyUdpEventToRslIo(ios_head, ios_tail, ios, log_head, log_tail, udpEventLog);

  assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
  lemma_UdpEventLogIsAbstractableExtend(log_head, log_tail, udpEventLog);
  assert UdpEventLogIsAbstractable(udpEventLog);
  lemma_EstablishAbstractifyRawLogToIos(udpEventLog, ios);
  assert AbstractifyRawLogToIos(udpEventLog) == ios;
  assert RawIoConsistentWithSpecIO(udpEventLog, ios);

  assert SpontaneousIos(ios, 1);
  assert AbstractifyCClockReadingToClockReading(clock) == ClockReading(ios[0].t);
  assert AbstractifyCClockReadingToClockReading(clock) == SpontaneousClock(ios);

  lemma_EstablishQLReplicaNoReceiveNextFromReadClock(replica, lreplica', lclock, lsent_packets, nextActionIndex as int, ios);
}

lemma lemma_SingletonSeqPrependSilly<T>(log_head:seq<T>, log_tail:seq<T>, log:seq<T>)
  requires |log_head|==1
  requires log == log_head + log_tail
  ensures log_tail == log[1..]
{
}

} 
