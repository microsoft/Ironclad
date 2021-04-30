include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/RSL/Replica.i.dfy"
include "ReplicaModel.i.dfy"
include "ReplicaImplLemmas.i.dfy"
include "ReplicaImplClass.i.dfy"
include "NetRSL.i.dfy"
include "CClockReading.i.dfy"

module LiveRSL__ReplicaImplDelivery_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened LiveRSL__CClockReading_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__Environment_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ReplicaModel_i
import opened LiveRSL__ReplicaImplLemmas_i
import opened LiveRSL__ReplicaImplClass_i
import opened LiveRSL__QRelations_i
import opened LiveRSL__Types_i
import opened LiveRSL__NetRSL_i
import opened Common__NodeIdentity_i
import opened Common__NetClient_i
import opened Common__Util_i
import opened Environment_s

method DeliverPacket(r:ReplicaImpl, packets:OutboundPackets) returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RslIo>)
  requires r.Valid()
  requires packets.OutboundPacket?
  requires OutboundPacketsIsValid(packets)
  requires OutboundPacketsHasCorrectSrc(packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index])
  modifies r.Repr
  ensures r.Repr == old(r.Repr)
  ensures r.netClient != null
  ensures ok == NetClientOk(r.netClient)
  ensures r.Env() == old(r.Env())
  ensures r.replica == old(r.replica)
  ensures ok ==>
          && r.Valid()
          && r.nextActionIndex == old(r.nextActionIndex)
          && AllIosAreSends(ios)
          && AbstractifyOutboundCPacketsToSeqOfRslPackets(packets) == ExtractSentPacketsFromIos(ios)
          && OnlySentMarshallableData(netEventLog)
          && RawIoConsistentWithSpecIO(netEventLog, ios)
          && old(r.Env().net.history()) + netEventLog == r.Env().net.history()
{
  var start_time := Time.GetDebugTimeTicks();
  ok, netEventLog := SendPacket(r.netClient, packets, r.localAddr);
  if (!ok) { return; }

  ios := MapSentPacketToIos(packets.p);
  lemma_MapSentPacketToIosExtractSentPacketsFromIosEquivalence(packets.p, ios);
  var end_time := Time.GetDebugTimeTicks();
  if packets.p.None? {
    RecordTimingSeq("DeliverPacketEmpty", start_time, end_time);
  } else {
    RecordTimingSeq("DeliverPacketSingleton", start_time, end_time);
  } 
}

method {:timeLimitMultiplier 2} DeliverPacketSequence(r:ReplicaImpl, packets:OutboundPackets) returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RslIo>)
  requires r.Valid()
  requires packets.PacketSequence?
  requires OutboundPacketsIsValid(packets)
  requires OutboundPacketsIsAbstractable(packets)
  requires OutboundPacketsHasCorrectSrc(packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index])
  modifies r.Repr
  ensures r.Repr == old(r.Repr)
  ensures r.netClient != null
  ensures ok == NetClientOk(r.netClient)
  ensures r.Env() == old(r.Env())
  ensures r.replica == old(r.replica)
  ensures ok ==>
          && r.Valid()
          && r.nextActionIndex == old(r.nextActionIndex)
          && AllIosAreSends(ios)
          && AbstractifyOutboundCPacketsToSeqOfRslPackets(packets) == ExtractSentPacketsFromIos(ios)
          && OnlySentMarshallableData(netEventLog)
          && RawIoConsistentWithSpecIO(netEventLog, ios)
          && old(r.Env().net.history()) + netEventLog == r.Env().net.history()
{
  var start_time := Time.GetDebugTimeTicks();
  ok, netEventLog := SendPacketSequence(r.netClient, packets, r.localAddr);
  if (!ok) { return; }

  ios := MapSentPacketSeqToIos(packets.s);
  lemma_MapSentPacketSeqToIosExtractSentPacketsFromIosEquivalence(packets, ios);
  var end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("DeliverPacketSequence", start_time, end_time);
}

method{:timeLimitMultiplier 2} DeliverBroadcast(r:ReplicaImpl, broadcast:CBroadcast) returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RslIo>)
  requires r.Valid()
  requires CBroadcastIsValid(broadcast)
  requires broadcast.CBroadcast? ==> broadcast.src == r.replica.constants.all.config.replica_ids[r.replica.constants.my_index];
  modifies r.Repr
  ensures r.Repr == old(r.Repr)
  ensures r.netClient != null
  ensures ok == NetClientOk(r.netClient)
  ensures r.Env() == old(r.Env())
  ensures r.replica == old(r.replica)
  ensures ok ==>
          && r.Valid()
          && r.nextActionIndex == old(r.nextActionIndex)
          && AllIosAreSends(ios)
          && AbstractifyCBroadcastToRlsPacketSeq(broadcast) == ExtractSentPacketsFromIos(ios)
          && OnlySentMarshallableData(netEventLog)
          && RawIoConsistentWithSpecIO(netEventLog, ios)
          && old(r.Env().net.history()) + netEventLog == r.Env().net.history()
{
  var start_time := Time.GetDebugTimeTicks();
  ok, netEventLog := SendBroadcast(r.netClient, broadcast, r.localAddr);
  if (!ok) { return; }

  ios := MapBroadcastToIos(broadcast);
  lemma_MapBroadcastToIosExtractSentPacketsFromIosEquivalence(broadcast, ios);
    
  lemma_NetEventLogToBroadcastRefinable(netEventLog, broadcast);
  assert NetEventLogIsAbstractable(netEventLog);
  if broadcast.CBroadcastNop? {
    assert RawIoConsistentWithSpecIO(netEventLog, ios);
  } else {
    ghost var broadcast_ios := BuildBroadcastIos(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                                                 AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                                                 AbstractifyCMessageToRslMessage(broadcast.msg));
    calc {
      AbstractifyRawLogToIos(netEventLog);
      {
        forall i | 0 <= i < |AbstractifyRawLogToIos(netEventLog)|
          ensures AbstractifyRawLogToIos(netEventLog)[i] == 
                    LIoOpSend(LPacket(AbstractifyEndPointsToNodeIdentities(broadcast.dsts)[i], 
                                      AbstractifyEndPointToNodeIdentity(broadcast.src), 
                                      AbstractifyCMessageToRslMessage(broadcast.msg)))
        {
          calc {
            AbstractifyRawLogToIos(netEventLog)[i];
            AbstractifyNetEventToRslIo(netEventLog[i]);
              { lemma_NetEventLogToBroadcast(netEventLog, broadcast, i); }
            LIoOpSend(AbstractifyCBroadcastToRlsPacketSeq(broadcast)[i]);
            LIoOpSend(BuildLBroadcast(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                                      AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                                      AbstractifyCMessageToRslMessage(broadcast.msg))[i]);
            LIoOpSend(LPacket(AbstractifyEndPointsToNodeIdentities(broadcast.dsts)[i], 
                              AbstractifyEndPointToNodeIdentity(broadcast.src), 
                              AbstractifyCMessageToRslMessage(broadcast.msg)));
          }
        }
        forall i | 0 <= i < |broadcast_ios|
          ensures broadcast_ios[i] == LIoOpSend(LPacket(AbstractifyEndPointsToNodeIdentities(broadcast.dsts)[i], 
                                                        AbstractifyEndPointToNodeIdentity(broadcast.src), 
                                                        AbstractifyCMessageToRslMessage(broadcast.msg)))
        {
          calc {
            LIoOpSend(LPacket(AbstractifyEndPointsToNodeIdentities(broadcast.dsts)[i], 
                              AbstractifyEndPointToNodeIdentity(broadcast.src), 
                              AbstractifyCMessageToRslMessage(broadcast.msg)));
            BuildBroadcastIos(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                              AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                              AbstractifyCMessageToRslMessage(broadcast.msg))[i];
            broadcast_ios[i];
          }
          }
      }
      broadcast_ios;
      BuildBroadcastIos(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                        AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                        AbstractifyCMessageToRslMessage(broadcast.msg));
      MapBroadcastToIos(broadcast);
      ios;
    }
    assert RawIoConsistentWithSpecIO(netEventLog, ios);
  }

  var end_time := Time.GetDebugTimeTicks();
  if broadcast.CBroadcastNop? || (broadcast.CBroadcast? && |broadcast.dsts| as uint64 == 0) {
    RecordTimingSeq("DeliverBroadcastEmpty", start_time, end_time);
  } else if broadcast.CBroadcast? && |broadcast.dsts| as uint64 == 1 {
    RecordTimingSeq("DeliverBroadcastSingleton", start_time, end_time);
  } else {
    RecordTimingSeq("DeliverBroadcastMany", start_time, end_time);
  }
}

method DeliverOutboundPackets(r:ReplicaImpl, packets:OutboundPackets) returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RslIo>)
  requires r.Valid()
  requires OutboundPacketsIsValid(packets)
  requires OutboundPacketsIsAbstractable(packets)
  requires OutboundPacketsHasCorrectSrc(packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);
  modifies r.Repr
  ensures r.Repr == old(r.Repr)
  ensures r.netClient != null
  ensures ok == NetClientOk(r.netClient)
  ensures r.Env() == old(r.Env())
  ensures r.replica == old(r.replica)
  ensures ok ==>
            &&  r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && AllIosAreSends(ios)
            && AbstractifyOutboundCPacketsToSeqOfRslPackets(packets) == ExtractSentPacketsFromIos(ios)
            && OnlySentMarshallableData(netEventLog)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && old(r.Env().net.history()) + netEventLog == r.Env().net.history()
{
  match packets {
    case Broadcast(broadcast) => ok, netEventLog, ios := DeliverBroadcast(r, broadcast);
    case OutboundPacket(p) => ok, netEventLog, ios := DeliverPacket(r, packets);
    case PacketSequence(s) => ok, netEventLog, ios := DeliverPacketSequence(r, packets);
  }
}

}
