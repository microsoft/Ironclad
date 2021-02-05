include "Configuration.i.dfy"
include "Environment.i.dfy"

module LiveRSL__Broadcast_i {
import opened LiveRSL__Configuration_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Message_i
import opened Environment_s

predicate LBroadcastToEveryone(c:LConfiguration, myidx:int, m:RslMessage, sent_packets:seq<RslPacket>)
{
  && |sent_packets| == |c.replica_ids|
  && 0 <= myidx < |c.replica_ids|
  && forall idx {:trigger sent_packets[idx]}{:trigger c.replica_ids[idx]}{:trigger LPacket(c.replica_ids[idx], c.replica_ids[myidx], m)} ::
      0 <= idx < |sent_packets| ==> sent_packets[idx] == LPacket(c.replica_ids[idx], c.replica_ids[myidx], m)
}

} 
