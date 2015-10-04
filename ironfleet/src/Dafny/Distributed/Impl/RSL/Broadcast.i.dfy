include "../../Protocol/RSL/Broadcast.i.dfy"
include "ReplicaConstantsState.i.dfy"

module Impl__LiveRSL__Broadcast_i {
import opened LiveRSL__Broadcast_i
import opened LiveRSL__ReplicaConstantsState_i

method BuildBroadcastToEveryone(config:CPaxosConfiguration, my_index:uint64, msg:CMessage) returns (broadcast:CBroadcast)
    requires CPaxosConfigurationIsValid(config);
    requires ReplicaIndexValid(my_index, config);
    requires CMessageIsAbstractable(msg);
    requires Marshallable(msg);
    ensures CBroadcastIsValid(broadcast);
    ensures OutboundPacketsHasCorrectSrc(Broadcast(broadcast), config.replica_ids[my_index]);
    ensures LBroadcastToEveryone(AbstractifyCPaxosConfigurationToConfiguration(config), int(my_index), AbstractifyCMessageToRslMessage(msg), AbstractifyCBroadcastToRlsPacketSeq(broadcast));
{
    broadcast := CBroadcast(config.replica_ids[my_index], config.replica_ids, msg);
}


} 
