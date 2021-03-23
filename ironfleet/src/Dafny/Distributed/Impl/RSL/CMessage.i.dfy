include "CTypes.i.dfy"

module LiveRSL__CMessage_i {
import opened LiveRSL__CTypes_i
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__AppInterface_i
import opened Logic__Option_i

datatype CMessage =
    CMessage_Invalid()
  | CMessage_Request(seqno:uint64, val:CAppMessage)
  | CMessage_1a(bal_1a:CBallot)
  | CMessage_1b(bal_1b:CBallot, log_truncation_point:COperationNumber, votes:CVotes)
  | CMessage_2a(bal_2a:CBallot, opn_2a:COperationNumber, val_2a:CRequestBatch)
  | CMessage_2b(bal_2b:CBallot, opn_2b:COperationNumber, val_2b:CRequestBatch)
  | CMessage_Heartbeat(bal_heartbeat:CBallot, suspicious:bool, opn_ckpt:COperationNumber)
  | CMessage_Reply(seqno_reply:uint64, reply:CAppMessage)
  | CMessage_AppStateRequest(bal_state_req:CBallot, opn_state_req:COperationNumber)
  | CMessage_AppStateSupply(bal_state_supply:CBallot, opn_state_supply:COperationNumber, app_state:CAppState, reply_cache:CReplyCache)
  | CMessage_StartingPhase2(bal_2:CBallot, logTruncationPoint_2:COperationNumber)

datatype CPacket = CPacket(dst:EndPoint, src:EndPoint, msg:CMessage)

datatype CBroadcast = CBroadcast(src:EndPoint, dsts:seq<EndPoint>, msg:CMessage) | CBroadcastNop

datatype OutboundPackets = Broadcast(broadcast:CBroadcast) | OutboundPacket(p:Option<CPacket>) | PacketSequence(s:seq<CPacket>)

} 
