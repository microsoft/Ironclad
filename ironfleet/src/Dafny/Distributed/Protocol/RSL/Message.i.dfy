include "Types.i.dfy"

module LiveRSL__Message_i {
import opened LiveRSL__Types_i
import opened AppStateMachine_i

// TODO put to/from header in every message

datatype RslMessage =
    RslMessage_Invalid()
  | RslMessage_Request(seqno_req:int, val:AppMessage)
  | RslMessage_1a(bal_1a:Ballot)
  | RslMessage_1b(bal_1b:Ballot, log_truncation_point:OperationNumber, votes:Votes)
  | RslMessage_2a(bal_2a:Ballot, opn_2a:OperationNumber, val_2a:RequestBatch)
  | RslMessage_2b(bal_2b:Ballot, opn_2b:OperationNumber, val_2b:RequestBatch)
  | RslMessage_Heartbeat(bal_heartbeat:Ballot, suspicious:bool, opn_ckpt:OperationNumber)
  | RslMessage_Reply(seqno_reply:int, reply:AppMessage)
  | RslMessage_AppStateRequest(bal_state_req:Ballot, opn_state_req:OperationNumber)
  | RslMessage_AppStateSupply(bal_state_supply:Ballot, opn_state_supply:OperationNumber, app_state:AppState, reply_cache:ReplyCache)
  | RslMessage_StartingPhase2(bal_2:Ballot, logTruncationPoint_2:OperationNumber)

} 
