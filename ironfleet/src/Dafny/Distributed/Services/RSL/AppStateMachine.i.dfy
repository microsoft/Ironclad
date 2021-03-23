include "AppStateMachine.s.dfy"

module AppStateMachine_i refines AppStateMachine_s {
type AppState = uint64

datatype AppMessage' = AppIncrementRequest() | AppIncrementReply(response:uint64) | AppInvalidReply()
type AppMessage = AppMessage'

function AppInitialize() : AppState { 0 }

function CappedIncr(v:uint64) : uint64
{
  if (v == 0xffff_ffff_ffff_ffff) then
    v
  else
    v + 1
}

function AppHandleRequest(m:AppState, request:AppMessage) : (AppState, AppMessage)
{
  if request.AppIncrementRequest? then
    (CappedIncr(m), AppIncrementReply(CappedIncr(m)))
  else
    (m, AppInvalidReply())
}

function MarshallAppMessage(m:AppMessage) : seq<byte>
{
  match m {                             // Case                    // Payload
    case AppIncrementRequest =>         [0, 0, 0, 0, 0, 0, 0, 0] 
    case AppIncrementReply(response) => [0, 0, 0, 0, 0, 0, 0, 1] + Uint64ToBytes(response)
    case AppInvalidReply =>             [0, 0, 0, 0, 0, 0, 0, 2] 
  }
}

function Uint64ToBytes(u:uint64) : seq<byte>
{
  [( u/0x1000000_00000000)        as byte,
   ((u/  0x10000_00000000)%0x100) as byte,
   ((u/    0x100_00000000)%0x100) as byte,
   ((u/      0x1_00000000)%0x100) as byte,
   ((u/         0x1000000)%0x100) as byte,
   ((u/           0x10000)%0x100) as byte,
   ((u/             0x100)%0x100) as byte,
   ( u                    %0x100) as byte]
}

}
