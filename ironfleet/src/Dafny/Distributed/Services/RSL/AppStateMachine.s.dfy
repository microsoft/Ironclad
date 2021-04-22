include "../../Common/Native/Io.s.dfy"

abstract module AppStateMachine_s {
import opened Native__NativeTypes_s
import opened Native__Io_s

type AppState
type AppMessage 

function AppInitialize() : AppState
predicate AppValidRequest(request:AppMessage)
function AppHandleRequest(m:AppState, request:AppMessage) : (AppState, AppMessage)

function MarshallAppMessage(m:AppMessage) : seq<byte>
}

