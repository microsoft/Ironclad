include "../../Common/Native/Io.s.dfy"

module AppStateMachine_s {
import opened Native__NativeTypes_s
import opened Native__Io_s

type Bytes = seq<byte>
type AppState = Bytes
type AppRequest = Bytes
type AppReply = Bytes

function {:axiom} AppInitialize() : AppState
function {:axiom} AppHandleRequest(m:AppState, request:AppRequest) : (AppState, AppReply)
function method MaxAppRequestSize() : int  { 0x800_0000 }            // 128 MB
function method MaxAppReplySize() : int    { 0x800_0000 }            // 128 MB
function method MaxAppStateSize() : int    { 0x1000_0000_0000_0000 } // 2^60 B

class AppStateMachine
{
  constructor{:axiom} ()
    requires false

  function {:axiom} Abstractify() : AppState

  static method {:axiom} Initialize() returns (m:AppStateMachine)
    ensures fresh(m)
    ensures m.Abstractify() == AppInitialize()

  static method {:axiom} Deserialize(state:AppState) returns (m:AppStateMachine)
    ensures fresh(m)
    ensures m.Abstractify() == state

  method {:axiom} Serialize() returns (state:AppState)
    ensures state == Abstractify()
    ensures |state| <= MaxAppStateSize()

  method {:axiom} HandleRequest(request:AppRequest) returns (reply:AppReply)
    requires |request| <= MaxAppRequestSize()
    ensures  (Abstractify(), reply) == AppHandleRequest(old(Abstractify()), request)
    ensures  |reply| <= MaxAppReplySize()
}

}

