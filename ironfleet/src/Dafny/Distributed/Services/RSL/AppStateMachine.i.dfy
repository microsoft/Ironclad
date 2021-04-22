include "AppStateMachine.s.dfy"


module AppStateMachine_i refines AppStateMachine_s {
type Bytes = seq<byte>
type AppState = map<Bytes, Bytes>

datatype AppMessage' = AppInvalidMessage()
                     | AppGetRequest(key: Bytes)
                     | AppGetFoundReply(value: Bytes)
                     | AppGetUnfoundReply()
                     | AppSetRequest(key: Bytes, value: Bytes)
                     | AppSetSuccessReply()
                     | AppSetFailureReply()
                     | AppDeleteRequest(key: Bytes)
                     | AppDeleteFoundReply()
                     | AppDeleteUnfoundReply()
type AppMessage = AppMessage'

function AppInitialize() : AppState { map [] }

// We have to use RemoveElementFromMap to work around a bug in Dafny
// that crashes it.  That bug manifests when you define a type T with
// type T = map<...> and then subtract a set from something of type T.

function RemoveElementFromMap(m: map<Bytes, Bytes>, s: Bytes) : map<Bytes, Bytes>
{
  m - {s}
}

predicate AppValidRequest(request: AppMessage)
{
  match request
    case AppGetRequest(key)        => |key| <= MaxKeySize()
    case AppSetRequest(key, value) => |key| <= MaxKeySize() && |value| <= MaxValueSize()
    case AppDeleteRequest(key)     => |key| <= MaxKeySize()
    case _                         => false
}

function AppHandleRequest(m: AppState, request: AppMessage) : (AppState, AppMessage)
{
  match request
    case AppGetRequest(key) =>
      (m, if key in m then AppGetFoundReply(m[key]) else AppGetUnfoundReply())

    case AppSetRequest(key, value) =>
      var m' := m[key := value];
      if |m'.Keys| > MaxNumKeys() || |key| > MaxKeySize() || |value| > MaxValueSize() then
        (m, AppSetFailureReply())
      else
        (m', AppSetSuccessReply())

    case AppDeleteRequest(key) =>
      if key in m then
        (RemoveElementFromMap(m, key), AppDeleteFoundReply())
      else
        (m, AppDeleteUnfoundReply())

    case _ =>
      (m, AppInvalidMessage())
}

function method MaxKeySize() : int   { 0x10_0000 } // 1 MB
function method MaxValueSize() : int { 0x800_0000 } // 128 MB
function method MaxNumKeys() : int   { 0x1_0000_0000 } // 2^32

predicate ValidAppMessage(m: AppMessage)
{
  match m
    case AppInvalidMessage() => false
    case AppGetRequest(key) => |key| <= MaxKeySize()
    case AppGetFoundReply(value) => |value| <= MaxValueSize()
    case AppGetUnfoundReply() => true
    case AppSetRequest(key, value) => |key| <= MaxKeySize() && |value| <= MaxValueSize()
    case AppSetSuccessReply() => true
    case AppSetFailureReply() => true
    case AppDeleteRequest(key) => |key| <= MaxKeySize()
    case AppDeleteFoundReply() => true
    case AppDeleteUnfoundReply() => true
}

function MarshallAppMessage(m: AppMessage) : seq<byte>
{
  if ValidAppMessage(m) then
    match m {
      case AppInvalidMessage() =>
        [0, 0, 0, 0, 0, 0, 0, 0]

      case AppGetRequest(key) =>
        [0, 0, 0, 0, 0, 0, 0, 1] + Uint64ToBytes(|key| as uint64) + key

      case AppGetFoundReply(value) =>
        [0, 0, 0, 0, 0, 0, 0, 2] + Uint64ToBytes(|value| as uint64) + value

      case AppGetUnfoundReply() =>
        [0, 0, 0, 0, 0, 0, 0, 3]

      case AppSetRequest(key, value) =>
        [0, 0, 0, 0, 0, 0, 0, 4] + Uint64ToBytes(|key| as uint64) + key + Uint64ToBytes(|value| as uint64) + value
      
      case AppSetSuccessReply() =>
        [0, 0, 0, 0, 0, 0, 0, 5]
      
      case AppSetFailureReply() =>
        [0, 0, 0, 0, 0, 0, 0, 6]
      
      case AppDeleteRequest(key) =>
        [0, 0, 0, 0, 0, 0, 0, 7] + Uint64ToBytes(|key| as uint64) + key

      case AppDeleteFoundReply() =>
        [0, 0, 0, 0, 0, 0, 0, 8]

      case AppDeleteUnfoundReply() =>
        [0, 0, 0, 0, 0, 0, 0, 9]
    }
  else
    [0, 0, 0, 0, 0, 0, 0, 0]
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
