include "../../Common/Collections/Maps.i.dfy"
include "../../Protocol/RSL/Configuration.i.dfy"
include "../../Protocol/RSL/Message.i.dfy"
include "../../Protocol/RSL/Types.i.dfy"
include "../Common/GenericMarshalling.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../../Services/RSL/AppStateMachine.i.dfy"

module LiveRSL__AppInterface_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Maps_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__Message_i
import opened LiveRSL__Types_i
import opened Common__GenericMarshalling_i
import opened Common__NodeIdentity_i
import opened AppStateMachine_i
import opened Math__mul_nonlinear_i
import opened Math__mul_i

////////////////////////////////////////////////
//      CAppMessage
////////////////////////////////////////////////

datatype CAppMessage = CAppInvalid()
                     | CAppGetRequest(key: Bytes)
                     | CAppGetFoundReply(value: Bytes)
                     | CAppGetUnfoundReply()
                     | CAppSetRequest(key: Bytes, value: Bytes)
                     | CAppSetSuccessReply()
                     | CAppSetFailureReply()
                     | CAppDeleteRequest(key: Bytes)
                     | CAppDeleteFoundReply()
                     | CAppDeleteUnfoundReply()

// This trivial definition is included here, since it should be part
// of our interface with the app.  Future apps may have more complex
// requirements for abstractability.

predicate CAppMessageIsAbstractable(c:CAppMessage)
{
  true
}

predicate method ValidCAppRequest(c:CAppMessage)
{
  match c
    case CAppGetRequest(key)        => |key| <= MaxKeySize()
    case CAppSetRequest(key, value) => |key| <= MaxKeySize() && |value| <= MaxValueSize()
    case CAppDeleteRequest(key)     => |key| <= MaxKeySize()
    case _                          => false
}

predicate method ValidCAppMessage(c:CAppMessage)
{
  match c
    case CAppInvalid()              => true
    case CAppGetRequest(key)        => |key| <= MaxKeySize()
    case CAppGetFoundReply(value)   => |value| <= MaxValueSize()
    case CAppGetUnfoundReply()      => true
    case CAppSetRequest(key, value) => |key| <= MaxKeySize() && |value| <= MaxValueSize()
    case CAppSetSuccessReply()      => true
    case CAppSetFailureReply()      => true
    case CAppDeleteRequest(key)     => |key| <= MaxKeySize()
    case CAppDeleteFoundReply()     => true
    case CAppDeleteUnfoundReply()   => true
}

function AbstractifyCAppMessageToAppMessage(c:CAppMessage) : AppMessage
  requires CAppMessageIsAbstractable(c)
{
  match c {
    case CAppInvalid() => AppInvalidMessage()
    case CAppGetRequest(key) => AppGetRequest(key)
    case CAppGetFoundReply(value) => AppGetFoundReply(value)
    case CAppGetUnfoundReply() => AppGetUnfoundReply()
    case CAppSetRequest(key, value) => AppSetRequest(key, value)
    case CAppSetSuccessReply() => AppSetSuccessReply()
    case CAppSetFailureReply() => AppSetFailureReply()
    case CAppDeleteRequest(key) => AppDeleteRequest(key)
    case CAppDeleteFoundReply() => AppDeleteFoundReply()
    case CAppDeleteUnfoundReply() => AppDeleteUnfoundReply()
  }
}

/////////////  CAppMessage parsing and marshalling

function method CAppMessage_grammar() : G { GTaggedUnion([
  GTuple([]),                       // CAppInvalid
  GByteArray,                       // CAppGetRequest
  GByteArray,                       // CAppGetFoundReply
  GTuple([]),                       // CAppGetUnfoundReply
  GTuple([GByteArray, GByteArray]), // CAppSetRequest
  GTuple([]),                       // CAppSetSuccessReply
  GTuple([]),                       // CAppSetFailureReply
  GByteArray,                       // CAppDeleteRequest
  GTuple([]),                       // CAppDeleteFoundReply
  GTuple([])                        // CAppDeleteUnfoundReply
]) }

function method parse_AppMessage(val:V) : CAppMessage
  requires ValInGrammar(val, CAppMessage_grammar())
{
  if val.c == 0 then
    CAppInvalid()
  else if val.c == 1 then
    assert ValInGrammar(val.val, CAppMessage_grammar().cases[1]);
    CAppGetRequest(val.val.b)
  else if val.c == 2 then
    assert ValInGrammar(val.val, CAppMessage_grammar().cases[2]);
    CAppGetFoundReply(val.val.b)
  else if val.c == 3 then
    assert ValInGrammar(val.val, CAppMessage_grammar().cases[3]);
    CAppGetUnfoundReply()
  else if val.c == 4 then
    assert ValInGrammar(val.val, CAppMessage_grammar().cases[4]);
    CAppSetRequest(val.val.t[0].b, val.val.t[1].b)
  else if val.c == 5 then
    assert ValInGrammar(val.val, CAppMessage_grammar().cases[5]);
    CAppSetSuccessReply()
  else if val.c == 6 then
    assert ValInGrammar(val.val, CAppMessage_grammar().cases[6]);
    CAppSetFailureReply()
  else if val.c == 7 then
    assert ValInGrammar(val.val, CAppMessage_grammar().cases[7]);
    CAppDeleteRequest(val.val.b)
  else if val.c == 8 then
    assert ValInGrammar(val.val, CAppMessage_grammar().cases[8]);
    CAppDeleteFoundReply()
  else if val.c == 9 then
    assert ValInGrammar(val.val, CAppMessage_grammar().cases[9]);
    CAppDeleteUnfoundReply()
  else
    CAppInvalid()
}

method MarshallCAppMessage(c:CAppMessage) returns (val:V)
  requires CAppMessageIsAbstractable(c)
  requires ValidCAppMessage(c)
  ensures  ValInGrammar(val, CAppMessage_grammar())
  ensures  ValidVal(val)
  ensures  parse_AppMessage(val) == c
{
  match c {
    case CAppInvalid()              => val := VCase(0, VTuple([]));
    case CAppGetRequest(key)        => val := VCase(1, VByteArray(key));
    case CAppGetFoundReply(value)   => val := VCase(2, VByteArray(value));
    case CAppGetUnfoundReply()      => val := VCase(3, VTuple([]));

    case CAppSetRequest(key, value) =>
      val := VCase(4, VTuple([VByteArray(key), VByteArray(value)]));
      ghost var g := CAppMessage_grammar();
      assert |val.val.t| == 2 == |g.cases[4].t|;
      forall i | 0 <= i < |val.val.t|
        ensures ValInGrammar(val.val.t[i], g.cases[4].t[i])
        ensures ValidVal(val.val.t[i])
      {
        if i == 0 { } else if i == 1 { } else { assert false; }
      }

    case CAppSetSuccessReply()      => val := VCase(5, VTuple([]));
    case CAppSetFailureReply()      => val := VCase(6, VTuple([]));
    case CAppDeleteRequest(key)     => val := VCase(7, VByteArray(key));
    case CAppDeleteFoundReply()     => val := VCase(8, VTuple([]));
    case CAppDeleteUnfoundReply()   => val := VCase(9, VTuple([]));
  }
}

function method max_val_len() : int { MaxKeySize() + MaxValueSize() + 25 }

lemma lemma_AppMessageBound(c:CAppMessage, val:V)
  requires ValInGrammar(val, CAppMessage_grammar())
  requires ValidCAppMessage(c)
  requires parse_AppMessage(val) == c
  ensures  ValidVal(val)
  ensures  SizeOfV(val) < max_val_len()
{
  assert SeqSum([]) == 0 by { reveal SeqSum(); }

  match c {
    case CAppInvalid() =>
      assert SizeOfV(val) == 8;

    case CAppGetRequest(key) =>
      assert SizeOfV(val) <= 16 + MaxKeySize();
      
    case CAppGetFoundReply(value) =>
      assert SizeOfV(val) <= 16 + MaxValueSize();

    case CAppGetUnfoundReply() =>
      assert SizeOfV(val) == 8;

    case CAppSetRequest(key, value) =>
      ghost var g := CAppMessage_grammar();
      assert ValInGrammar(val.val, g.cases[4]);
      assert |val.val.t| == |g.cases[4].t| == 2;
      assert val.val.t[0].b == key;
      assert val.val.t[1].b == value;
      assert val.val.t[2..] == [];
      assert forall v :: v in val.val.t ==> ValidVal(v);
      calc {
        SizeOfV(val);
        8 + SizeOfV(val.val);
        8 + SeqSum(val.val.t);
          { reveal SeqSum(); }
        8 + (SizeOfV(val.val.t[0]) + SeqSum(val.val.t[1..]));
          { reveal SeqSum(); }
        8 + (SizeOfV(val.val.t[0]) + (SizeOfV(val.val.t[1]) + SeqSum(val.val.t[2..])));
        8 + SizeOfV(val.val.t[0]) + SizeOfV(val.val.t[1]);
        <= { assert |val.val.t[0].b| <= MaxKeySize(); }
          8 + (8 + MaxKeySize()) + SizeOfV(val.val.t[1]);
        <= { assert |val.val.t[1].b| <= MaxValueSize(); }
          8 + (8 + MaxKeySize()) + (8 + MaxValueSize());
        MaxKeySize() + MaxValueSize() + 24;
      }

    case CAppSetSuccessReply() =>
      assert SizeOfV(val) == 8;

    case CAppSetFailureReply() =>
      assert SizeOfV(val) == 8;

    case CAppDeleteRequest(key) =>
      assert SizeOfV(val) <= 16 + MaxKeySize();

    case CAppDeleteFoundReply() =>
      assert SizeOfV(val) == 8;

    case CAppDeleteUnfoundReply() =>
      assert SizeOfV(val) == 8;
  }
}

////////////////////////////////////////////////
//     CAppState (App State Machine)
////////////////////////////////////////////////

type CAppState = MutableMap<Bytes, Bytes>

predicate CAppStateIsAbstractable(appstate: CAppState)
{
  true
}

function AbstractifyCAppStateToAppState(appstate: CAppState) : AppState
  reads appstate
  requires CAppStateIsAbstractable(appstate)
{
  MutableMap.MapOf(appstate)
}

predicate AppStateMarshallable(c:CAppState)
  reads c
{
  var m := MutableMap.MapOf(c);
  && |m.Keys| <= MaxNumKeys()
  && (forall k :: k in m.Keys ==> |k| <= MaxKeySize() && |m[k]| <= MaxValueSize())
}

method CAppState_Init() returns (s:CAppState)
  ensures CAppStateIsAbstractable(s)
  ensures AbstractifyCAppStateToAppState(s) == AppInitialize()
  ensures AppStateMarshallable(s)
{
  s := MutableMap.EmptyMap();
}

method HandleAppGetRequest(appState:CAppState, key:Bytes) returns (reply:CAppMessage)
  requires CAppStateIsAbstractable(appState)
  requires AppStateMarshallable(appState)
  ensures  CAppMessageIsAbstractable(reply)
  ensures  AppHandleRequest(AbstractifyCAppStateToAppState(appState), AbstractifyCAppMessageToAppMessage(CAppGetRequest(key))) ==
             (AbstractifyCAppStateToAppState(appState), AbstractifyCAppMessageToAppMessage(reply))
  ensures  ValidCAppMessage(reply)
{
  var contains, value := appState.TryGetValue(key);
  if !contains {
    reply := CAppGetUnfoundReply();
  }
  else {
    reply := CAppGetFoundReply(value);
  }
}

method HandleAppSetRequest(appState:CAppState, key:Bytes, value:Bytes) returns (reply:CAppMessage)
  modifies appState
  requires CAppStateIsAbstractable(appState)
  requires AppStateMarshallable(appState)
  ensures  CAppStateIsAbstractable(appState)
  ensures  CAppMessageIsAbstractable(reply)
  ensures  AppStateMarshallable(appState)
  ensures  AppHandleRequest(old(AbstractifyCAppStateToAppState(appState)), AbstractifyCAppMessageToAppMessage(CAppSetRequest(key, value)))
             == (AbstractifyCAppStateToAppState(appState), AbstractifyCAppMessageToAppMessage(reply))
  ensures  ValidCAppMessage(reply)
{
  if |key| > MaxKeySize() {
    reply := CAppSetFailureReply();
    return;
  }

  if |value| > MaxValueSize() {
    reply := CAppSetFailureReply();
    return;
  }
  
  var sz := appState.Size();
  assert sz <= MaxNumKeys();

  // If the maximum number of keys has already been reached and we're supposed to
  // set a key that isn't present, then do nothing but return a failure reply,
  // so that we don't exceed the maximum number of keys allowed.  This behavior
  // is what the spec specifies.

  if sz == MaxNumKeys() {
    var contains := appState.Contains(key);
    if !contains {
      reply := CAppSetFailureReply();
      return;
    }
  }

  appState.Set(key, value);
  reply := CAppSetSuccessReply();
}

method HandleAppDeleteRequest(appState:CAppState, key:Bytes) returns (reply:CAppMessage)
  modifies appState
  requires CAppStateIsAbstractable(appState)
  requires AppStateMarshallable(appState)
  ensures  CAppStateIsAbstractable(appState)
  ensures  CAppMessageIsAbstractable(reply)
  ensures  AppStateMarshallable(appState)
  ensures  AppHandleRequest(old(AbstractifyCAppStateToAppState(appState)), AbstractifyCAppMessageToAppMessage(CAppDeleteRequest(key))) ==
             (AbstractifyCAppStateToAppState(appState), AbstractifyCAppMessageToAppMessage(reply))
  ensures  ValidCAppMessage(reply)
{
  var contains := appState.Contains(key);
  if contains {
    appState.Remove(key);
    reply := CAppDeleteFoundReply();
  }
  else {
    reply := CAppDeleteUnfoundReply();
  }
}

method HandleAppRequest(appState:CAppState, request:CAppMessage) returns (reply:CAppMessage)
  modifies appState
  requires CAppStateIsAbstractable(appState)
  requires CAppMessageIsAbstractable(request)
  requires AppStateMarshallable(appState)
  ensures  CAppStateIsAbstractable(appState)
  ensures  CAppMessageIsAbstractable(reply)
  ensures  AppStateMarshallable(appState)
  ensures  AppHandleRequest(old(AbstractifyCAppStateToAppState(appState)), AbstractifyCAppMessageToAppMessage(request)) ==
             (AbstractifyCAppStateToAppState(appState), AbstractifyCAppMessageToAppMessage(reply))
  ensures  ValidCAppMessage(reply)
{
  match request {
    case CAppGetRequest(key) =>
      reply := HandleAppGetRequest(appState, key);

    case CAppSetRequest(key, value) =>
      reply := HandleAppSetRequest(appState, key, value);

    case CAppDeleteRequest(key) =>
      reply := HandleAppDeleteRequest(appState, key);

    case _ =>
      reply := CAppInvalid();
  }
}

////////////////////////////////////////////////
//      CTransferableAppState
////////////////////////////////////////////////

type CTransferableAppState = seq<(Bytes, Bytes)>

predicate CTransferableAppStateIsAbstractable(appstate: CTransferableAppState)
{
  true
}

function AbstractifyCTransferableAppStateToAppState(appstate: CTransferableAppState) : AppState
  requires CTransferableAppStateIsAbstractable(appstate)
{
  KVTupleSeqToMap(appstate)
}

/////////////  CTransferableAppState parsing and marshalling

function method CTransferableAppState_grammar() : G
{
  GArray(GTuple([GByteArray, GByteArray]))
}

function method parse_KVTuple(val: V) : (Bytes, Bytes)
  requires ValInGrammar(val, GTuple([GByteArray, GByteArray]))
{
  ghost var g := GTuple([GByteArray, GByteArray]);
  assert ValInGrammar(val.t[0], g.t[0]);
  assert ValInGrammar(val.t[1], g.t[1]);
  (val.t[0].b, val.t[1].b)
}

function method parse_KVTupleSeq(vals: seq<V>) : (result: seq<(Bytes, Bytes)>)
  requires forall val :: val in vals ==> ValInGrammar(val, GTuple([GByteArray, GByteArray]))
  ensures  |result| == |vals|
  ensures  forall i :: 0 <= i < |vals| ==> result[i] == parse_KVTuple(vals[i])
{
  if |vals| == 0 then
    []
  else
    [parse_KVTuple(vals[0])] + parse_KVTupleSeq(vals[1..])
}

function method parse_TransferableAppState(val:V) : CTransferableAppState
  requires ValInGrammar(val, CTransferableAppState_grammar())
  ensures  CTransferableAppStateIsAbstractable(parse_TransferableAppState(val))
{
  parse_KVTupleSeq(val.a)
}

function method TransferableAppStateMarshallable(c:CTransferableAppState) : bool
{
  && |c| <= MaxNumKeys()
  && (forall kv :: kv in c ==> |kv.0| <= MaxKeySize() && |kv.1| <= MaxValueSize())
}

function max_transferable_app_state_size():int { 0x1000_0000_0000_0000 } // 2^60

lemma lemma_SeqSumMultiply(vals: seq<V>, bound: int)
  requires forall val :: val in vals ==> SizeOfV(val) <= bound
  ensures SeqSum(vals) <= bound * |vals|
{
  reveal SeqSum();
  if |vals| == 0 {
    return;
  }
  lemma_SeqSumMultiply(vals[1..], bound);
  calc {
    SeqSum(vals);
    SizeOfV(vals[0]) + SeqSum(vals[1..]);
    <= bound + SeqSum(vals[1..]);
    <= bound + bound * |vals[1..]|;
    bound + bound * (|vals| - 1);
    bound * 1 + bound * (|vals| - 1);
      { lemma_mul_is_distributive_add(bound, 1, |vals| - 1); }
     bound * (1 + (|vals| - 1));
     bound * |vals|;
  }
}

lemma lemma_TransferableAppStateBound(c:CTransferableAppState, val:V)
  requires ValInGrammar(val, CTransferableAppState_grammar())
  requires ValidVal(val)
  requires parse_TransferableAppState(val) == c
  requires TransferableAppStateMarshallable(c)
  ensures  SizeOfV(val) < max_transferable_app_state_size()
{
  var bound := MaxKeySize() + MaxValueSize() + 16;

  forall v | v in val.a
    ensures SizeOfV(v) <= bound
  {
    assert ValInGrammar(v, GTuple([GByteArray, GByteArray]));
    assert |v.t| == 2;
    assert |v.t[0].b| <= MaxKeySize();
    assert |v.t[1].b| <= MaxValueSize();
    reveal SeqSum();
    calc {
      SizeOfV(v);
      SeqSum(v.t);
      SizeOfV(v.t[0]) + (SizeOfV(v.t[1]) + SeqSum(v.t[1+1..]));
      SizeOfV(v.t[0]) + SizeOfV(v.t[1]);
      <= (8 + MaxKeySize()) + SizeOfV(v.t[1]);
      <= (8 + MaxKeySize()) + (8 + MaxValueSize());
      MaxKeySize() + MaxValueSize() + 16;
      bound;
    }
  }

  calc {
    SizeOfV(val);
    8 + SeqSum(val.a);
    <= { lemma_SeqSumMultiply(val.a, bound); }
      8 + bound * |val.a|;
    <= { lemma_mul_is_commutative(bound, |val.a|);
        lemma_mul_is_commutative(bound, MaxNumKeys());
        lemma_mul_inequality(|val.a|, MaxNumKeys(), bound); }
      8 + bound * MaxNumKeys();
    < max_transferable_app_state_size();
  }
}

method MarshallTransferableAppState(c:CTransferableAppState) returns (val:V)
  requires TransferableAppStateMarshallable(c)
  ensures  ValInGrammar(val, CTransferableAppState_grammar())
  ensures  ValidVal(val)
  ensures  parse_TransferableAppState(val) == c
{
  var kvs: seq<V> := [];
  var i: int := 0;
  while i < |c|
    invariant 0 <= i <= |c|
    invariant |kvs| == i
    invariant ValInGrammar(VArray(kvs), CTransferableAppState_grammar())
    invariant forall v :: v in kvs ==> ValidVal(v)
    invariant ValidVal(VArray(kvs))
    invariant parse_TransferableAppState(VArray(kvs)) == c[..i]
  {
    var (k, v) := c[i];
    var k' := VByteArray(k);
    var v' := VByteArray(v);
    var kv' := VTuple([k', v']);
    assert ValidVal(kv');
    assert ValInGrammar(kv', GTuple([GByteArray, GByteArray]));
    kvs := kvs + [kv'];
    i := i + 1;
  }

  val := VArray(kvs);
}

}

