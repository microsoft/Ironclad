include "../../Common/Collections/Maps.i.dfy"
include "../../Protocol/RSL/Configuration.i.dfy"
include "../../Protocol/RSL/Message.i.dfy"
include "../../Protocol/RSL/Types.i.dfy"
include "../Common/GenericMarshalling.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../../Services/RSL/AppStateMachine.i.dfy"

module LiveRSL__AppInterface_i {
import opened Collections__Maps_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__Message_i
import opened LiveRSL__Types_i
import opened Common__GenericMarshalling_i
import opened Common__NodeIdentity_i
import opened AppStateMachine_i

type CAppState = uint64

datatype CAppMessage = CAppIncrement() | CAppReply(response:uint64) | CAppInvalid()

////////////////////////////////////////////////
//      CAppState
////////////////////////////////////////////////

predicate CAppStateIsAbstractable(appstate:CAppState)
{
    true
}

function AbstractifyCAppStateToAppState(appstate:CAppState) : AppState
    requires CAppStateIsAbstractable(appstate);
{
    appstate
}

function {:opaque} AbstractifyCAppStateSeqToAppStateSeq(s:seq<CAppState>) : seq<AppState>
    requires forall i :: i in s ==> CAppStateIsAbstractable(i);
    ensures |AbstractifyCAppStateSeqToAppStateSeq(s)| == |s|;
    ensures forall i :: 0 <= i < |AbstractifyCAppStateSeqToAppStateSeq(s)| ==> AbstractifyCAppStateSeqToAppStateSeq(s)[i] == AbstractifyCAppStateToAppState(s[i]);
{
    if |s| == 0 then
        []
    else
        [AbstractifyCAppStateToAppState(s[0])] + AbstractifyCAppStateSeqToAppStateSeq(s[1..])
}


/////////////  CAppState parsing and marshalling

function method CAppState_grammar() : G { GUint64 }

function method parse_AppState(val:V) : CAppState
    requires ValInGrammar(val, CAppState_grammar());
    ensures  CAppStateIsAbstractable(parse_AppState(val));
{
    CAppState(val.u)
}

function method AppStateMarshallable(msg:CAppState) : bool
{
    true
}

method MarshallAppState(c:CAppState) returns (val:V)
    requires AppStateMarshallable(c);
    ensures  ValInGrammar(val, CAppState_grammar());
    ensures  ValidVal(val);
    ensures  parse_AppState(val) == c;
{
    val := VUint64(c);
}

function max_app_state_size():int { 0x8000 } // 2^15  // 0xFEFF_FFCF_FFFF_FF00


lemma lemma_AppStateBound(c:CAppState, val:V)
    requires ValInGrammar(val, CAppState_grammar());
    requires ValidVal(val);
    requires parse_AppState(val) == c;
    ensures  SizeOfV(val) < max_app_state_size()
{
}

////////////////////////////////////////////////
//      CAppMessage
////////////////////////////////////////////////

// These trivial definitions are included here, since these functions
// should be part of our interface with the app.  Future apps may have
// more complex requirements

predicate method ValidAppMessage(c:CAppMessage)
{
    true
}

predicate CAppMessageIsAbstractable(c:CAppMessage)
{
    true
}

function AbstractifyCAppMessageToAppMessage(c:CAppMessage) : AppMessage
    requires CAppMessageIsAbstractable(c);
{
    match c {
        case CAppIncrement => AppIncrementRequest()
        case CAppReply(response) => AppIncrementReply(response)
        case CAppInvalid => AppInvalidReply()
    }
}

/////////////  CAppMessage parsing and marshalling

function method CAppMessage_grammar() : G { GTaggedUnion([GTuple([]), GUint64, GTuple([])]) }

function method parse_AppMessage(val:V) : CAppMessage
    requires ValInGrammar(val, CAppMessage_grammar());
{
    if val.c == 0 then
        CAppIncrement()
    else if val.c == 1 then
        assert ValInGrammar(val.val, CAppMessage_grammar().cases[1]);
        CAppReply(val.val.u)
    else
        assert val.c == 2;
        CAppInvalid()
}

method MarshallCAppMessage(c:CAppMessage) returns (val:V)
    requires CAppMessageIsAbstractable(c);
    requires ValidAppMessage(c);
    ensures  ValInGrammar(val, CAppMessage_grammar());
    ensures  ValidVal(val);
    ensures  parse_AppMessage(val) == c;
{
    match c {
        case CAppIncrement       => val := VCase(0, VTuple([]));
        case CAppReply(response) => val := VCase(1, VUint64(response));
        case CAppInvalid         => val := VCase(2, VTuple([]));
    }
}

function method max_val_len() : int { 64 }  //{ 0x100_0000 }    // 2^24


lemma lemma_AppMessageBound(c:CAppMessage, val:V)
    requires ValInGrammar(val, CAppMessage_grammar());
    requires ValidAppMessage(c);
    requires parse_AppMessage(val) == c;
    ensures  ValidVal(val);
    ensures  SizeOfV(val) < max_val_len()   // 0x100_0000; // 2^24
{
    calc ==> {
        true;
            { reveal_SeqSum(); }
        SeqSum([]) == 0;
    }
}


////////////////////////////////////////////////
//     App State Machine 
////////////////////////////////////////////////

method CAppState_Init() returns (s:CAppState)
    ensures CAppStateIsAbstractable(s);
    ensures AbstractifyCAppStateToAppState(s) == AppInitialize();
    ensures AppStateMarshallable(s);
{
    s := 0;
}


method CappedIncrImpl(v:uint64) returns (v':uint64)
    requires 0 <= v <= 0xffff_ffff_ffff_ffff;
    ensures v' == CappedIncr(v)
{
    if (v == 0xffff_ffff_ffff_ffff) {
        v' := v;
    } else {
        v' := v + 1;
    }
}

method HandleAppRequest(appState:CAppState, request:CAppMessage) returns (appState':CAppState, reply:CAppMessage)
    requires CAppStateIsAbstractable(appState);
    requires CAppMessageIsAbstractable(request);
    ensures  CAppStateIsAbstractable(appState');
    ensures  CAppMessageIsAbstractable(reply);
    ensures  AppStateMarshallable(appState');
    ensures  AppHandleRequest(AbstractifyCAppStateToAppState(appState), AbstractifyCAppMessageToAppMessage(request)) == 
                (AbstractifyCAppStateToAppState(appState'), AbstractifyCAppMessageToAppMessage(reply));
{
    if request.CAppIncrement? {
        appState' := CappedIncrImpl(appState);
        reply := CAppReply(appState');
    } else {
        appState' := appState;
        reply := CAppInvalid();
    }
}

}

