include "../../Common/Collections/Maps.i.dfy"
include "../../Protocol/RSL/Configuration.i.dfy"
include "../../Protocol/RSL/Message.i.dfy"
include "../../Protocol/RSL/Types.i.dfy"
include "../Common/GenericMarshalling.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../../Services/RSL/AppStateMachine.s.dfy"

module LiveRSL__AppInterface_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Maps_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__Message_i
import opened LiveRSL__Types_i
import opened Common__GenericMarshalling_i
import opened Common__NodeIdentity_i
import opened AppStateMachine_s
import opened Math__mul_nonlinear_i
import opened Math__mul_i

//////////////////////////////////////////////////////////////////////////////
// CAppRequest
//
// Currently, this is just the same as an AppRequest.  Someday, we
// might want it to be something more efficient, like an array.
/////////////////////////////////////////////////////////////////////////////

type CAppRequest = Bytes

predicate method CAppRequestIsAbstractable(request:CAppRequest)
{
  true
}

function method AbstractifyCAppRequestToAppRequest(request:CAppRequest) : AppRequest
{
  request
}

predicate method CAppRequestMarshallable(request:CAppRequest)
{
  |request| <= MaxAppRequestSize()
}

function method MarshallCAppRequest(request:CAppRequest) : V
{
  VByteArray(request)
}

//////////////////////////////////////////////////////////////////////////////
// CAppReply
//
// Currently, this is just the same as an AppReply.  Someday, we
// might want it to be something more efficient, like an array.
/////////////////////////////////////////////////////////////////////////////

type CAppReply = Bytes

predicate method CAppReplyIsAbstractable(reply:CAppReply)
{
  true
}

function method AbstractifyCAppReplyToAppReply(reply:CAppReply) : AppReply
{
  reply
}

predicate method CAppReplyMarshallable(reply:CAppReply)
{
  |reply| <= MaxAppReplySize()
}

function method MarshallCAppReply(reply:CAppReply) : V
{
  VByteArray(reply)
}

//////////////////////////////////////////////////////////////////////////////
// CAppState
//
// Currently, this is just the same as an AppState.  Someday, we
// might want it to be something more efficient, like an array.
/////////////////////////////////////////////////////////////////////////////

type CAppState = Bytes

predicate method CAppStateIsAbstractable(state:CAppState)
{
  true
}

function method AbstractifyCAppStateToAppState(state:CAppState) : AppState
{
  state
}

predicate method CAppStateMarshallable(state:CAppState)
{
  |state| <= MaxAppStateSize()
}

function method MarshallCAppState(state:CAppState) : V
{
  VByteArray(state)
}

}

