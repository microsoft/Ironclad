include "../../Common/Native/Io.s.dfy"

module Common__NetClient_i {
import opened Native__Io_s

//////////////////////////////////////////////////////////////////////////////
// Things that probably belong in "../../../Common/Native/Io.i.dfy"

function Workaround_CastHostEnvironmentToObject(env:HostEnvironment) : object {env}
function Workaround_CastOkStateToObject(okState:OkState) : object {okState}
function Workaround_CastNowStateToObject(nowState:NowState) : object {nowState}
function Workaround_CastNetStateToObject(netState:NetState) : object {netState}
function Workaround_CastNetClientToObject(netc:NetClient?) : object? {netc}

function HostEnvironmentDefaultFrame(env:HostEnvironment) : set<object>
  reads env
  reads {env.now}
  reads {env.ok}
  reads {env.net}
  reads {env}
{
  {Workaround_CastOkStateToObject(env.ok), Workaround_CastNowStateToObject(env.now), Workaround_CastNetStateToObject(env.net)}
}

function NetClientRepr(netc:NetClient?) : set<object?>
  reads netc
  reads if netc != null then HostEnvironmentDefaultFrame.reads(netc.env) else {}
{
  {Workaround_CastNetClientToObject(netc)} +
  (if netc != null then HostEnvironmentDefaultFrame(netc.env) else {})
}

predicate HostEnvironmentIsValid(env:HostEnvironment)
  reads env
  reads env.Valid.reads()
  reads env.ok.ok.reads()
{
  && env.Valid()
  && env.ok.ok()
}

predicate NetClientOk(netc:NetClient?)
  reads netc
  reads if netc != null then HostEnvironmentDefaultFrame.reads(netc.env) else {}
{
  && netc != null
  && netc.env.ok.ok()
}

function method EndPointIsValidPublicKey(endPoint:EndPoint) : bool
{
  && |endPoint.public_key| < 0x10_0000 // < 1 MB
}

predicate NetClientIsValid(netc:NetClient?)
  reads NetClientRepr(netc)
  reads if netc != null then HostEnvironmentIsValid.reads(netc.env) else {}
{
  && netc != null
  && netc.IsOpen()
  && HostEnvironmentIsValid(netc.env)
  && EndPointIsValidPublicKey(netc.LocalEndPoint())
}

predicate EndPointsAreValidPublicKeys(eps:seq<EndPoint>) 
{
  forall i :: 0 <= i < |eps| ==> EndPointIsValidPublicKey(eps[i])
}


} 
