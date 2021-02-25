include "../../Common/Native/Io.s.dfy"

module Common__UdpClient_i {
import opened Native__Io_s

//////////////////////////////////////////////////////////////////////////////
// Things that probably belong in "../../../Common/Native/Io.i.dfy"

function Workaround_CastHostEnvironmentToObject(env:HostEnvironment) : object {env}
function Workaround_CastOkStateToObject(okState:OkState) : object {okState}
function Workaround_CastNowStateToObject(nowState:NowState) : object {nowState}
function Workaround_CastUdpStateToObject(udpState:UdpState) : object {udpState}
function Workaround_CastIPEndPointToObject(ip:IPEndPoint) : object {ip}
function Workaround_CastUdpClientToObject(udpc:UdpClient?) : object? {udpc}

function HostEnvironmentDefaultFrame(env:HostEnvironment) : set<object>
  reads env
  reads {env.now}
  reads {env.ok}
  reads {env.udp}
  reads {env}
{
  {Workaround_CastOkStateToObject(env.ok), Workaround_CastNowStateToObject(env.now), Workaround_CastUdpStateToObject(env.udp)}
}

function UdpClientRepr(udpc:UdpClient?) : set<object?>
  reads udpc
  reads if udpc != null then HostEnvironmentDefaultFrame.reads(udpc.env) else {}
{
  {Workaround_CastUdpClientToObject(udpc)} +
  (if udpc != null then HostEnvironmentDefaultFrame(udpc.env) else {})
}

predicate HostEnvironmentIsValid(env:HostEnvironment)
  reads env
  reads env.Valid.reads()
  reads env.ok.ok.reads()
{
  && env.Valid()
  && env.ok.ok()
}

predicate UdpClientOk(udpc:UdpClient?)
  reads udpc
  reads if udpc != null then HostEnvironmentDefaultFrame.reads(udpc.env) else {}
{
  && udpc != null
  && udpc.env.ok.ok()
}

function method EndPointIsValidIPV4(endPoint:EndPoint) : bool
{
  && |endPoint.addr| == 4
  && 0 <= endPoint.port <= 65535
}

predicate UdpClientIsValid(udpc:UdpClient?)
  reads UdpClientRepr(udpc)
  reads if udpc != null then HostEnvironmentIsValid.reads(udpc.env) else {}
{
  && udpc != null
  && udpc.IsOpen()
  && HostEnvironmentIsValid(udpc.env)
  && EndPointIsValidIPV4(udpc.LocalEndPoint())
}

predicate EndPointsAreValidIPV4(eps:seq<EndPoint>) 
{
  forall i :: 0 <= i < |eps| ==> EndPointIsValidIPV4(eps[i])
}


} 
