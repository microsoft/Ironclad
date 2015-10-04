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
function Workaround_CastUdpClientToObject(udpc:UdpClient) : object {udpc}

function HostEnvironmentDefaultFrame(env:HostEnvironment) : set<object>
    reads env;
    reads if env != null then {env.now} else {};
    reads if env != null then {env.ok} else {};
    reads if env != null then {env.udp} else {};
    reads if env != null then {env} else {};
{
    (if env != null then
        {Workaround_CastOkStateToObject(env.ok), Workaround_CastNowStateToObject(env.now), Workaround_CastUdpStateToObject(env.udp)}
    else
        {})
}

function UdpClientRepr(udpc:UdpClient) : set<object>
    reads udpc;
    reads if udpc != null then HostEnvironmentDefaultFrame.reads(udpc.env) else {};
{
      {Workaround_CastUdpClientToObject(udpc)}
    + (if udpc != null then HostEnvironmentDefaultFrame(udpc.env) else {})
}

predicate HostEnvironmentIsValid(env:HostEnvironment)
    reads env;
    reads if env != null then env.Valid.reads() else {};
    reads if env != null && env.ok != null then env.ok.ok.reads() else {};
{
       env != null
    && env.Valid()
    && env.constants != null
    && env.now != null
    && env.ok != null
    && env.ok.ok()
    && env.udp != null
}

predicate UdpClientOk(udpc:UdpClient)
    reads udpc;
    reads if udpc != null then HostEnvironmentDefaultFrame.reads(udpc.env) else {};
{
       udpc != null
    && udpc.env != null
    && udpc.env.ok != null
    && udpc.env.ok.ok()
}

function method EndPointIsValidIPV4(endPoint:EndPoint) : bool
{
       |endPoint.addr| == 4
    && 0 <= endPoint.port <= 65535
}

predicate UdpClientIsValid(udpc:UdpClient)
    reads UdpClientRepr(udpc);
    reads if udpc != null then HostEnvironmentIsValid.reads(udpc.env) else {};
{
       udpc != null
    && udpc.env != null
    && udpc.IsOpen()
    && HostEnvironmentIsValid(udpc.env)
    && EndPointIsValidIPV4(udpc.LocalEndPoint())
}

predicate EndPointsAreValidIPV4(eps:seq<EndPoint>) 
{
    forall i :: 0 <= i < |eps| ==> EndPointIsValidIPV4(eps[i])
}


} 
