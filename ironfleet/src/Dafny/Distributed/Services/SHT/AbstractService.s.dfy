include "../../Common/Framework/AbstractService.s.dfy"
include "AppInterface.s.dfy"
include "HT.s.dfy"

module AbstractServiceSHT_s refines AbstractService_s {
import opened Bytes_s
import opened AppInterface_i`Spec
import opened SHT__HT_s
export Spec
    provides Native__Io_s, Environment_s, Native__NativeTypes_s
    provides ServiceState 
    provides Service_Init, Service_Next, Service_Correspondence

    reveals AppRequest, AppReply
    provides AppInterface_i, SHT__HT_s
    provides MarshallServiceGetRequest, MarshallServiceSetRequest, MarshallServiceReply
export All reveals *

datatype AppRequest = AppGetRequest(g_seqno:int, g_k:Key) | AppSetRequest(s_seqno:int, s_k:Key, ov:OptionalValue)
datatype AppReply   = AppReply(seqno:int, k:Key, ov:OptionalValue)
    
datatype ServiceState' = ServiceState'(
    serverAddresses:set<EndPoint>,
    ht:Hashtable,
    requests:set<AppRequest>,
    replies:set<AppReply>
    )

type ServiceState = ServiceState'

predicate Service_Init(s:ServiceState, serverAddresses:set<EndPoint>)
{
       s.serverAddresses == serverAddresses
    && SpecInit(s.ht)
    && s.requests == {}
    && s.replies == {}
}

/*predicate Service_Next_ServerReceivesRequest(s:ServiceState, s':ServiceState, req:AppRequest)
{
    s'.requests == s.requests + { req }
}*/

predicate Service_Next_ServerExecutesRequest(s:ServiceState, s':ServiceState, req:AppRequest, rep:AppReply)
{
       s'.serverAddresses == s.serverAddresses
    && s'.requests == s.requests + { req }
    && (req.AppGetRequest? ==> Get(s.ht, s'.ht, req.g_k, rep.ov) && s'.replies == s.replies + { rep } && req.g_k == rep.k)
    && (req.AppSetRequest? ==> Set(s.ht, s'.ht, req.s_k, req.ov) && s'.replies == s.replies + { rep } && req.s_k == rep.k && req.ov == rep.ov)
}

predicate Service_Next(s:ServiceState, s':ServiceState)
{
    exists request, reply :: Service_Next_ServerExecutesRequest(s, s', request, reply)
    //|| exists request :: Service_Next_ServerReceivesRequest(s, s', request)
}

function MarshallServiceGetRequest(app:AppRequest, reserved:seq<byte>) : seq<byte>
    requires app.AppGetRequest?
{
    if 0 <= app.g_seqno < 0x1_0000_0000_0000_0000 then
        [ 0, 0, 0, 0, 0, 0, 0, 0] // CSingleMessage_grammar magic number        
      + Uint64ToBytes(app.g_seqno as uint64)
      + reserved
      + [ 0, 0, 0, 0, 0, 0, 0, 0] // CMessage_GetRequest_grammar magic number
      + MarshallSHTKey(app.g_k)
    else
        [ 1 ]
}

function MarshallServiceSetRequest(app:AppRequest, reserved:seq<byte>) : seq<byte>
    requires app.AppSetRequest?
{    
    if 0 <= app.s_seqno < 0x1_0000_0000_0000_0000 then
        [ 0, 0, 0, 0, 0, 0, 0, 0] // CSingleMessage_grammar magic number        
      + Uint64ToBytes(app.s_seqno as uint64)
      + reserved
      + [ 0, 0, 0, 0, 0, 0, 0, 1] // CMessage_SetRequest_grammar magic number
      + MarshallSHTKey(app.s_k)
      + if app.ov.ValuePresent? then
            [ 0, 0, 0, 0, 0, 0, 0, 0] // ValuePresent magic number
            + MarshallSHTValue(app.ov.v)
        else
            [ 0, 0, 0, 0, 0, 0, 0, 1] // ValueAbsent magic number
    else
        [ 1 ]
}

function MarshallServiceReply(app:AppReply, reserved:seq<byte>) : seq<byte>
{
    if 0 <= app.seqno < 0x1_0000_0000_0000_0000 then
        [ 0, 0, 0, 0, 0, 0, 0, 0] // CSingleMessage_grammar magic number        
      + Uint64ToBytes(app.seqno as uint64)
      + reserved
      + [ 0, 0, 0, 0, 0, 0, 0, 2] // CMessage_Reply_grammar magic number
      + MarshallSHTKey(app.k)
      + if app.ov.ValuePresent? then
            [ 0, 0, 0, 0, 0, 0, 0, 0] // ValuePresent magic number
            + MarshallSHTValue(app.ov.v)
        else
            [ 0, 0, 0, 0, 0, 0, 0, 1] // ValueAbsent magic number
    else
        [ 1 ]
}

predicate Service_Correspondence(concretePkts:set<LPacket<EndPoint, seq<byte>>>, serviceState:ServiceState) 
{
       (forall p, reply, reserved_bytes :: 
                    p in concretePkts 
                 && p.src in serviceState.serverAddresses 
                 && p.msg == MarshallServiceReply(reply, reserved_bytes)
                 && |reserved_bytes| == 8
                    ==> reply in serviceState.replies)
    && (forall req :: req in serviceState.requests && req.AppGetRequest? 
                      ==> exists p, reserved_bytes :: p in concretePkts && p.dst in serviceState.serverAddresses 
                                                   && p.msg == MarshallServiceGetRequest(req, reserved_bytes)
                                                   && |reserved_bytes| == 8)
    && (forall req :: req in serviceState.requests && req.AppSetRequest? 
                      ==> exists p, reserved_bytes :: p in concretePkts && p.dst in serviceState.serverAddresses 
                                                   && p.msg == MarshallServiceSetRequest(req, reserved_bytes)
                                                   && |reserved_bytes| == 8)
}

}
