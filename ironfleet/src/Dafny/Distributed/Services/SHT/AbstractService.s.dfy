include "../../Common/Framework/AbstractService.s.dfy"
include "AppInterface.s.dfy"
include "HT.s.dfy"

module AbstractServiceSHT_s exclusively refines AbstractService_s {
import opened AppInterface_s
import opened SHT__HT_s

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

function Uint64ToBytes(u:uint64) : seq<byte>
{
    [byte( u/0x1000000_00000000),
     byte((u/  0x10000_00000000)%0x100),
     byte((u/    0x100_00000000)%0x100),
     byte((u/      0x1_00000000)%0x100),
     byte((u/         0x1000000)%0x100),
     byte((u/           0x10000)%0x100),
     byte((u/             0x100)%0x100),
     byte( u                    %0x100)]
}

function MarshallServiceGetRequest(app:AppRequest, reserved:seq<byte>) : seq<byte>
    requires app.AppGetRequest?
{
    if 0 <= app.g_seqno < 0x1_0000_0000_0000_0000 then
        [ 0, 0, 0, 0, 0, 0, 0, 0] // CSingleMessage_grammar magic number        
      + Uint64ToBytes(uint64(app.g_seqno))
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
      + Uint64ToBytes(uint64(app.s_seqno))
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
      + Uint64ToBytes(uint64(app.seqno))
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
