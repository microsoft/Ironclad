include "../../Common/Framework/AbstractService.s.dfy"
include "AppStateMachine.s.dfy"

module AbstractServiceRSL_s exclusively refines AbstractService_s {
import opened AppStateMachine_s
    
datatype AppRequest = AppRequest(client:EndPoint, seqno:int, request:AppMessage)
datatype AppReply   = AppReply(client:EndPoint, seqno:int, reply:AppMessage)

datatype ServiceState' = ServiceState'(
    serverAddresses:set<EndPoint>,
    app:AppState,
    requests:set<AppRequest>,
    replies:set<AppReply>
    )

type ServiceState = ServiceState'

predicate Service_Init(s:ServiceState, serverAddresses:set<EndPoint>)
{
       s.serverAddresses == serverAddresses
    && s.app == AppInitialize()
    && s.requests == {}
    && s.replies == {}
}

predicate ServiceNextServerExecutesAppRequest(s:ServiceState, s':ServiceState, client:EndPoint, seqno:int, request:AppMessage)
{
       s'.serverAddresses == s.serverAddresses
    && s'.requests == s.requests + { AppRequest(client, seqno, request) }
    && s'.app == AppHandleRequest(s.app, request).0
    && s'.replies == s.replies + { AppReply(client, seqno, AppHandleRequest(s.app, request).1) }
}

predicate Service_Next(s:ServiceState, s':ServiceState)
{
    exists client, seqno, request :: ServiceNextServerExecutesAppRequest(s, s', client, seqno, request)
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

function MarshallServiceRequest(seqno:int, request:AppMessage) : seq<byte>
{
  if 0 <= seqno < 0x1_0000_0000_0000_0000 then
        [ 0, 0, 0, 0, 0, 0, 0, 0] // MarshallMesssage_Request magic number
      + Uint64ToBytes(uint64(seqno))        
      + MarshallAppMessage(request)
  else 
      [ 1 ]
}

function MarshallServiceReply(seqno:int, reply:AppMessage) : seq<byte>
{
  if 0 <= seqno < 0x1_0000_0000_0000_0000 then
        [ 0, 0, 0, 0, 0, 0, 0, 6] // MarshallMesssage_Reply magic number
      + Uint64ToBytes(uint64(seqno))        
      + MarshallAppMessage(reply)
  else 
      [ 1 ]
}

predicate Service_Correspondence(concretePkts:set<LPacket<EndPoint, seq<byte>>>, serviceState:ServiceState) 
{
       (forall p, seqno, reply :: p in concretePkts && p.src in serviceState.serverAddresses && p.msg == MarshallServiceReply(seqno, reply) ==>
               AppReply(p.dst, seqno, reply) in serviceState.replies)
    && (forall req :: req in serviceState.requests ==> exists p :: p in concretePkts && p.dst in serviceState.serverAddresses 
                                                                && p.msg == MarshallServiceRequest(req.seqno, req.request)
                                                                && p.src == req.client)
}

}
