/////////////////////////////////////////////////////////////////////////////
//
// This is the specification for an abstract service that implements an
// application-defined state machine.  It provides linearizability of
// state-machine operations requested by clients.  That is, each operation
// the service executes appears to occur atomically, at a point after it
// was submitted by the client and before the service sent its response.
//
// Note that the specification does not require exactly-once semantics.
// If one needs exactly-once semantics, one should enforce that in the
// application state machine.  For instance, the state machine could keep
// track of the highest request sequence number seen from each client, and
// treat requests with older sequence numbers as no-ops.
//
/////////////////////////////////////////////////////////////////////////////

include "../../Common/Framework/AbstractService.s.dfy"
include "../../Common/Collections/Seqs.s.dfy"
include "AppStateMachine.i.dfy"

module AbstractServiceRSL_s refines AbstractService_s {
import opened AppStateMachine_i
import opened Collections__Seqs_s
    
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
  && s.serverAddresses == serverAddresses
  && s.app == AppInitialize()
  && s.requests == {}
  && s.replies == {}
}

predicate ServiceExecutesAppRequest(s:ServiceState, s':ServiceState, req:AppRequest)
{
  && s'.serverAddresses == s.serverAddresses
  && s'.requests == s.requests + { req }
  && s'.app == AppHandleRequest(s.app, req.request).0
  && s'.replies == s.replies + { AppReply(req.client, req.seqno, AppHandleRequest(s.app, req.request).1) }
}

predicate StateSequenceReflectsBatchExecution(s:ServiceState, s':ServiceState, intermediate_states:seq<ServiceState>, batch:seq<AppRequest>)
{
  && |intermediate_states| == |batch| + 1
  && intermediate_states[0] == s
  && last(intermediate_states) == s'
  && forall i :: 0 <= i < |batch| ==> ServiceExecutesAppRequest(intermediate_states[i], intermediate_states[i+1], batch[i])
}

predicate Service_Next(s:ServiceState, s':ServiceState)
{
  exists intermediate_states, batch :: StateSequenceReflectsBatchExecution(s, s', intermediate_states, batch)
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

function MarshallServiceRequest(seqno:int, request:AppMessage) : seq<byte>
{
  if 0 <= seqno < 0x1_0000_0000_0000_0000 then
        [ 0, 0, 0, 0, 0, 0, 0, 0] // MarshallMesssage_Request magic number
      + Uint64ToBytes(seqno as uint64)        
      + MarshallAppMessage(request)
  else 
      [ 1 ]
}

function MarshallServiceReply(seqno:int, reply:AppMessage) : seq<byte>
{
  if 0 <= seqno < 0x1_0000_0000_0000_0000 then
      [ 0, 0, 0, 0, 0, 0, 0, 6] // MarshallMesssage_Reply magic number
    + Uint64ToBytes(seqno as uint64)        
    + MarshallAppMessage(reply)
  else 
    [ 1 ]
}

predicate Service_Correspondence(concretePkts:set<LPacket<EndPoint, seq<byte>>>, serviceState:ServiceState) 
{
  && (forall p, seqno, reply :: p in concretePkts && p.src in serviceState.serverAddresses && p.msg == MarshallServiceReply(seqno, reply) ==>
             AppReply(p.dst, seqno, reply) in serviceState.replies)
  && (forall req :: req in serviceState.requests ==> exists p :: p in concretePkts && p.dst in serviceState.serverAddresses 
                                                                    && p.msg == MarshallServiceRequest(req.seqno, req.request)
                                                                    && p.src == req.client)
}

}
