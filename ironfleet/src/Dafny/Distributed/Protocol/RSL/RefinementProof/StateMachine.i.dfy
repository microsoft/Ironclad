include "../DistributedSystem.i.dfy"

module DirectRefinement__StateMachine_i {

import opened LiveRSL__DistributedSystem_i
import opened LiveRSL__Types_i
import opened Concrete_NodeIdentity_i
import opened AppStateMachine_i
import opened Collections__Seqs_s

datatype RSLSystemState = RSLSystemState(
  server_addresses:set<NodeIdentity>,
  app:AppState,
  requests:set<Request>,
  replies:set<Reply>
  )

predicate RslSystemInit(s:RSLSystemState, server_addresses:set<NodeIdentity>)
{
  && s.server_addresses == server_addresses
  && s.app == AppInitialize()
  && s.requests == {}
  && s.replies == {}
}

predicate RslSystemNextServerExecutesRequest(s:RSLSystemState, s':RSLSystemState, req:Request)
{
  && s'.server_addresses == s.server_addresses
  && s'.requests == s.requests + { req }
  && s'.app == AppHandleRequest(s.app, req.request).0
  && s'.replies == s.replies + { Reply(req.client, req.seqno, AppHandleRequest(s.app, req.request).1) }
}

predicate RslStateSequenceReflectsBatchExecution(s:RSLSystemState, s':RSLSystemState, intermediate_states:seq<RSLSystemState>,
                                                 batch:seq<Request>)
{
  && |intermediate_states| == |batch| + 1
  && intermediate_states[0] == s
  && last(intermediate_states) == s'
  && forall i :: 0 <= i < |batch| ==> RslSystemNextServerExecutesRequest(intermediate_states[i], intermediate_states[i+1], batch[i])
}

predicate RslSystemNext(s:RSLSystemState, s':RSLSystemState)
{
  exists intermediate_states, batch :: RslStateSequenceReflectsBatchExecution(s, s', intermediate_states, batch)
}

predicate RslSystemRefinement(ps:RslState, rs:RSLSystemState)
{
  && (forall p :: p in ps.environment.sentPackets && p.src in rs.server_addresses && p.msg.RslMessage_Reply?
           ==> Reply(p.dst, p.msg.seqno_reply, p.msg.reply) in rs.replies)
  && (forall req :: req in rs.requests ==> exists p :: p in ps.environment.sentPackets && p.dst in rs.server_addresses && p.msg.RslMessage_Request?
                                         && req == Request(p.src, p.msg.seqno_req, p.msg.val))
}

predicate RslSystemBehaviorRefinementCorrect(server_addresses:set<NodeIdentity>, low_level_behavior:seq<RslState>, high_level_behavior:seq<RSLSystemState>)
{
  && |high_level_behavior| == |low_level_behavior|
  && (forall i :: 0 <= i < |low_level_behavior| ==> RslSystemRefinement(low_level_behavior[i], high_level_behavior[i]))
  && |high_level_behavior| > 0
  && RslSystemInit(high_level_behavior[0], server_addresses)
  && (forall i {:trigger high_level_behavior[i], high_level_behavior[i+1]} :: 0 <= i < |high_level_behavior| - 1
          ==> RslSystemNext(high_level_behavior[i], high_level_behavior[i+1]))
}

}
