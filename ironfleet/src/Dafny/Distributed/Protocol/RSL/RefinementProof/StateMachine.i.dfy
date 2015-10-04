include "../DistributedSystem.i.dfy"

module DirectRefinement__StateMachine_i {

import opened LiveRSL__DistributedSystem_i

datatype RSLSystemState = RSLSystemState(
    server_addresses:set<NodeIdentity>,
    app:AppState,
    requests:set<Request>,
    replies:set<Reply>
    )

predicate RslSystemInit(s:RSLSystemState, server_addresses:set<NodeIdentity>)
{
       s.server_addresses == server_addresses
    && s.app == AppInitialize()
    && s.requests == {}
    && s.replies == {}
}

predicate RslSystemNextServerExecutesRequest(s:RSLSystemState, s':RSLSystemState, client:NodeIdentity, seqno:int, request:AppMessage)
{
       s'.server_addresses == s.server_addresses
    && s'.requests == s.requests + { Request(client, seqno, request) }
    && s'.app == AppHandleRequest(s.app, request).0
    && s'.replies == s.replies + { Reply(client, seqno, AppHandleRequest(s.app, request).1) }
}

predicate RslSystemNext(s:RSLSystemState, s':RSLSystemState)
{
    exists client, seqno, request :: RslSystemNextServerExecutesRequest(s, s', client, seqno, request)
}

predicate RslSystemRefinement(ps:RslState, rs:RSLSystemState)
{
       (forall p :: p in ps.environment.sentPackets && p.src in rs.server_addresses && p.msg.RslMessage_Reply? ==>
               Reply(p.dst, p.msg.seqno_reply, p.msg.reply) in rs.replies)
    && (forall req :: req in rs.requests ==> exists p :: p in ps.environment.sentPackets && p.dst in rs.server_addresses && p.msg.RslMessage_Request?
                                              && req == Request(p.src, p.msg.seqno_req, p.msg.val))
}

predicate RslSystemBehaviorRefinementCorrect(server_addresses:set<NodeIdentity>, low_level_behavior:seq<RslState>, high_level_behavior:seq<RSLSystemState>, refinement_mapping:seq<int>)
{
       |refinement_mapping| == |low_level_behavior|
    && (forall i :: 0 <= i < |refinement_mapping| ==> 0 <= refinement_mapping[i] < |high_level_behavior|)
    && (forall i :: 0 <= i < |low_level_behavior| - 1 ==> refinement_mapping[i] <= refinement_mapping[i+1])
    && (forall i :: 0 <= i < |low_level_behavior| ==> RslSystemRefinement(low_level_behavior[i], high_level_behavior[refinement_mapping[i]]))
    && |high_level_behavior| > 0
    && |refinement_mapping| > 0 
    && refinement_mapping[0] == 0
    && RslSystemInit(high_level_behavior[0], server_addresses)
    && (forall i :: 0 <= i < |high_level_behavior| - 1 ==> RslSystemNext(high_level_behavior[i], high_level_behavior[i+1]))
}

}
