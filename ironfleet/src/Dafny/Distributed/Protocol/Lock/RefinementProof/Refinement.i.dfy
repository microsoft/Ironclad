include "DistributedSystem.i.dfy"
include "../../../Services/Lock/AbstractService.s.dfy"
include "../../../Common/Collections/Sets.i.dfy"

module Refinement_i {
    import opened DistributedSystem_i
    import opened AbstractServiceLock_s 
    import opened Collections__Sets_i

    
    function AbstractifyGLS_State(gls:GLS_State) : ServiceState
    {
        ServiceState'(mapdomain(gls.ls.servers), gls.history)
    }

    /*lemma SingetonSetAllAreEqual<T>(s:set<T>)
        requires |s| == 1;
        ensures forall p,q :: p in s && q in s ==> p == q;
    {
        forall p,q | p in s && q in s 
            ensures p == q;
        {
            ThingsIKnowAboutASingletonSet(s, p, q);
        }
    }

    function getMinimumEpochPacket(pkts:set<LockPacket>) : LockPacket
        requires |pkts| > 0;
        requires forall p :: p in pkts ==> p.msg.Locked?;
        ensures  getMinimumEpochPacket(pkts).msg.Locked?;
        ensures  getMinimumEpochPacket(pkts) in pkts;
        ensures  forall p :: p in pkts ==> p.msg.locked_epoch >= getMinimumEpochPacket(pkts).msg.locked_epoch;
    {
        if |pkts| == 1 then
            var p :| p in pkts;
            SingetonSetAllAreEqual(pkts);
            p
        else
            var p :| p in pkts;
            var minRest := getMinimumEpochPacket(pkts - {p});
            if p.msg.locked_epoch < minRest.msg.locked_epoch then
                p
            else
                minRest
    }

    function makeHistoryExistsLockedPacket(ls:LS_State, locked_packets:set<LockPacket>) : seq<EndPoint>
        requires forall p :: p in locked_packets ==> p in ls.environment.sentPackets && p.msg.Locked? && p.src in ls.servers;
        requires |locked_packets| > 0;
        decreases |locked_packets|;
        //ensures forall p :: p in locked_packets ==> p.src in makeHistoryExistsLockedPacket(ls, locked_packets);
    {
        if |locked_packets| == 1 then
            var p :| p in locked_packets;
            [p.src]
        else
            var p := getMinimumEpochPacket(locked_packets);
            makeHistoryExistsLockedPacket(ls, locked_packets-{p}) + [p.src]
    }

    function makeHistory(ls:LS_State) : seq<EndPoint>
    {
        var locked_packets := set p | p in ls.environment.sentPackets && p.src in ls.servers && p.msg.Locked?;
        if |locked_packets| == 0 then
            if exists host :: host in ls.servers && ls.servers[host].held then
                var host :| host in ls.servers && ls.servers[host].held;
                [host]
            else
                []
        else
            makeHistoryExistsLockedPacket(ls, locked_packets)
            
    }*/


    /*function makeHistory1(ls:LS_State) : imap<int, set<EndPoint>>
    {
        imap i :: (set p | p in ls.environment.sentPackets && p.msg.Transfer? && p.src in ls.servers :: p.dst)
    }

    function makeHistory2(ls:LS_State) : imap<int, set<EndPoint>>
    {
        imap i :: (set p | p in ls.environment.sentPackets && p.msg.Locked? && p.src in ls.servers :: p.src)
    }*/

}
