include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/RSL/Replica.i.dfy"
include "ReplicaModel.i.dfy"
include "ReplicaImplLemmas.i.dfy"
include "UdpRSL.i.dfy"
include "CClockReading.i.dfy"

module LiveRSL__ReplicaImplClass_i {

import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ReplicaModel_i
import opened LiveRSL__ReplicaImplLemmas_i
import opened LiveRSL__UdpRSL_i
import opened LiveRSL__CClockReading_i

class ReplicaImpl
{
    var replica:ReplicaState;
    var nextActionIndex:uint64;
    var udpClient:UdpClient;
    var localAddr:EndPoint;
    // Optimized mutable sets for ElectionState
    var cur_req_set:MutableSet<CRequestHeader>;
    var prev_req_set:MutableSet<CRequestHeader>;
    var reply_cache_mutable:MutableMap<EndPoint, CReply>;
    var msg_grammar:G;

    ghost var Repr : set<object>;

    predicate Valid()
        reads this;
        reads this.cur_req_set;
        reads this.prev_req_set;
        reads this.reply_cache_mutable;
        reads UdpClientIsValid.reads(udpClient);
    {
           ReplicaStateIsAbstractable(replica)
        && (0 <= int(nextActionIndex) < 10)
        && UdpClientIsValid(udpClient)
        && udpClient.LocalEndPoint() == localAddr
        && udpClient.LocalEndPoint() == replica.constants.all.config.replica_ids[replica.constants.my_index]
        && ReplicaStateIsValid(replica)
        && Repr == { this } + UdpClientRepr(udpClient)
        && cur_req_set != null && prev_req_set != null && cur_req_set != prev_req_set
        && MutableSet.SetOf(cur_req_set) == replica.proposer.election_state.cur_req_set
        && MutableSet.SetOf(prev_req_set) == replica.proposer.election_state.prev_req_set
        && reply_cache_mutable != null
        && MutableMap.MapOf(reply_cache_mutable) == replica.executor.reply_cache 
        && msg_grammar == CMessage_grammar()
    }

    function Env() : HostEnvironment
        reads this, UdpClientIsValid.reads(udpClient);
    {
        if udpClient!=null then udpClient.env else null
    }

    function RefineReplica() : LReplica
        reads this;
        requires ReplicaStateIsAbstractable(replica);
    {
        AbstractifyReplicaStateToLReplica(replica)
    }

    function AbstractifyToLScheduler() : LScheduler
        reads this;
        requires ReplicaStateIsAbstractable(replica);
    {
        LScheduler(
            AbstractifyReplicaStateToLReplica(replica),
            int(nextActionIndex))
    }

    method ConstructUdpClient(constants:ReplicaConstantsState, ghost env_:HostEnvironment) returns (ok:bool, client:UdpClient)
        requires env_!=null && env_.Valid() && env_.ok.ok();
        requires ReplicaConstantsState_IsValid(constants);
        modifies env_.ok;
        ensures ok ==> UdpClientIsValid(client)
                    && client.LocalEndPoint() == constants.all.config.replica_ids[constants.my_index]
                    && client.env == env_;
    {
        var my_ep := constants.all.config.replica_ids[constants.my_index];
        var ip_byte_array := new byte[|my_ep.addr|];
        assert EndPointIsValidIPV4(my_ep);
        seqIntoArrayOpt(my_ep.addr, ip_byte_array);
        var ip_endpoint;
        ok, ip_endpoint := IPEndPoint.Construct(ip_byte_array, my_ep.port, env_);
        if !ok { return; }
        ok, client := UdpClient.Construct(ip_endpoint, env_);
        if ok {
            calc {
                client.LocalEndPoint();
                ip_endpoint.EP();
                my_ep;
            }
        }
    }

    method {:timeLimitMultiplier 7} Replica_Init(constants:ReplicaConstantsState, ghost env_:HostEnvironment) returns (ok:bool)
        requires env_!=null && env_.Valid() && env_.ok.ok();
        requires ReplicaConstantsState_IsValid(constants);
        requires WellFormedLConfiguration(AbstractifyReplicaConstantsStateToLReplicaConstants(constants).all.config);
        //requires KnownSendersMatchConfig(constants.all.config);
        modifies this, udpClient;
        modifies env_.ok;
        ensures ok ==>
               Valid()
            && Env() == env_
            && this.replica.constants == constants
            && LSchedulerInit(AbstractifyToLScheduler(), AbstractifyReplicaConstantsStateToLReplicaConstants(constants));
    {
        ok, udpClient := ConstructUdpClient(constants, env_); 

        if (ok)
        {
            replica, cur_req_set, prev_req_set, reply_cache_mutable := InitReplicaState(constants);
            nextActionIndex := 0;
            localAddr := replica.constants.all.config.replica_ids[replica.constants.my_index];
            Repr := { this } + UdpClientRepr(udpClient);
            this.msg_grammar := CMessage_grammar();
        }
    }

    predicate ReceivedPacketProperties(cpacket:CPacket, udpEvent0:UdpEvent, io0:RslIo)
        reads this;
        requires CPaxosConfigurationIsValid(replica.constants.all.config);
    {
           CPacketIsSendable(cpacket)
        && PaxosEndPointIsValid(cpacket.src, replica.constants.all.config)
        && io0.LIoOpReceive?
        && UdpEventIsAbstractable(udpEvent0)
        && io0 == RefineRawEventToIo(udpEvent0)
        && UdpEventIsAbstractable(udpEvent0)
        && udpEvent0.LIoOpReceive? && AbstractifyCPacketToRslPacket(cpacket) == AbstractifyUdpPacketToRslPacket(udpEvent0.r)
    }
}


}
