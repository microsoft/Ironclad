include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/RSL/Replica.i.dfy"
include "ReplicaModel.i.dfy"
include "ReplicaImplLemmas.i.dfy"
include "UdpRSL.i.dfy"
include "CClockReading.i.dfy"

module LiveRSL__ReplicaImplClass_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened LiveRSL__CClockReading_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__ElectionState_i
import opened LiveRSL__Environment_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ReplicaConstantsState_i
import opened LiveRSL__ReplicaModel_i
import opened LiveRSL__ReplicaModel_Part1_i
import opened LiveRSL__ReplicaState_i
import opened LiveRSL__ReplicaImplLemmas_i
import opened LiveRSL__Types_i
import opened LiveRSL__UdpRSL_i
import opened Common__GenericMarshalling_i
import opened Common__UdpClient_i
import opened Common__Util_i

class ReplicaImpl
{
  var replica:ReplicaState;
  var nextActionIndex:uint64;
  var udpClient:UdpClient?;
  var localAddr:EndPoint;
  // Optimized mutable sets for ElectionState
  var cur_req_set:MutableSet<CRequestHeader>;
  var prev_req_set:MutableSet<CRequestHeader>;
  var reply_cache_mutable:MutableMap<EndPoint, CReply>;
  var msg_grammar:G;

  ghost var Repr : set<object>;

  constructor()
  {
    udpClient := null;
    var empty_MutableMap:MutableMap<EndPoint, CReply> := MutableMap.EmptyMap();
    reply_cache_mutable := empty_MutableMap;
    var empty_MutableSet:MutableSet<CRequestHeader> := MutableSet.EmptySet();
    cur_req_set := empty_MutableSet;
    prev_req_set := empty_MutableSet;
  }

  predicate Valid()
    reads this
    reads this.cur_req_set
    reads this.prev_req_set
    reads this.reply_cache_mutable
    reads if udpClient != null then UdpClientIsValid.reads(udpClient) else {}
  {
    && ReplicaStateIsAbstractable(replica)
    && (0 <= nextActionIndex as int < 10)
    && udpClient != null
    && UdpClientIsValid(udpClient)
    && udpClient.LocalEndPoint() == localAddr
    && udpClient.LocalEndPoint() == replica.constants.all.config.replica_ids[replica.constants.my_index]
    && ReplicaStateIsValid(replica)
    && Repr == { this } + UdpClientRepr(udpClient)
    && cur_req_set != prev_req_set
    && MutableSet.SetOf(cur_req_set) == replica.proposer.election_state.cur_req_set
    && MutableSet.SetOf(prev_req_set) == replica.proposer.election_state.prev_req_set
    && MutableMap.MapOf(reply_cache_mutable) == replica.executor.reply_cache 
    && msg_grammar == CMessage_grammar()
  }

  function Env() : HostEnvironment
    requires udpClient != null
    reads this, UdpClientIsValid.reads(udpClient)
  {
    udpClient.env
  }

  function AbstractifyToLReplica() : LReplica
    reads this
    requires ReplicaStateIsAbstractable(replica)
  {
    AbstractifyReplicaStateToLReplica(replica)
  }

  function AbstractifyToLScheduler() : LScheduler
    reads this
    requires ReplicaStateIsAbstractable(replica)
  {
    LScheduler(
      AbstractifyReplicaStateToLReplica(replica),
      nextActionIndex as int)
  }

  method ConstructUdpClient(constants:ReplicaConstantsState, ghost env_:HostEnvironment) returns (ok:bool, client:UdpClient?)
    requires env_.Valid() && env_.ok.ok()
    requires ReplicaConstantsState_IsValid(constants)
    modifies env_.ok
    ensures ok ==> && client != null
                   && UdpClientIsValid(client)
                   && client.LocalEndPoint() == constants.all.config.replica_ids[constants.my_index]
                   && client.env == env_
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
    requires env_.Valid() && env_.ok.ok()
    requires ReplicaConstantsState_IsValid(constants)
    requires WellFormedLConfiguration(AbstractifyReplicaConstantsStateToLReplicaConstants(constants).all.config)
    //requires KnownSendersMatchConfig(constants.all.config)
    modifies this, udpClient
    modifies env_.ok
    ensures ok ==>
            && Valid()
            && Env() == env_
            && this.replica.constants == constants
            && LSchedulerInit(AbstractifyToLScheduler(), AbstractifyReplicaConstantsStateToLReplicaConstants(constants))
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
    reads this
    requires CPaxosConfigurationIsValid(replica.constants.all.config)
  {
    && CPacketIsSendable(cpacket)
    && PaxosEndPointIsValid(cpacket.src, replica.constants.all.config)
    && io0.LIoOpReceive?
    && UdpEventIsAbstractable(udpEvent0)
    && io0 == AbstractifyUdpEventToRslIo(udpEvent0)
    && UdpEventIsAbstractable(udpEvent0)
    && udpEvent0.LIoOpReceive? && AbstractifyCPacketToRslPacket(cpacket) == AbstractifyUdpPacketToRslPacket(udpEvent0.r)
  }
}


}
