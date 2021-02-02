include "Node.i.dfy"
include "UdpLock.i.dfy"

module NodeImpl_i {
import opened Impl_Node_i
import opened UdpLock_i

class NodeImpl
{
    var node:CNode;
    var udpClient:UdpClient;
    var localAddr:EndPoint;

    ghost var Repr : set<object>;

    constructor () {
        udpClient := null;
    }

    predicate Valid()
        reads this;
        reads UdpClientIsValid.reads(udpClient);
    {
           CNodeValid(node)
        && UdpClientIsValid(udpClient)
        && udpClient.LocalEndPoint() == localAddr
        && udpClient.LocalEndPoint() == node.config[node.my_index]
        && Repr == { this } + UdpClientRepr(udpClient)
    }
        
    function Env() : HostEnvironment
        reads this, UdpClientIsValid.reads(udpClient);
    {
        if udpClient!=null then udpClient.env else null
    }
   
    method ConstructUdpClient(me:EndPoint, ghost env_:HostEnvironment) 
        returns (ok:bool, client:UdpClient)
        requires env_!=null && env_.Valid() && env_.ok.ok();
        requires EndPointIsValidIPV4(me);
        modifies env_.ok;
        ensures ok ==> UdpClientIsValid(client)
                    && client.LocalEndPoint() == me
                    && client.env == env_;
    {
        var my_ep := me;
        var ip_byte_array := new byte[|my_ep.addr|];
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

    method InitNode(config:Config, my_index:uint64, ghost env_:HostEnvironment) returns (ok:bool)
        requires env_!=null && env_.Valid() && env_.ok.ok();
        requires ValidConfig(config) && ValidConfigIndex(config, my_index);
        modifies this, udpClient;
        modifies env_.ok;
        ensures ok ==>
               Valid()
            && Env() == env_
            && NodeInit(AbstractifyCNode(node), int(my_index), config)
            && node.config == config 
            && node.my_index == my_index;
    {
        ok, udpClient := ConstructUdpClient(config[my_index], env_); 

        if (ok) {
            node := NodeInitImpl(my_index, config);
            assert node.my_index == my_index;
            localAddr := node.config[my_index];
            Repr := { this } + UdpClientRepr(udpClient);
            
        }
    }

    method NodeNextGrant() returns (ok:bool, ghost udpEventLog:seq<UdpEvent>, ghost ios:seq<LockIo>)
        requires Valid();
        modifies Repr;
        ensures Repr == old(Repr);
        ensures ok == UdpClientOk(udpClient);
        ensures Env() == old(Env());
        ensures ok ==> (
               Valid()
            && NodeGrant(old(AbstractifyCNode(node)), AbstractifyCNode(node), ios)
            && AbstractifyRawLogToIos(udpEventLog) == ios
            && OnlySentMarshallableData(udpEventLog)
            && old(Env().udp.history()) + udpEventLog == Env().udp.history());
    {
        var transfer_packet;
        node, transfer_packet, ios := NodeGrantImpl(node);
        ok := true;

        if transfer_packet.Some? {
            ghost var sendEventLog;
            ok, sendEventLog := SendPacket(udpClient, transfer_packet, localAddr); 
            udpEventLog := sendEventLog;
        } else {
            udpEventLog := [];
            assert AbstractifyRawLogToIos(udpEventLog) == ios;
        }
    }

    method NodeNextAccept() returns (ok:bool, ghost udpEventLog:seq<UdpEvent>, ghost ios:seq<LockIo>)
        requires Valid();
        modifies Repr;
        ensures Repr == old(Repr);
        ensures ok == UdpClientOk(udpClient);
        ensures Env() == old(Env());
        ensures ok ==> (
               Valid()
            && NodeAccept(old(AbstractifyCNode(node)), AbstractifyCNode(node), ios)
            && AbstractifyRawLogToIos(udpEventLog) == ios
            && OnlySentMarshallableData(udpEventLog)
            && old(Env().udp.history()) + udpEventLog == Env().udp.history());
    {
        var rr;
        ghost var receiveEvent;
        rr, receiveEvent := Receive(udpClient, localAddr);

        udpEventLog := [ receiveEvent ];
        if (rr.RRFail?) {
            ok := false;
            return;
        } else if (rr.RRTimeout?) {
            ok := true;
            ios := [ LIoOpTimeoutReceive() ];
            return;
        } else {
            ok := true;
            var locked_packet;
            node, locked_packet, ios := NodeAcceptImpl(node, rr.cpacket);

            if locked_packet.Some? {
                ghost var sendEventLog;
                ok, sendEventLog := SendPacket(udpClient, locked_packet, localAddr); 
                udpEventLog := udpEventLog + sendEventLog;
            }
        }
    }


    method HostNextMain()
        returns (ok:bool, ghost udpEventLog:seq<UdpEvent>, ghost ios:seq<LockIo>)
        requires Valid();
        modifies Repr;
        ensures  Repr == old(Repr);
        ensures  ok <==> Env() != null && Env().Valid() && Env().ok.ok();
        ensures  Env() == old(Env());
        ensures  ok ==> (
                   Valid()
                && NodeNext(old(AbstractifyCNode(node)), AbstractifyCNode(node), ios)
                && AbstractifyRawLogToIos(udpEventLog) == ios
                && OnlySentMarshallableData(udpEventLog)
                && old(Env().udp.history()) + udpEventLog == Env().udp.history()
                );
    {
        if node.held {
            ok, udpEventLog, ios := NodeNextGrant();
        } else {
            ok, udpEventLog, ios := NodeNextAccept();
        }
    }
}

} 
