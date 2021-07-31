include "Node.i.dfy"
include "NetLock.i.dfy"

module NodeImpl_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened Environment_s
import opened Types_i
import opened Message_i
import opened Impl_Node_i
import opened NetLock_i
import opened Protocol_Node_i
import opened Common__Util_i
import opened Common__NetClient_i

class NodeImpl
{
    var node:CNode;
    var netClient:NetClient?;
    var localAddr:EndPoint;

    ghost var Repr : set<object>;

    constructor () {
        netClient := null;
    }

    predicate Valid()
        reads this;
        reads NetClientIsValid.reads(netClient);
    {
           CNodeValid(node)
        && NetClientIsValid(netClient)
        && netClient.LocalEndPoint() == localAddr
        && netClient.LocalEndPoint() == node.config[node.my_index]
        && Repr == { this } + NetClientRepr(netClient)
    }
        
    function Env() : HostEnvironment?
        reads this, NetClientIsValid.reads(netClient);
    {
        if netClient!=null then netClient.env else null
    }
   
    method ConstructNetClient(me:EndPoint, ghost env_:HostEnvironment) 
        returns (ok:bool, client:NetClient?)
        requires env_.Valid() && env_.ok.ok();
        requires EndPointIsValidPublicKey(me);
        modifies env_.ok;
        ensures ok ==> NetClientIsValid(client)
                    && client.LocalEndPoint() == me
                    && client.env == env_;
    {
        client := null;
        var my_ep := me;

        var ip_endpoint;
        ok, ip_endpoint := CryptoEndPoint.Construct(my_ep.public_key, env_);
        if !ok { return; }

        ok, client := NetClient.Construct(ip_endpoint, env_);
        if ok {
            calc {
                client.LocalEndPoint();
                ip_endpoint.EP();
                my_ep;
            }
        }
    }

    method InitNode(config:Config, my_index:uint64, ghost env_:HostEnvironment) returns (ok:bool)
        requires env_.Valid() && env_.ok.ok();
        requires ValidConfig(config) && ValidConfigIndex(config, my_index);
        modifies this, netClient;
        modifies env_.ok;
        ensures ok ==>
               Valid()
            && Env() == env_
            && NodeInit(AbstractifyCNode(node), my_index as int, config)
            && node.config == config 
            && node.my_index == my_index;
    {
        ok, netClient := ConstructNetClient(config[my_index], env_); 

        if (ok) {
            node := NodeInitImpl(my_index, config);
            assert node.my_index == my_index;
            localAddr := node.config[my_index];
            Repr := { this } + NetClientRepr(netClient);
            
        }
    }

    method NodeNextGrant() returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<LockIo>)
        requires Valid();
        modifies Repr;
        ensures Repr == old(Repr);
        ensures ok == NetClientOk(netClient);
        ensures Env() == old(Env());
        ensures ok ==> (
               Valid()
            && NodeGrant(old(AbstractifyCNode(node)), AbstractifyCNode(node), ios)
            && AbstractifyRawLogToIos(netEventLog) == ios
            && OnlySentMarshallableData(netEventLog)
            && old(Env().net.history()) + netEventLog == Env().net.history());
    {
        var transfer_packet;
        node, transfer_packet, ios := NodeGrantImpl(node);
        ok := true;

        if transfer_packet.Some? {
            ghost var sendEventLog;
            ok, sendEventLog := SendPacket(netClient, transfer_packet, localAddr); 
            netEventLog := sendEventLog;
        } else {
            netEventLog := [];
            assert AbstractifyRawLogToIos(netEventLog) == ios;
        }
    }

    method NodeNextAccept() returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<LockIo>)
        requires Valid();
        modifies Repr;
        ensures Repr == old(Repr);
        ensures ok == NetClientOk(netClient);
        ensures Env() == old(Env());
        ensures ok ==> (
               Valid()
            && NodeAccept(old(AbstractifyCNode(node)), AbstractifyCNode(node), ios)
            && AbstractifyRawLogToIos(netEventLog) == ios
            && OnlySentMarshallableData(netEventLog)
            && old(Env().net.history()) + netEventLog == Env().net.history());
    {
        var rr;
        ghost var receiveEvent;
        rr, receiveEvent := Receive(netClient, localAddr);

        netEventLog := [ receiveEvent ];
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
                ok, sendEventLog := SendPacket(netClient, locked_packet, localAddr); 
                netEventLog := netEventLog + sendEventLog;
            }
        }
    }


    method HostNextMain()
        returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<LockIo>)
        requires Valid();
        modifies Repr;
        ensures  Repr == old(Repr);
        ensures  ok <==> Env() != null && Env().Valid() && Env().ok.ok();
        ensures  Env() == old(Env());
        ensures  ok ==> (
                   Valid()
                && NodeNext(old(AbstractifyCNode(node)), AbstractifyCNode(node), ios)
                && AbstractifyRawLogToIos(netEventLog) == ios
                && OnlySentMarshallableData(netEventLog)
                && old(Env().net.history()) + netEventLog == Env().net.history()
                );
    {
        if node.held {
            ok, netEventLog, ios := NodeNextGrant();
        } else {
            ok, netEventLog, ios := NodeNextAccept();
        }
    }
}

} 
