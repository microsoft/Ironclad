include "../../Protocol/Lock/Node.i.dfy"
include "Message.i.dfy"
include "../Common/UdpClient.i.dfy"

module Impl_Node_i {
import opened Protocol_Node_i
import opened Message_i
import opened Common__UdpClient_i

datatype CNode = CNode(held:bool, epoch:uint64, my_index:uint64, config:Config)

predicate ValidConfig(c:Config)
{
    0 < |c| < 0x1_0000_0000_0000_0000
 && (forall e :: e in c ==> EndPointIsValidIPV4(e))
}

predicate ValidConfigIndex(c:Config, index:uint64)
{
    0 <= int(index) < |c|
}

predicate CNodeValid(c:CNode)
{
       ValidConfig(c.config)
    && ValidConfigIndex(c.config, c.my_index)
}

function AbstractifyCNode(n:CNode) : Node
{
    Node(n.held, int(n.epoch), int(n.my_index), n.config)
}

method NodeInitImpl(my_index:uint64, config:Config) returns (node:CNode)
    requires 0 < |config| < 0x1_0000_0000_0000_0000;
    requires 0 <= int(my_index) < |config|;
    ensures CNodeValid(node);
    ensures NodeInit(AbstractifyCNode(node), int(my_index), config);
    ensures node.my_index == my_index;
    ensures node.config == config;
{
    node := CNode(my_index == 0, 0, my_index, config);
}

method NodeGrantImpl(s:CNode) returns (s':CNode, packet:CLockPacket, ghost ios:seq<LockIo>)
    requires CNodeValid(s);
    ensures  NodeGrant(AbstractifyCNode(s), AbstractifyCNode(s'), ios);
    ensures  |ios| == 0 || |ios| == 1;
    ensures  |ios| == 1 ==> ios[0].LIoOpSend? && ios[0].s == AbstractifyCLockPacket(packet);
    ensures  CNodeValid(s');
{
    if s.held && s.epoch < 0xFFFF_FFFF_FFFF_FFFF {
        s' := s[held := false];
        var dst_index := (s.my_index + 1) % uint64(|s.config|);
        packet := LPacket(s.config[dst_index], s.config[s.my_index], CTransfer(s.epoch + 1));
        ios := [LIoOpSend(AbstractifyCLockPacket(packet))];
    } else {
        s' := s;
        ios := [];
    }
}

method NodeAcceptImpl(s:CNode, transfer_packet:CLockPacket) 
    returns (s':CNode, locked_packet:CLockPacket, ghost ios:seq<LockIo>)
    requires CNodeValid(s);
    ensures  NodeAccept(AbstractifyCNode(s), AbstractifyCNode(s'), ios);
    ensures  |ios| == 1 || |ios| == 2;
    ensures  |ios| == 1 ==> ios[0].LIoOpReceive? && ios[0].r == AbstractifyCLockPacket(transfer_packet);
    ensures  |ios| == 2 ==> ios == [LIoOpReceive(AbstractifyCLockPacket(transfer_packet)), 
                                    LIoOpSend(AbstractifyCLockPacket(locked_packet))];
    ensures  CNodeValid(s');
{
    ios := [LIoOpReceive(AbstractifyCLockPacket(transfer_packet))];

    if    !s.held 
       && transfer_packet.src in s.config
       && transfer_packet.msg.CTransfer? 
       && transfer_packet.msg.transfer_epoch > s.epoch {
        s' := s[held := true][epoch := transfer_packet.msg.transfer_epoch];
        locked_packet := LPacket(transfer_packet.src, 
                                 s.config[s.my_index],
                                 CLocked(transfer_packet.msg.transfer_epoch));
        ios := ios + [LIoOpSend(AbstractifyCLockPacket(locked_packet))];
        print "I hold the lock!\n";
    } else  {
        s' := s;
    }
}

}
