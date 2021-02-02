include "Types.i.dfy"

module Protocol_Node_i {
import opened Types_i
import opened Native__Io_s

type Config = seq<EndPoint>

datatype Node = Node(held:bool, epoch:int, my_index:int, config:Config)

predicate NodeInit(s:Node, my_index:int, config:Config)
{
    s.epoch == (if my_index == 0 then 1 else 0)
 && 0 <= my_index < |config|
 && s.my_index == my_index // change
 && s.held == (my_index == 0)
 && s.config == config
}

predicate NodeGrant(s:Node, s':Node, ios:seq<LockIo>)
{
    s.my_index == s'.my_index // change
 && if s.held && s.epoch < 0xFFFF_FFFF_FFFF_FFFF then 
        !s'.held 
     && |ios| == 1 && ios[0].LIoOpSend?
     && |s.config| > 0
     && s'.config == s.config
     && s'.epoch == s.epoch
     && var outbound_packet := ios[0].s;
            outbound_packet.msg.Transfer? 
         && outbound_packet.msg.transfer_epoch == s.epoch + 1
         && outbound_packet.dst == s.config[(s.my_index + 1) % |s.config|]
    else 
        s == s' && ios == []
}

predicate NodeAccept(s:Node, s':Node, ios:seq<LockIo>)
{
    s.my_index == s'.my_index // change
 && |ios| >= 1
 && if ios[0].LIoOpTimeoutReceive? then 
        s == s' && |ios| == 1
    else
        ios[0].LIoOpReceive?
     && if    !s.held 
           && ios[0].r.src in s.config
           && ios[0].r.msg.Transfer? 
           && ios[0].r.msg.transfer_epoch > s.epoch then
                   s'.held
                && |ios| == 2
                && ios[1].LIoOpSend?
                && ios[1].s.msg.Locked?
                && s'.epoch == ios[0].r.msg.transfer_epoch == ios[1].s.msg.locked_epoch
                && s'.config == s.config
        else 
            s == s' && |ios| == 1
}

predicate NodeNext(s:Node, s':Node, ios:seq<LockIo>)
{
    NodeGrant(s, s', ios)
 || NodeAccept(s, s', ios)
}


}
