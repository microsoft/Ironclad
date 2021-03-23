include "Message.i.dfy"
include "SingleMessage.i.dfy"

module SHT__Network_i {
import opened Concrete_NodeIdentity_i`Spec
import opened SHT__Message_i
import opened SHT__SingleMessage_i

// Ugly failure to parameterize
type PMsg = SingleMessage<Message>
datatype Packet = Packet(dst:NodeIdentity, src:NodeIdentity, msg:PMsg)

type Network = set<Packet>

predicate Network_Init(n:Network) {
    n == {}
}

function PacketsTo(ps:set<Packet>, dst:NodeIdentity) : set<Packet>
{
    set p | p in ps && p.dst ==dst
}

predicate Network_Receive(n:Network, dst:NodeIdentity, recv:set<Packet>) {
    recv == PacketsTo(n, dst)
}

predicate Network_Send(n:Network, n':Network, src:NodeIdentity, out:set<Packet>)
{
       (forall p :: p in out ==> p.src == src)  // Jay rewired this to have OutboundPackets
    && n' == n + out
}

} 
