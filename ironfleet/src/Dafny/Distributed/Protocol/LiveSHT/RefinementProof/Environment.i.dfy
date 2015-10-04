include "../../SHT/SingleDelivery.i.dfy"
include "../../SHT/Message.i.dfy"
include "../../../Common/Framework/Environment.s.dfy"

module LiveSHT__Environment_i {
import opened SHT__Message_i
import opened SHT__SingleDelivery_i
import opened Environment_s

type LSHTEnvironment = LEnvironment<NodeIdentity, SingleMessage<Message>>
type LSHTPacket = LPacket<NodeIdentity, SingleMessage<Message>>
type LSHTIo = LIoOp<NodeIdentity, SingleMessage<Message>>

function ConcatenateSHTIos(s:seq<seq<LSHTIo>>) : seq<LSHTIo>
{
    if |s| == 0 then
        []
    else
        s[0] + ConcatenateSHTIos(s[1..])
}

} 
