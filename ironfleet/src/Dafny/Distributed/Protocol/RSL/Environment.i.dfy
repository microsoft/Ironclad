include "Types.i.dfy"
include "Message.i.dfy"
include "../../Common/Framework/Environment.s.dfy"

module LiveRSL__Environment_i {
import opened LiveRSL__Types_i
import opened LiveRSL__Message_i
import opened Environment_s
import opened Concrete_NodeIdentity_i

type RslEnvironment = LEnvironment<NodeIdentity, RslMessage>
type RslPacket = LPacket<NodeIdentity, RslMessage>
type RslIo = LIoOp<NodeIdentity, RslMessage>

function ConcatenatePaxosIos(s:seq<seq<RslIo>>) : seq<RslIo>
{
  if |s| == 0 then
    []
  else
    s[0] + ConcatenatePaxosIos(s[1..])
}

} 
