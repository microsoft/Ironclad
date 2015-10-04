include "Environment.i.dfy"
include "../../SHT/Network.i.dfy"

module LiveSHT__EnvironmentRefinement_i {
import opened LiveSHT__Environment_i
import opened SHT__Network_i

function LSHTPacket_Refine(p:LSHTPacket) : Packet
{
    Packet(p.dst, p.src, p.msg)
}

function LSHTPacketSet_Refine(packets:set<LSHTPacket>) : set<Packet>
{
    set p | p in packets :: LSHTPacket_Refine(p)
}

function LSHTPacketSeq_Refine(packets:seq<LSHTPacket>) : set<Packet>
{
    set p | p in packets :: LSHTPacket_Refine(p)
}

function LSHTIoSeq_RefineAsSends(ios:seq<LSHTIo>) : set<Packet>
{
    set io | io in ios && io.LIoOpSend? :: LSHTPacket_Refine(io.s)
}

function LSHTIoSeq_RefineAsReceives(ios:seq<LSHTIo>) : set<Packet>
{
    set io | io in ios && io.LIoOpReceive? :: LSHTPacket_Refine(io.r)
}

function LSHTEnvironment_Refine(e:LSHTEnvironment) : Network
{
    set p | p in e.sentPackets :: LSHTPacket_Refine(p)
}
} 
