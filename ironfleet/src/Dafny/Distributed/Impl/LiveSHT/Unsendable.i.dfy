include "../../Protocol/LiveSHT/Scheduler.i.dfy"
include "../SHT/PacketParsing.i.dfy"

module LiveSHT__Unsendable_i {
    import opened Native__NativeTypes_s
    import opened Native__Io_s
    import opened Logic__Option_i
    import opened Environment_s
    import opened LiveSHT__Scheduler_i
    import opened SHT__PacketParsing_i
    import opened SHT__Host_i
    import opened SHT__Keys_i
    import opened Common__GenericMarshalling_i

    predicate IosReflectIgnoringUnDemarshallable(ios:seq<LIoOp<EndPoint, seq<byte>>>)
    {
           |ios| == 1
        && ios[0].LIoOpReceive?
        && !Demarshallable(ios[0].r.msg, CSingleMessage_grammar())
    }


    predicate IosReflectIgnoringUnParseable(s:LScheduler, ios:seq<LIoOp<EndPoint, seq<byte>>>)
    {
        ios == []
     && (   s.host.receivedPacket.Some? 
         && s.host.receivedPacket.v.msg.SingleMessage? 
         && s.host.receivedPacket.v.msg.m.Delegate?
         && var msg := s.host.receivedPacket.v.msg.m;
            !(ValidKeyRange(msg.range) && ValidHashtable(msg.h) && !EmptyKeyRange(msg.range)))
    }
    
    predicate HostNextIgnoreUnsendableReceive(s:LScheduler, s':LScheduler, ios:seq<LIoOp<EndPoint, seq<byte>>>)
    {
        s.nextActionIndex == 0
     && s' == s.(nextActionIndex := 1)
     && IosReflectIgnoringUnDemarshallable(ios) 
    }

    predicate IgnoreSchedulerUpdate(s:LScheduler, s':LScheduler) 
    {
        if ShouldProcessReceivedMessage(s.host) then
            s' == s.(nextActionIndex := 2, host := s.host.(receivedPacket := None))
        else 
            s' == s.(nextActionIndex := 2)
    }
    
    predicate HostNextIgnoreUnsendableProcess(s:LScheduler, s':LScheduler, ios:seq<LIoOp<EndPoint, seq<byte>>>)
    {
        s.nextActionIndex == 1
     && IgnoreSchedulerUpdate(s, s')
     && IosReflectIgnoringUnParseable(s, ios)
    }
    
    predicate HostNextIgnoreUnsendable(s:LScheduler, s':LScheduler, ios:seq<LIoOp<EndPoint, seq<byte>>>)
    {
        HostNextIgnoreUnsendableReceive(s, s', ios) || HostNextIgnoreUnsendableProcess(s, s', ios)
    }
}
