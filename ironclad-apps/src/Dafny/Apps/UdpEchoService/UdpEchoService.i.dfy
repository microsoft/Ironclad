include "../../Drivers/Network/Intel/driver.i.dfy"
include "../../Libraries/Net/ethernet.i.dfy"
include "../../Libraries/Net/IPv4.i.dfy"
include "../../Libraries/Net/Udp.i.dfy"
include "../../Libraries/Util/integer_sequences.i.dfy"

//-
//- A simple UDP Echo Service.
//-

method DebugPrintSequence(Offset:int, Data:seq<int>)
    requires 0 <= Offset <= 160 - 16;
    requires IsByteSeq(Data);
    requires |Data| >= 0;
{
    var Index:int := 0;

    while (Index < |Data|)
        decreases |Data| - Index;
        invariant Index >= 0;
        invariant Index <= |Data|;
    {
        debug_print(Offset, Data[Index]);
        Index := Index + 1;
    }
}

method Main()
    returns (Result:int)
    ensures public(true);
{
    lemma_2toX();

    Result := 0;

    var NetUp, net_state := init_network_card();

    if NetUp {
        lemma_2toX();
        debug_print(0x90, 0xded0d0d0);

        var Success:bool := true;
        var EtherSource:ethernet_addr;
        var IPSource:IPv4Address;
        var IPDest:IPv4Address;
        var SourcePort:int;
        var DestPort:int;
        var Data:seq<int>;

        while (Success)
            invariant valid_network_state(net_state);
            invariant public(net_state);
            invariant public(Success);
            decreases *;
        {
            Success, net_state, EtherSource, IPSource, IPDest, SourcePort, DestPort, Data := UdpReceive(net_state);
            if (Success)
            {
                lemma_2toX();
            
//-                DebugPrintSequence(0x90, Data);
                debug_print(0x90, 0xdedadada);

                if (DestPort == 7)
                {
                    //-
                    //- Port 7 is the Echo Service port.
                    //- Echo the data received back to the sender.
                    //-              
                    net_state := UdpSend(net_state, EtherSource, IPDest, IPSource, DestPort, SourcePort, Data);
                }
            }
            else
            {
                Result := 0xdeadbeef;
                debug_print(0x90, 0xdeadbeef);
            }
        }
    } else {
        Result := 0xdeaddead;
        debug_print(0x90, 0xdeaddead);
    }
}
