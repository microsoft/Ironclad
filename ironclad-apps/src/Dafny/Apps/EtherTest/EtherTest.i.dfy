include "../../Drivers/Network/Intel/driver.i.dfy"
include "../../Libraries/Net/ethernet.i.dfy"
include "../../Libraries/Util/integer_sequences.i.dfy"

//-
//- Ethernet Test App.
//-

//-method DebugPrintSequence(Offset:int, Data:seq<int>)
//-    requires 0 <= Offset <= 160 - 16;
//-    requires IsByteSeq(Data);
//-    requires |Data| >= 0;
//-{
//-    var Index:int := 0;
//-
//-    while (Index < |Data|)
//-        decreases |Data| - Index;
//-        invariant Index >= 0;
//-        invariant Index <= |Data|;
//-    {
//-        debug_print(Offset, Data[Index]);
//-        Index := Index + 1;
//-    }
//-}

method GenerateSecret() returns (secret:int)
    ensures IsByte(secret);
{
    secret := 42;
}

method Main()
    returns (Result:int)
    ensures public(true);
{
    lemma_2toX();

    var NetUp, net_state := init_network_card();

    //-var my_secret := GenerateSecret();

    if NetUp {
        var Headers := [0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x20];
        var Data := [0x57, 0x6f, 0x72, 0x6c, 0x64, 0x21];

        //- This line fails SymDiff, as expected
        //-Data := Data + [my_secret];

        assert IsByteSeq(Headers);
        assert IsByteSeq(Data);

        debug_print(0x90, 0xded0d0d0);

        net_state := EtherSend(net_state, ethernet_addr_builder([0x60, 0x61, 0x62, 0x63, 0x64, 0x65]), Headers, Data);

        debug_print(0x90, 0xdedadada);
        Result := 0xdedadada;

    } else {
        Result := 0xdeaddead;
        debug_print(0x90, 0xdeaddead);
    }
}
