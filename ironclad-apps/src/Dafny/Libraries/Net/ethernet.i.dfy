//-<NuBuild BasmEnableSymdiff true />
include "../Util/integer_sequences.i.dfy"
include "../../Drivers/Network/Intel/driver.i.dfy"

//-
//- Ethernet-level interface to the network.
//-

//-
//- Send the given Headers and Data to the given ethernet destination address.
//-
method EtherSend(state:network_state, EtherDest:ethernet_addr, Headers:seq<int>, Data:seq<int>)
    returns (new_state:network_state)
    requires valid_network_state(state);
    requires valid_ethernet_addr(EtherDest);
    requires IsByteSeq(Headers);
    requires IsByteSeq(Data);
    requires |Headers| + |Data| <= 1500;
    requires public(state);
    requires public(EtherDest);
    requires public(Headers);
    requires public(Data);
    ensures valid_network_state(new_state);
    ensures public(new_state);
{
    lemma_2toX();

    //-
    //- Create an Ethernet header to prepend to the caller's headers and data.
    //-
    var EtherSource := my_ethernet_addr();
    var EtherType := [0x08, 0x00];  //- Fix the type to be IPv4
                                    
    var EtherHeader := EtherDest.bytes + EtherSource.bytes + EtherType;

    assert |EtherHeader| == 14;

//-    assert Data == old(Data);
//-    assert app_approves_disclosure(left(UserData), right(UserData), 1500);

    new_state := NetIfSend(state, EtherHeader + Headers, Data);
}

method EtherReceive(state:network_state)
    returns (Success:bool, new_state:network_state, EtherSource:ethernet_addr, EtherType:seq<int>, Data:seq<int>)
//-    requires net_init;
    requires valid_network_state(state);
    requires public(state);
    ensures valid_network_state(new_state);
    ensures Success ==> valid_ethernet_addr(EtherSource);
    ensures Success ==> IsByteSeq(EtherType);
    ensures Success ==> |EtherType| == 2;
    ensures Success ==> IsByteSeq(Data);
    ensures Success ==> 46 <= |Data| <= 1500;
    ensures public(Success);
    ensures public(new_state);
    ensures public(EtherSource);
    ensures public(EtherType);
    ensures public(Data);
{
    lemma_2toX();

    EtherSource := ethernet_addr_builder([]); // TODO: dafnycc: had to add this line because dafnycc doesn't handle returning uninitialized variables.
    EtherType := [0x00, 0x00];

    Success, new_state, Data := NetIfReceive(state);

    if (Success)
    {
        if (|Data| < 60) {
            //-
            //- Too short for an Ethernet packet.
            //-
            Success := false;
            //-debug_print(0x90, 0xdead2001);

        } else {
            //
            
            
            //
            var EtherDest := ethernet_addr_builder(Data[0..6]);
            assert valid_ethernet_addr(EtherDest);

            EtherSource := ethernet_addr_builder(Data[6..12]);
            assert valid_ethernet_addr(EtherSource);

            EtherType := Data[12..14];

            //-
            //- Remove the Ethernet Header and trim the data length to a maximum of 1500 bytes.
            //-
            var Length := |Data| - 14;
            if (Length > 1500)
            {
                Length := 1500;
            }
            Data := Data[14..14 + Length];
        }
    }
    else
    {
            //-debug_print(0x90, 0xdead2000);
    }
}
