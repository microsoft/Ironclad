//-<NuBuild BasmEnableSymdiff true />
include "../Util/bytes_and_words.s.dfy"
include "../Util/integer_sequences.i.dfy"
include "../Math/power2.i.dfy"
include "IPv4.i.dfy"


//-
//- UDP Header Format:
//-
//-          Byte 0           Byte 1           Byte 2           Byte 3
//-    ---------------------------------------------------------------------
//-    |           Source Port           |        Destination Port         |
//-    ---------------------------------------------------------------------
//-    |             Length              |            Checksum             |
//-    ---------------------------------------------------------------------
//-
//-    Source Port is the sender's 16 bit port number.
//-    Destination Port is the receiver's 16 bit port number.
//-    Length = UDP Header + Payload Length in bytes.
//-    Checksum is the standard Internet Checksum computed over the Pseudo Header and data.
//-


//-
//- Send the given Data via UDP to the given destination ethernet address, IPv4 address, and UDP port.
//- Use the given source IPv4 address and UDP port as the source.
//-
//- Note: Caller is responsible for ensuring that the provided destination IPv4 address is valid for the station with the provided ethernet address.
//-
method{:dafnycc_conservative_seq_triggers} UdpSend(state:network_state, EtherDest:ethernet_addr, IPSource:IPv4Address, IPDest:IPv4Address, SourcePort:int, DestPort:int, Data:seq<int>)
    returns (new_state:network_state)
    requires valid_network_state(state);
    requires ValidIPv4Address(IPSource);
    requires ValidIPv4Address(IPDest);
    requires valid_ethernet_addr(EtherDest);
    requires Word16(SourcePort);
    requires Word16(DestPort);
    requires |Data| <= 1472;  
    requires IsByteSeq(Data);
    requires public(state);
    requires public(EtherDest);
    requires public(IPSource);
    requires public(IPDest);
    requires public(SourcePort);
    requires public(DestPort);
    requires public(Data);
    ensures valid_network_state(new_state);
    ensures public(new_state);
{
    lemma_2toX();

    var Length := 8 + |Data|;

    var PseudoHeader := IPSource.bytes + IPDest.bytes + [0] + [17] + Serialize16(Length);

    var Checksum := 0;
    var UdpHeader:seq<int> := Serialize16(SourcePort)
        + Serialize16(DestPort)
        + Serialize16(Length)
        + Serialize16(Checksum);

    Checksum := InternetChecksum(PseudoHeader + UdpHeader + Data);
    if (Checksum == 0)
    {
        Checksum := 0xffff;
    }

    UdpHeader := Serialize16(SourcePort)
        + Serialize16(DestPort)
        + Serialize16(Length)
        + Serialize16(Checksum);

    new_state := IPv4Send(state, EtherDest, IPSource, IPDest, 17, UdpHeader, Data);
}

method{:dafnycc_conservative_seq_triggers} UdpReceive(state:network_state)
    returns (Success:bool, new_state:network_state, EtherSource:ethernet_addr, IPSource:IPv4Address, IPDest:IPv4Address, SourcePort:int, DestPort:int, Data:seq<int>)
    requires valid_network_state(state);
    requires public(state);
    ensures valid_network_state(new_state);
    ensures Success ==> valid_ethernet_addr(EtherSource);
    ensures Success ==> ValidIPv4Address(IPSource);
    ensures Success ==> ValidIPv4Address(IPDest);
    ensures Success ==> Word16(SourcePort);
    ensures Success ==> Word16(DestPort);
    ensures Success ==> IsByteSeq(Data);
    ensures Success ==> |Data| <= 1472;
    ensures public(Success);
    ensures public(new_state);
    ensures public(EtherSource);
    ensures public(IPSource);
    ensures public(IPDest);
    ensures public(SourcePort);
    ensures public(DestPort);
    ensures public(Data);
{
    lemma_2toX();

    var Protocol:int;

    SourcePort := 0;
    DestPort := 0;

    Success, new_state, EtherSource, IPSource, IPDest, Protocol, Data := IPv4Receive(state);

    if (Success)
    {
        if (Protocol != 17)
        {
            //- Not a UDP packet.
            Success := false;
        }
        else if (|Data| < 8 )
        {
            //- Received data is too short to contain a UDP header.
            Success := false;
        }
        else
        {
            var Length:int := Deserialize16(Data[4..6]);
            if (Length < 8)
            {
                //- Length field is bogus (too small to include UDP header).
                Success := false;
            }
            else if (Length > |Data|)
            {
                //- Not enough data to hold packet described by IPv4 header.
                Success := false;
            }
            else
            {
                var PseudoHeader := IPSource.bytes + IPDest.bytes + [0] + [17] + Serialize16(Length);
                var Checksum:int := InternetChecksum(PseudoHeader + Data);
                if (Checksum != 0)
                {
                    //- Checksum failed, packet corrupted.
                    Success := false;
                }
                else
                {
                    SourcePort := Deserialize16(Data[0..2]);
                    DestPort := Deserialize16(Data[2..4]);

                    //-
                    //- Everything looks good.
                    //- Strip off the UDP header and trim to Length.
                    //-
                    Data := Data[8..Length];
                }
            }
        }
    }
}
