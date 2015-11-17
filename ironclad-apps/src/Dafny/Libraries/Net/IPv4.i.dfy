//-<NuBuild BasmEnableSymdiff true />
include "../Util/bytes_and_words.s.dfy"
include "../Util/integer_sequences.i.dfy"
include "../Math/power2.i.dfy"
include "../../Drivers/Network/Intel/driver.i.dfy"
include "ethernet.i.dfy"
include "InternetChecksum.i.dfy"

//

//

function method {:opaque} Serialize16(Value:int) : seq<int>
    requires Word16(Value);
    ensures IsByteSeqOfLen(Serialize16(Value), 2);
{
    lemma_2toX();

    [Value / 0x100] + [Value % 0x100]
}

function method {:opaque} Deserialize16(Bytes:seq<int>) : int
    requires IsByteSeq(Bytes);
    requires |Bytes| == 2;
    ensures Word16(Deserialize16(Bytes));
{
    lemma_2toX();

    Bytes[0] * 0x100 + Bytes[1]
}


//-
//- Define an IPv4 Address.
//-
datatype IPv4Address = IPv4AddressBuilder(bytes:seq<int>);
function ValidIPv4Address(Addr:IPv4Address) : bool
{
    //-
    //- Technically all 2^32 are valid, although some are reserved.
    //-
    IsByteSeqOfLen(Addr.bytes, 4)
}

//-
//- IPv4 Header Format:
//-
//-          Byte 0           Byte 1           Byte 2           Byte 3
//-    ---------------------------------------------------------------------
//-    | Vers / Hdr Len |   DSCP / ECN   |           Total Length          |
//-    ---------------------------------------------------------------------
//-    |         Identification          |       Flags / Frag Offset       |
//-    ---------------------------------------------------------------------
//-    |  Time To Live  |    Protocol    |         Header Checksum         |
//-    ---------------------------------------------------------------------
//-    |                         Source IP Address                         |
//-    ---------------------------------------------------------------------
//-    |                      Destination IP Address                       |
//-    ---------------------------------------------------------------------
//-
//-    Version = 4 and Header Length = 5 (32-bit words), so first byte = 0x45.
//-    DSCP / ECN we can leave at zero.
//-    Total Length = Header + Payload Length in bytes.  We need to set this.
//-    Identification should be unique per packet, but can be ignored if we never fragment?
//-    Flags / Fragment Offset we can leave at zero.
//-    Time To Live (TTL) is really a hop count, we can use anything reasonable (e.g. 0x80).
//-    Protocol could be passed to us, or can be hard-wired to UDP (0x11).
//-    Header checksum needs to be calculated properly.
//-    Source IP Address could be passed to us or can be hard-wired.
//-    Destination IP Address should be passed to us.
//-

//-
//- Send the given Data via IPv4 to the given destination ethernet address and IPv4 address.
//- Use the given Protocol value as the number for the contained protocol.
//- Use the given Headers as the header for the contained prtocol.
//- Use the given source IPv4 address as the source.
//-
//- Note: Caller is responsible for ensuring that the provided destination IPv4 address is valid for the station with the provided ethernet address.
//-


method{:dafnycc_conservative_seq_triggers} compute_header(TotalLength:int, Id:int, Protocol:int, Checksum:int, IPSource:IPv4Address, IPDest:IPv4Address) returns (IpHeader:seq<int>)
    requires 0 <= TotalLength <= 1500;  
    requires IsByte(Id);
    requires IsByte(Protocol);
    requires Word16(Checksum);
    requires ValidIPv4Address(IPSource);
    requires ValidIPv4Address(IPDest);
    requires public(TotalLength);
    requires public(Id);
    requires public(Protocol);
    requires public(Checksum);
    requires public(IPSource);
    requires public(IPDest);
    ensures  IsByteSeqOfLen(IpHeader,20);
    ensures  public(IpHeader);
{    
    lemma_2toX();
    IpHeader := [0x45]  //- Version and Header Length.
        + [0x00]  //- DSCP bits and ECN bit.
        + Serialize16(TotalLength)  //- Total Length.
        + Serialize16(Id)  //- Identification.
        + [0x0]  //- First byte of Flags and Fragement Offset.
        + [0x0]  //- Second byte of Flags and Fragement Offset.
        + [0x80]  //- Time to live (TTL).
        + [Protocol]  //- Higher-level Protocol.
        + Serialize16(Checksum)  //- IP Header Checksum.
        + IPSource.bytes  //- Source IP address.
        + IPDest.bytes;  //- Destination IP address.
}

method{:dafnycc_conservative_seq_triggers} IPv4Send(state:network_state, EtherDest:ethernet_addr, IPSource:IPv4Address, IPDest:IPv4Address, Protocol:int, Headers:seq<int>, Data:seq<int>)
    returns (new_state:network_state)
    requires valid_network_state(state);
    requires ValidIPv4Address(IPSource);
    requires ValidIPv4Address(IPDest);
    requires valid_ethernet_addr(EtherDest);
    requires IsByte(Protocol);
    requires |Headers| + |Data| <= 1480;  
    requires IsByteSeq(Headers);
    requires IsByteSeq(Data);
    requires public(state);
    requires public(EtherDest);
    requires public(IPSource);
    requires public(IPDest);
    requires public(Protocol);
    requires public(Headers);
    requires public(Data);
    ensures  valid_network_state(new_state);
    ensures  public(new_state);
{
    lemma_2toX();

    var TotalLength := 20 + |Headers| + |Data|;
    var Id := 0;

    //-
    //- First create the header over which to calculate the checksum.
    //-
    var Checksum := 0;
    var IpHeader := compute_header(TotalLength, Id, Protocol, Checksum, IPSource, IPDest); 

    //-
    //- Re-create the header using the valid checksum.
    //-
    Checksum := InternetChecksum(IpHeader);
    IpHeader := compute_header(TotalLength, Id, Protocol, Checksum, IPSource, IPDest); 

    new_state := EtherSend(state, EtherDest, IpHeader + Headers, Data);
}


method{:dafnycc_conservative_seq_triggers} IPv4Receive(state:network_state)
    returns (Success:bool, new_state:network_state, EtherSource:ethernet_addr, IPSource:IPv4Address, IPDest:IPv4Address, Protocol:int, Data:seq<int>)
    requires valid_network_state(state);
    requires public(state);
    ensures valid_network_state(new_state);
    ensures Success ==> valid_ethernet_addr(EtherSource);
    ensures Success ==> ValidIPv4Address(IPSource);
    ensures Success ==> ValidIPv4Address(IPDest);
    ensures Success ==> IsByte(Protocol);
    ensures Success ==> IsByteSeq(Data);
    ensures Success ==> |Data| <= 1480;
    ensures public(new_state);
    ensures public(Success);
    ensures public(EtherSource);
    ensures public(IPSource);
    ensures public(IPDest);
    ensures public(Protocol);
    ensures public(Data);
{
    lemma_2toX();

    var EtherType:seq<int>;

    Protocol := 0;
    IPSource := IPv4AddressBuilder([0, 0, 0, 0]);
    IPDest := IPv4AddressBuilder([0, 0, 0, 0]);

    Success, new_state, EtherSource, EtherType, Data := EtherReceive(state);

    if (Success)
    {
        if (EtherType[0] != 0x08 || EtherType[1] != 0x00)
        {
            //- Wrong Ethernet type field for IPv4.
            Success := false;
            //-debug_print(0x90, 0xdead3001);
        }
        else if (|Data| < 20)
        {
            //- Received data too short to contain an IPv4 header.
            Success := false;
            //-debug_print(0x90, 0xdead3002);
        }
        else
        {
            var Checksum := InternetChecksum(Data[0..20]);
            if (Checksum != 0)
            {
                //- Checksum failed, packet corrupted.
                Success := false;
                //-debug_print(0x90, 0xdead3003);
            }
            else if (Data[0] != 0x45)
            {
                //- Not an option-less IPv4 header.
                Success := false;
                //-debug_print(0x90, 0xdead3004);
            }
            else
            {
                var TotalLength := Deserialize16(Data[2..4]);
                if (TotalLength < 20)
                {
                    //- TotalLength field is bogus (too small to include IPv4 header).
                    Success := false;
                    //-debug_print(0x90, 0xdead3005);
                }
                else if (TotalLength > |Data|)
                {
                    //- Not enough data to hold packet described by IPv4 header.
                    Success := false;
                    //-debug_print(0x90, 0xdead3006);
                }
                else
                {
                    Protocol := Data[9];
                    IPSource := IPv4AddressBuilder(Data[12..16]);
                    IPDest := IPv4AddressBuilder(Data[16..20]);

                    //-
                    //- Everything looks good.
                    //- Strip off the IPv4 header and trim to TotalLength.
                    //-
                    Data := Data[20..TotalLength];
                }
            }
        }
    }
//-    else
//-    {
//-        debug_print(0x90, 0xdead3000);
//-    }
}
