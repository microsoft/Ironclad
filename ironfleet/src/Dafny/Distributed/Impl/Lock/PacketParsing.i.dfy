include "../Common/GenericMarshalling.i.dfy"
include "../Common/UdpClient.i.dfy"
include "Message.i.dfy"

module PacketParsing_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened Logic__Option_i
import opened Environment_s
import opened Common__GenericMarshalling_i
import opened Common__UdpClient_i
import opened Types_i
import opened Message_i

predicate UdpPacketBound(data:seq<byte>) 
{
    |data| < MaxPacketSize()
}

////////////////////////////////////////////////////////////////////
//    Grammars for the Lock messages
////////////////////////////////////////////////////////////////////

function method CMessageTransferGrammar() : G { GUint64 }
function method CMessageLockedGrammar() : G { GUint64 }

function method CMessageGrammar() : G 
{ 
    GTaggedUnion([CMessageTransferGrammar(), CMessageLockedGrammar()])
}

////////////////////////////////////////////////////////////////////
//    Parsing
////////////////////////////////////////////////////////////////////

function method ParseCMessageTransfer(val:V) : CMessage
    requires ValInGrammar(val, CMessageTransferGrammar());
{
    CTransfer(val.u)
}

function method ParseCMessageLocked(val:V) : CMessage
    requires ValInGrammar(val, CMessageLockedGrammar());
{
    CLocked(val.u)
}

function method ParseCMessage(val:V) : CMessage
    requires ValInGrammar(val, CMessageGrammar());
{
    if val.c == 0 then
        ParseCMessageTransfer(val.val)
    else
        ParseCMessageLocked(val.val)
}

function DemarshallData(data:seq<byte>) : CMessage
{
    if Demarshallable(data, CMessageGrammar()) then
        var val := DemarshallFunc(data, CMessageGrammar());
        ParseCMessage(val)
    else
        CInvalid()
}

method DemarshallDataMethod(data:array<byte>) returns (msg:CMessage)
    requires data.Length < 0x1_0000_0000_0000_0000;
    ensures  msg == DemarshallData(data[..]);
//    ensures  if Demarshallable(data[..], msg_grammar) then 
//                msg == PaxosDemarshallData(data[..]) 
//             else msg.CMessage_Invalid?;
//    ensures  CMessageIs64Bit(msg);
{
    var success, val := Demarshall(data, CMessageGrammar());
    if success {
        //assert ValInGrammar(val, msg_grammar);
        msg := ParseCMessage(val);
        assert !msg.CInvalid?;
    } else {
        msg := CInvalid();
    }
}



////////////////////////////////////////////////////////////////////
//    Marshalling
////////////////////////////////////////////////////////////////////

method MarshallMessageTransfer(c:CMessage) returns (val:V)
    requires c.CTransfer?;
    ensures  ValInGrammar(val, CMessageTransferGrammar());
    ensures  ValidVal(val);
    ensures  ParseCMessageTransfer(val) == c;
    ensures  SizeOfV(val) < MaxPacketSize();
{
    val := VUint64(c.transfer_epoch);
}

method MarshallMessageLocked(c:CMessage) returns (val:V)
    requires c.CLocked?;
    ensures  ValInGrammar(val, CMessageLockedGrammar());
    ensures  ValidVal(val);
    ensures  ParseCMessageLocked(val) == c;
    ensures  SizeOfV(val) < MaxPacketSize();
{
    val := VUint64(c.locked_epoch);
}

method MarshallMessage(c:CMessage) returns (val:V)
    requires !c.CInvalid?;
    ensures  ValInGrammar(val, CMessageGrammar());
    ensures  ValidVal(val);
    ensures  ParseCMessage(val) == c;
    ensures  SizeOfV(val) < MaxPacketSize();
{
    if c.CTransfer? {
        var msg := MarshallMessageTransfer(c);
        val := VCase(0, msg);
    } else if c.CLocked? {
        var msg := MarshallMessageLocked(c);
        val := VCase(1, msg);
    } else {
        assert false;       // Provably will not reach here
    }
}

method MarshallLockMessage(msg:CMessage) returns (data:array<byte>)
    requires !msg.CInvalid?;
    ensures fresh(data);
    ensures UdpPacketBound(data[..]);
    ensures DemarshallData(data[..]) == msg;
{
    var val := MarshallMessage(msg);
    data := Marshall(val, CMessageGrammar());
}

////////////////////////////////////////////////////////////////////
//    Packet translation 
////////////////////////////////////////////////////////////////////

function AbstractifyUdpPacket(udp:UdpPacket) : LockPacket
{
    LPacket(udp.dst, udp.src, AbstractifyCMessage(DemarshallData(udp.msg)))
}

predicate CLockPacketValid(p:CLockPacket)
{
       EndPointIsValidIPV4(p.src)
    && EndPointIsValidIPV4(p.dst)
    && !p.msg.CInvalid?
}

predicate OptionCLockPacketValid(opt_packet:Option<CLockPacket>)
{
    opt_packet.Some? ==> CLockPacketValid(opt_packet.v)
}

}

