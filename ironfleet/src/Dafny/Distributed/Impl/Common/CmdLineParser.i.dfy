include "../../Common/Native/Io.s.dfy"
include "../../../Libraries/Math/power.i.dfy"
include "SeqIsUniqueDef.i.dfy"
include "UdpClient.i.dfy"

module CmdLineParser_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Math__power_s
import opened Common__SeqIsUniqueDef_i
import opened Common__UdpClient_i

function method ascii_to_int(short:uint16) : (bool, byte)
  ensures var tuple := ascii_to_int(short);
          tuple.0 ==> 0 <= tuple.1 <= 9
{
  if 48 <= short <= 57 then
    (true, (short - 48) as byte)
  else 
    (false, 0)
}

method power10(e:nat) returns (val:int)
  ensures val == power(10, e)
{
  reveal power();
  if e == 0 {
    return 1;
  } else {
    var tmp := power10(e-1);
    return 10 * tmp;
  }
}

function method shorts_to_bytes(shorts:seq<uint16>) : (bool, seq<byte>)
{
  if |shorts| == 0 then (true, [])
  else 
    var tuple := shorts_to_bytes(shorts[1..]);
    var ok, rest := tuple.0, tuple.1;
    var tuple' := ascii_to_int(shorts[0]);
    var ok', a_byte := tuple'.0, tuple'.1;
    if ok && ok' then
      (true, [a_byte] + rest)
    else
      (false, [])
}

function method bytes_to_decimal(bytes:seq<byte>) : nat
{
  if |bytes| == 0 then 0
  else (bytes[|bytes|-1] as int) + 10 * bytes_to_decimal(bytes[0..|bytes|-1])
}

function method shorts_to_nat(shorts:seq<uint16>) : (bool, int)
{
  if |shorts| == 0 then (false, 0)
  else 
    var tuple := shorts_to_bytes(shorts);
    var ok, bytes := tuple.0, tuple.1;
    if !ok then (false, 0)
    else
      (true, bytes_to_decimal(bytes))
}

function method shorts_to_byte(shorts:seq<uint16>) : (bool, byte)
{
  var tuple := shorts_to_nat(shorts);
  var ok, val := tuple.0, tuple.1;
  if 0 <= val < 0x100 then
    (true, val as byte)
  else
    (false, 0)
}

function method shorts_to_uint16(shorts:seq<uint16>) : (bool, uint16)
{
  var tuple := shorts_to_nat(shorts);
  var ok, val := tuple.0, tuple.1;
  if 0 <= val < 0x10000 then
    (true, val as uint16)
  else
    (false, 0)
}

function method shorts_to_uint32(shorts:seq<uint16>) : (bool, uint32)
{
  var tuple := shorts_to_nat(shorts);
  var ok, val := tuple.0, tuple.1;
  if 0 <= val < 0x1_0000_0000 then
    (true, val as uint32)
  else
    (false, 0)
}

function method is_ascii_period(short:uint16) : (bool)
{
  short == 46
}

function method parse_ip_addr_helper(ip_shorts:seq<uint16>, current_octet_shorts:seq<uint16>) : (bool, seq<byte>)
{
  if |ip_shorts| == 0 then 
    var tuple := shorts_to_byte(current_octet_shorts);
    var okay, b := tuple.0, tuple.1;
    if !okay then (false, []) else (true, [b])
  else
    if is_ascii_period(ip_shorts[0]) then
      var tuple := shorts_to_byte(current_octet_shorts);
      var okay, b := tuple.0, tuple.1;
      if !okay then
        (false, [])
      else
        var tuple' := parse_ip_addr_helper(ip_shorts[1..], []);
        var ok, ip_bytes := tuple'.0, tuple'.1;
        if !ok then
          (false, [])
        else
          (true, [b] + ip_bytes)
    else
      parse_ip_addr_helper(ip_shorts[1..], current_octet_shorts + [ip_shorts[0]])
}

function method parse_ip_addr(ip_shorts:seq<uint16>) : (bool, seq<byte>)
{
  var tuple := parse_ip_addr_helper(ip_shorts, []);
  var ok, ip_bytes := tuple.0, tuple.1;
  if ok && |ip_bytes| == 4 then
    (true, ip_bytes)
  else 
    (false, [])
}


function method {:opaque} parse_end_point(ip_shorts:seq<uint16>, port_shorts:seq<uint16>) : (bool, EndPoint)
  ensures var tuple := parse_end_point(ip_shorts,port_shorts);
          var ok, ep := tuple.0, tuple.1;
          ok ==> EndPointIsValidIPV4(ep)
{
  var tuple := parse_ip_addr(ip_shorts);
  var okay, ip_bytes := tuple.0, tuple.1;

  if !okay then 
    //print("Failed to parse_ip_addr\n");
    (false, EndPoint([0,0,0,0], 0))
  else
    var tuple' := shorts_to_uint16(port_shorts);
    var okay', port := tuple'.0, tuple'.1;
    if !okay' then 
      //print("Failed to parse port\n");
      (false, EndPoint([0,0,0,0], 0))
    else
      (true, EndPoint(ip_bytes, port))

}

method test_unique'(endpoints:seq<EndPoint>) returns (unique:bool)
  ensures unique <==> SeqIsUnique(endpoints)
{
  unique := true;

  var i := 0;

  while i < |endpoints| 
    invariant 0 <= i <= |endpoints|
    invariant forall j,k :: 0 <= j < |endpoints| && 0 <= k < i && j != k 
                      ==> endpoints[j] != endpoints[k]
  {
    var j := 0;
    while j < |endpoints|
      invariant 0 <= j <= |endpoints|
      invariant forall k :: 0 <= k < j && k != i ==> endpoints[i] != endpoints[k]
    {
      if i != j && endpoints[i] == endpoints[j] {
        unique := false;
        reveal_SeqIsUnique();
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  reveal SeqIsUnique();
}

function method parse_end_points(args:seq<seq<uint16>>) : (bool, seq<EndPoint>)
  requires |args| % 2 == 0
  ensures var (ok, endpoints) := parse_end_points(args);
          ok ==> (forall e :: e in endpoints ==> EndPointIsValidIPV4(e))
{
  if |args| == 0 then
    (true, [])
  else
    var (ok1, ep) := parse_end_point(args[0], args[1]);
    var (ok2, rest) := parse_end_points(args[2..]);

    if !(ok1 && ok2) then
      (false, [])
    else 
      (true, [ep] + rest)
}

method collect_cmd_line_args(ghost env:HostEnvironment) returns (args:seq<seq<uint16>>)
  requires HostEnvironmentIsValid(env)
  ensures  |env.constants.CommandLineArgs()| == |args|
  ensures  forall i :: 0 <= i < |env.constants.CommandLineArgs()| ==> args[i] == env.constants.CommandLineArgs()[i]
{
  var num_args := HostConstants.NumCommandLineArgs(env);
  var i := 0;
  args := [];

  while (i < num_args)
    invariant 0 <= i <= num_args
    invariant |env.constants.CommandLineArgs()[0..i]| == |args|
    invariant forall j :: 0 <= j < i ==> args[j] == env.constants.CommandLineArgs()[j];
  {
    var arg := HostConstants.GetCommandLineArg(i as uint64, env);
    args := args + [arg[..]];
    i := i + 1;
  }
}

}
