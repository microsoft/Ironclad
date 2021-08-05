include "../../Common/Native/Io.s.dfy"
include "../../../Libraries/Math/power.i.dfy"
include "SeqIsUniqueDef.i.dfy"
include "NetClient.i.dfy"

module CmdLineParser_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Math__power_s
import opened Common__SeqIsUniqueDef_i
import opened Common__NetClient_i

function method parse_end_point(public_key:seq<byte>) : (bool, EndPoint)
  ensures var tuple := parse_end_point(public_key);
          var ok, ep := tuple.0, tuple.1;
          ok ==> EndPointIsValidPublicKey(ep)
{
  if |public_key| < 0x10_0000 then
    (true, EndPoint(public_key))
  else
    (false, EndPoint(public_key))
}

method test_unique(endpoints:seq<EndPoint>) returns (unique:bool)
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

function method parse_end_points(args:seq<seq<byte>>) : (bool, seq<EndPoint>)
  ensures var (ok, endpoints) := parse_end_points(args);
          ok ==> (forall e :: e in endpoints ==> EndPointIsValidPublicKey(e))
{
  if |args| == 0 then
    (true, [])
  else
    var (ok1, ep) := parse_end_point(args[0]);
    var (ok2, rest) := parse_end_points(args[1..]);

    if !(ok1 && ok2) then
      (false, [])
    else 
      (true, [ep] + rest)
}

method GetHostIndex(host:EndPoint, hosts:seq<EndPoint>) returns (found:bool, index:uint64)
  requires EndPointIsValidPublicKey(host)
  requires SeqIsUnique(hosts)
  requires |hosts| < 0x1_0000_0000_0000_0000
  requires forall h :: h in hosts ==> EndPointIsValidPublicKey(h)
  ensures  found ==> 0 <= index as int < |hosts| && hosts[index] == host
  ensures !found ==> !(host in hosts)
{
  var i:uint64 := 0;

  while i < (|hosts| as uint64)
    invariant i as int <= |hosts|;
    invariant forall j :: 0 <= j < i ==> hosts[j] != host;
  {
    if host == hosts[i] {
      found := true;
      index := i;
    
      calc ==> {
        true;
          { reveal_SeqIsUnique(); }
        forall j :: 0 <= j < |hosts| && j != i as int ==> hosts[j] != host;
      }

      return;
    }

    if i == (|hosts| as uint64) - 1 {
      found := false;
      return;
    }

    i := i + 1;
  }
  found := false;
}

}
