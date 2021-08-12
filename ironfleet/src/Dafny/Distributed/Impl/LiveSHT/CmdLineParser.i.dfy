include "../Common/CmdLineParser.i.dfy"
include "../SHT/ConstantsState.i.dfy"

module ShtCmdLineParser_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened CmdLineParser_i
import opened SHT__ConstantsState_i
import opened Impl_Parameters_i
import opened Common__NetClient_i
import opened Common__SeqIsUniqueDef_i
import opened Common__NodeIdentity_i

function EndPointNull () : EndPoint
{
  EndPoint([])
}

function ConstantsStateNull () : ConstantsState 
{
  ConstantsState(EndPointNull(), [], StaticParams())
}

function sht_cmd_line_parsing(args:seq<seq<byte>>) : ConstantsState
{
  var (ok, endpoints) := parse_end_points(args);
  if !ok then
    ConstantsStateNull()
  else
    ConstantsState(if |endpoints| > 0 then endpoints[0] else EndPointNull(), // Root is the first endpoint in the list
                   endpoints,
                   StaticParams())
}

function sht_parse_id(arg:seq<byte>) : EndPoint
{
  var (ok, ep) := parse_end_point(arg);
  ep
}

method GetHostIndex(host:EndPoint, hosts:seq<EndPoint>) returns (found:bool, index:uint64)
  requires EndPointIsValidPublicKey(host)
  requires SeqIsUnique(hosts)
  requires |hosts| < 0x1_0000_0000_0000_0000
  requires forall h :: h in hosts ==> EndPointIsValidPublicKey(h)
  ensures  found ==> 0 <= index as int < |hosts| && hosts[index] == host
  ensures !found ==> !(host in hosts)
  ensures !found ==> !(AbstractifyEndPointToNodeIdentity(host) in AbstractifyEndPointsToNodeIdentities(hosts))
{
  var i:uint64 := 0;
  lemma_AbstractifyEndPointsToNodeIdentities_properties(hosts);

  while i < |hosts| as uint64
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

    if i == |hosts| as uint64 - 1 {
      found := false;
      return;
    }

    i := i + 1;
  }
  found := false;
}

method parse_cmd_line(id:EndPoint, args:seq<seq<byte>>) returns (ok:bool, config:ConstantsState, my_index:uint64)
  requires EndPointIsValidPublicKey(id)
  ensures ok ==> && ConstantsStateIsValid(config)
                && 0 <= my_index as int < |config.hostIds|
                && config == sht_cmd_line_parsing(args)
                && config.hostIds[my_index] == id
{
  var tuple1 := parse_end_points(args);
  ok := tuple1.0;
  var endpoints := tuple1.1;
  if !ok || |endpoints| >= 0xffff_ffff_ffff_ffff {
    ok := false;
    return;
  }

  var unique := test_unique(endpoints);
  if !unique {
    ok := false;
    return;
  }

  ok, my_index := GetHostIndex(id, endpoints);
  if !ok {
    return;
  }
  var root_identity := endpoints[0];

  config := ConstantsState(root_identity, endpoints, StaticParams());
}
}
