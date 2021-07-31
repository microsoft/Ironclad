include "../Common/CmdLineParser.i.dfy"

module LockCmdLineParser_i {

import opened Native__NativeTypes_s
import opened Native__Io_s
import opened Environment_s
import opened CmdLineParser_i
import opened Common__NetClient_i
import opened Common__SeqIsUniqueDef_i

function lock_config_parsing(args:seq<seq<byte>>) : seq<EndPoint>
{
  var (ok, endpoints) := parse_end_points(args);
  if ok && |endpoints| > 0 && |endpoints| < 0x1_0000_0000_0000_0000 then
    endpoints 
  else 
    []
}

function lock_cmd_line_parsing(env:HostEnvironment) : (seq<EndPoint>, EndPoint)
  reads env
  reads env.constants
{
  var args := env.constants.CommandLineArgs();
  if |args| < 1 then
    ([], EndPoint([])) 
  else
    var final_arg := args[|args|-1];
    var config := lock_config_parsing(args[..|args|-1]);
    var (_, me) := parse_end_point(final_arg);
    (config, me)
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

method ParseCmdLine(ghost env:HostEnvironment) returns (ok:bool, host_ids:seq<EndPoint>, my_index:uint64)
  requires HostEnvironmentIsValid(env)
  ensures ok ==> |host_ids| > 0
  ensures ok ==> 0 <= my_index as int < |host_ids|
  ensures var (host_ids', my_ep') := lock_cmd_line_parsing(env);
          ok ==> host_ids == host_ids' && host_ids[my_index] == my_ep'
  ensures var args := env.constants.CommandLineArgs();
          ok ==> |args| > 0 && host_ids[my_index] == EndPoint(args[|args|-1])
  ensures ok ==> SeqIsUnique(host_ids)
{
  ok := false;
  var num_args := HostConstants.NumCommandLineArgs(env);
  var args := collect_cmd_line_args(env);
  assert args == env.constants.CommandLineArgs();

  if |args| < 1 {
    print "Incorrect number of command line arguments.\n";
    print "Expected: ./Main.exe [public_key]+ [public_key]\n";
    print "  where the final argument is one of the public keys provided earlier \n";
    return;
  }

  var tuple1 := parse_end_points(args[..|args|-1]);
  ok := tuple1.0;
  var endpoints := tuple1.1;
  if !ok || |endpoints| == 0 || |endpoints| >= 0x1_0000_0000_0000_0000 {
    ok := false;
    return;
  }

  var tuple2 := parse_end_point(args[|args|-1]);
  ok := tuple2.0;
  if !ok {
    return;
  }

  var unique := test_unique(endpoints);
  if !unique {
    ok := false;
    return;
  }

  ok, my_index := GetHostIndex(tuple2.1, endpoints);
  if !ok {
    return;
  }
  host_ids := endpoints;
  var me := endpoints[my_index];

  ghost var ghost_tuple := lock_cmd_line_parsing(env);
  ghost var config', my_ep' := ghost_tuple.0, ghost_tuple.1;
  assert endpoints == config';
  assert me == my_ep';
}

}
