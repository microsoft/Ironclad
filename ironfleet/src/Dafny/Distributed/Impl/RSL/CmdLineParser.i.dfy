include "../Common/CmdLineParser.i.dfy"
include "CPaxosConfiguration.i.dfy"

module PaxosCmdLineParser_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened CmdLineParser_i
import opened Common__NetClient_i
import opened LiveRSL__CPaxosConfiguration_i

function paxos_config_parsing(args:seq<seq<uint16>>) : CPaxosConfiguration
{
  if args != [] && |args[1..]| % 2 == 0 then 
    var (ok, endpoints) := parse_end_points(args[1..]);
    CPaxosConfiguration(endpoints)
  else 
    CPaxosConfiguration([])
}

function paxos_parse_id(ip:seq<uint16>, port:seq<uint16>) : EndPoint
{
  var (ok, ep) := parse_end_point(ip, port);
  ep
}

function paxos_cmd_line_parsing(env:HostEnvironment) : (CPaxosConfiguration, EndPoint)
  reads env
  reads env.constants
{
  var args := resolve_cmd_line_args(env.constants.CommandLineArgs());
  if |args| < 2 then
    (CPaxosConfiguration([]), EndPoint([0,0,0,0], 0))
  else
    var penultimate_arg, final_arg := args[|args|-2], args[|args|-1];
    var config := paxos_config_parsing(args[..|args|-2]);
    var me := paxos_parse_id(penultimate_arg, final_arg);
    (config, me)
}

method parse_cmd_line(ghost env:HostEnvironment) returns (ok:bool, config:CPaxosConfiguration, my_index:uint64)
  requires HostEnvironmentIsValid(env)
  ensures ok ==> CPaxosConfigurationIsValid(config)
  ensures ok ==> |config.replica_ids| > 0
  ensures ok ==> 0 <= my_index as int < |config.replica_ids|
  ensures var (config', my_ep') := paxos_cmd_line_parsing(env);
          ok ==> config == config' && config.replica_ids[my_index] == my_ep'
{
  ok := false;
  var num_args := HostConstants.NumCommandLineArgs(env);
  var args := collect_cmd_line_args(env);
  assert args == env.constants.CommandLineArgs();

  args := resolve_cmd_line_args(args);

  if |args| < 4 || |args| % 2 != 1 {
    print "Incorrect number of command line arguments.\n";
    print "Expected: ./Main.exe [name:port]+ [name:port]\n";
    print "      or: ./Main.exe [IP port]+ [IP port]\n";
    print "  where the final argument is one of the IP-port pairs provided earlier \n";
    return;
  }

  var tuple1 := parse_end_points(args[1..|args|-2]);
  ok := tuple1.0;
  var endpoints := tuple1.1;
  if !ok {
    print "Error encountered while processing command-line arguments";
    return;
  }

  if |endpoints| >= 0xffff_ffff_ffff_ffff {
    print "Internal error: impossibly many endpoints.\n";
    ok := false;
    return;
  }

  var tuple2 := parse_end_point(args[|args|-2], args[|args|-1]);
  ok := tuple2.0;
  if !ok {
    print "Error: Could not parse command-line arguments.\n";
    return;
  }

  var unique := test_unique'(endpoints);
  if !unique {
    print "Error: Each endpoint must be unique.\n";
    ok := false;
    return;
  }

  config := CPaxosConfiguration(endpoints);
  lemma_MinQuorumSizeLessThanReplicaCount(config);

  ok, my_index := CGetReplicaIndex(tuple2.1, config);
  if !ok {
    print "Error: Could not find local endpoint (last command-line endpoint) in list of preceding endpoints\n";
    return;
  }

  ghost var ghost_tuple := paxos_cmd_line_parsing(env);
  ghost var config', my_ep' := ghost_tuple.0, ghost_tuple.1;
  assert endpoints == config'.replica_ids;
  assert config == config';
  assert config.replica_ids[my_index] == my_ep';
}

}
