include "../Common/CmdLineParser.i.dfy"
include "../SHT/ConstantsState.i.dfy"

module ShtCmdLineParser_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened CmdLineParser_i
import opened SHT__ConstantsState_i
import opened Impl_Parameters_i
import opened Common__UdpClient_i
import opened Common__SeqIsUniqueDef_i
import opened Common__NodeIdentity_i

function method EndPointNull() : EndPoint { EndPoint([0, 0, 0, 0], 0) }

function ConstantsStateNull () : ConstantsState 
{
    ConstantsState(EndPointNull(), [], StaticParams())
}

function sht_config_parsing(args:seq<seq<uint16>>) : ConstantsState
{
    if args != [] && |args[1..]| % 2 == 0 then 
        var (ok, endpoints) := parse_end_points(args[1..]);
        ConstantsState(if |endpoints| > 0 then endpoints[0] else EndPointNull(), // Root is the first endpoint in the list
                       endpoints,
                       StaticParams())
    else 
        ConstantsStateNull()
}

function sht_parse_id(ip:seq<uint16>, port:seq<uint16>) : EndPoint
{
    var (ok, ep) := parse_end_point(ip, port);
    ep
}

function sht_cmd_line_parsing(env:HostEnvironment) : (ConstantsState, EndPoint)
    reads env;
    reads env.constants;
{
    var args := env.constants.CommandLineArgs();
    if |args| < 2 then
        (ConstantsStateNull(), EndPointNull()) 
    else
        var penultimate_arg, final_arg := args[|args|-2], args[|args|-1];
        var config := sht_config_parsing(args[..|args|-2]);
        var me := sht_parse_id(penultimate_arg, final_arg);
        (config, me)
}

method GetHostIndex(host:EndPoint, hosts:seq<EndPoint>) returns (found:bool, index:uint64)
    requires EndPointIsValidIPV4(host);
    requires SeqIsUnique(hosts);
    requires |hosts| < 0x1_0000_0000_0000_0000;
    requires forall h :: h in hosts ==> EndPointIsValidIPV4(h);
    ensures  found ==> 0 <= index as int < |hosts| && hosts[index] == host;
    ensures !found ==> !(host in hosts);
    ensures !found ==> !(AbstractifyEndPointToNodeIdentity(host) in AbstractifyEndPointsToNodeIdentities(hosts));
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

method parse_cmd_line(ghost env:HostEnvironment) returns (ok:bool, config:ConstantsState, my_index:uint64)
    requires HostEnvironmentIsValid(env);
    ensures ok ==> ConstantsStateIsValid(config);
    ensures ok ==> |config.hostIds| > 0;
    ensures ok ==> 0 <= my_index as int < |config.hostIds|;
    //ensures (config, my_index) == sht_cmd_line_parsing(env);
    ensures var (config', my_ep') := sht_cmd_line_parsing(env);
            ok ==> config == config' && config.hostIds[my_index] == my_ep';
{
    ok := false;
    var num_args := HostConstants.NumCommandLineArgs(env);
    if num_args < 4 || num_args % 2 != 1 {
        print "Incorrect number of command line arguments.\n";
        print "Expected: ./Main.exe [IP port]+ [IP port]\n";
        print "  where the final argument is one of the IP-port pairs provided earlier \n";
        print "Note that the first IP-port pair indicates the root identity\n";
        return;
    }

    var args := collect_cmd_line_args(env);
    assert args == env.constants.CommandLineArgs();
    var tuple1 := parse_end_points(args[1..|args|-2]);
    ok := tuple1.0;
    var endpoints := tuple1.1;
    if !ok || |endpoints| >= 0xffff_ffff_ffff_ffff {
        ok := false;
        return;
    }

    var tuple2 := parse_end_point(args[|args|-2], args[|args|-1]);
    ok := tuple2.0;
    if !ok {
        return;
    }

    var unique := test_unique'(endpoints);
    if !unique {
        ok := false;
        return;
    }

    ok, my_index := GetHostIndex(tuple2.1, endpoints);
    if !ok {
        return;
    }
    var root_identity := endpoints[0];
    var hosts := endpoints;
    var me := endpoints[my_index];

    config := ConstantsState(root_identity, hosts, StaticParams());

    ghost var ghost_tuple := sht_cmd_line_parsing(env);
    ghost var config', my_ep' := ghost_tuple.0, ghost_tuple.1;
    assert endpoints == config'.hostIds;
    assert config == config';
    assert me == my_ep';
}
}
