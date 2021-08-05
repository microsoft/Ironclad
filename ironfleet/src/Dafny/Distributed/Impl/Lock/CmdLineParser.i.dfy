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

method ParseCmdLine(id:EndPoint, args:seq<seq<byte>>)
  returns (ok:bool, host_ids:seq<EndPoint>, my_index:uint64)
  requires EndPointIsValidPublicKey(id)
  ensures ok ==> && 0 <= my_index as int < |host_ids|
                && host_ids == lock_config_parsing(args)
                && host_ids[my_index] == id
                && SeqIsUnique(host_ids)
{
  ok := false;

  var tuple1 := parse_end_points(args);
  ok := tuple1.0;
  if !ok {
    return;
  }
  host_ids := tuple1.1;
  if |host_ids| == 0 || |host_ids| >= 0x1_0000_0000_0000_0000 {
    ok := false;
    return;
  }

  var unique := test_unique(host_ids);
  if !unique {
    ok := false;
    return;
  }

  ok, my_index := GetHostIndex(id, host_ids);
  if !ok {
    return;
  }

  ghost var ghost_host_ids := lock_config_parsing(args);
  assert host_ids == ghost_host_ids;
}

}
