include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/RSL/Replica.i.dfy"
include "ReplicaModel.i.dfy"
include "ReplicaImplLemmas.i.dfy"
include "ReplicaImplClass.i.dfy"
include "ReplicaImplProcessPacketX.i.dfy"
include "ReplicaImplNoReceiveNoClock.i.dfy"
include "ReplicaImplNoReceiveClock.i.dfy"
include "NetRSL.i.dfy"
include "CClockReading.i.dfy"

module LiveRSL__ReplicaImplMain_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened LiveRSL__CClockReading_i
import opened LiveRSL__Environment_i
import opened LiveRSL__QRelations_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ReplicaImplClass_i
import opened LiveRSL__ReplicaImplLemmas_i
import opened LiveRSL__ReplicaImplNoReceiveClock_i
import opened LiveRSL__ReplicaImplNoReceiveNoClock_i
import opened LiveRSL__ReplicaImplProcessPacketX_i
import opened LiveRSL__ReplicaModel_i
import opened LiveRSL__NetRSL_i
import opened LiveRSL__Unsendable_i
import opened Common__NetClient_i


method rollActionIndex(a:uint64) returns (a':uint64)
  requires 0 <= a as int < 10
  ensures a' as int == ((a as int) + 1) % LReplicaNumActions()
{
  lemma_mod_auto(10);
  if (a >= 9) {
    a' := 0;
  } else {
    a' := (a + 1);
  }
}

method {:timeLimitMultiplier 2} ReplicaNextMainProcessPacketX(r:ReplicaImpl)
  returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RslIo>)
  requires r.Valid()
  requires r.nextActionIndex == 0
  modifies r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures r.Repr == old(r.Repr)
  ensures r.netClient != null
  ensures r.Env().Valid() && r.Env().ok.ok() ==> ok
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && (|| Q_LScheduler_Next(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), ios)
               || HostNextIgnoreUnsendable(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), netEventLog))
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && old(r.Env().net.history()) + netEventLog == r.Env().net.history()
{
  ghost var replica_old := old(r.AbstractifyToLReplica());
  ghost var scheduler_old := old(r.AbstractifyToLScheduler());

  assert scheduler_old.nextActionIndex == 0;

  //print ("Replica_Next_main Enter\n");
  assert scheduler_old.replica == replica_old;
  ok, netEventLog, ios := Replica_Next_ProcessPacketX(r);
  if (!ok) { return; }

  assert r.Valid();

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.MyPublicKey();
  assert NetClientIsValid(net_client_old);

  ghost var replica := r.AbstractifyToLReplica();
  r.nextActionIndex := 1;
  ghost var scheduler := r.AbstractifyToLScheduler();

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert NetClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.MyPublicKey();

  assert r.Valid();

  calc {
    scheduler.nextActionIndex;
    r.nextActionIndex as int;
    1;
      { lemma_mod_auto(LReplicaNumActions()); }
    (1)%LReplicaNumActions();
    (scheduler_old.nextActionIndex+1)%LReplicaNumActions();
  }

  if Q_LReplica_Next_ProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios) {
    lemma_EstablishQLSchedulerNext(replica_old, replica, ios, scheduler_old, scheduler);
    assert Q_LScheduler_Next(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), ios);
  }
  else {
    assert IosReflectIgnoringUnsendable(netEventLog);
    assert old(r.AbstractifyToLReplica()) == r.AbstractifyToLReplica();
    assert HostNextIgnoreUnsendable(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), netEventLog);
  }
}

method ReplicaNextMainNoClock(r:ReplicaImpl)
  returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RslIo>)
  requires r.Valid()
  requires r.nextActionIndex == 1 || r.nextActionIndex == 2 || r.nextActionIndex == 4 || r.nextActionIndex == 5 || r.nextActionIndex == 6
  modifies r.replica.executor.app, r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures r.Repr == old(r.Repr)
  ensures r.netClient != null
  ensures r.Env().Valid() && r.Env().ok.ok() ==> ok
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && Q_LScheduler_Next(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), ios)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && old(r.Env().net.history()) + netEventLog == r.Env().net.history()
{
  var curActionIndex := r.nextActionIndex;

  ghost var replica_old := old(r.AbstractifyToLReplica());
  ghost var scheduler_old := old(r.AbstractifyToLScheduler());

  assert scheduler_old.replica == replica_old;
  ok, netEventLog, ios := Replica_NoReceive_NoClock_Next(r);
  if (!ok) { return; }

  assert r.Valid();

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.MyPublicKey();
  assert NetClientIsValid(net_client_old);

  ghost var replica := r.AbstractifyToLReplica();
  var nextActionIndex' := r.nextActionIndex + 1; // rollActionIndex(r.nextActionIndex);
  r.nextActionIndex := nextActionIndex';
  ghost var scheduler := r.AbstractifyToLScheduler();

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert NetClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.MyPublicKey();

  assert r.Valid();
        
  calc {
    scheduler.nextActionIndex;
    r.nextActionIndex as int;
    nextActionIndex' as int;
      { lemma_mod_auto(LReplicaNumActions()); }
    ((curActionIndex+1) as int)%LReplicaNumActions();
    (scheduler_old.nextActionIndex+1)%LReplicaNumActions();
  }

  lemma_EstablishQLSchedulerNext(replica_old, replica, ios, scheduler_old, scheduler);
  assert Q_LScheduler_Next(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), ios);
}

method ReplicaNextMainReadClock(r:ReplicaImpl)
  returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RslIo>)
  requires r.Valid()
  requires r.nextActionIndex == 3 || r.nextActionIndex == 7 || r.nextActionIndex == 8 || r.nextActionIndex == 9
  modifies r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures r.Repr == old(r.Repr)
  ensures r.netClient != null
  ensures r.Env().Valid() && r.Env().ok.ok() ==> ok
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && Q_LScheduler_Next(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), ios)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && old(r.Env().net.history()) + netEventLog == r.Env().net.history()
{
  var curActionIndex := r.nextActionIndex;

  ghost var replica_old := old(r.AbstractifyToLReplica());
  ghost var scheduler_old := old(r.AbstractifyToLScheduler());

  assert scheduler_old.replica == replica_old;
  ok, netEventLog, ios := Replica_NoReceive_ReadClock_Next(r);
  if (!ok) { return; }

  assert r.Valid();

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.MyPublicKey();
  assert NetClientIsValid(net_client_old);

  ghost var replica := r.AbstractifyToLReplica();
  var nextActionIndex' := rollActionIndex(r.nextActionIndex);
  r.nextActionIndex := nextActionIndex';
  ghost var scheduler := r.AbstractifyToLScheduler();

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert NetClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.MyPublicKey();

  assert r.Valid();
        
  calc {
    scheduler.nextActionIndex;
    r.nextActionIndex as int;
    nextActionIndex' as int;
    ((curActionIndex+1) as int)%LReplicaNumActions();
    (scheduler_old.nextActionIndex+1)%LReplicaNumActions();
  }

  lemma_EstablishQLSchedulerNext(replica_old, replica, ios, scheduler_old, scheduler);
  assert Q_LScheduler_Next(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), ios);
}

method Replica_Next_main(r:ReplicaImpl)
  returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RslIo>)
  requires r.Valid()
  modifies r.replica.executor.app, r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures r.Repr == old(r.Repr)
  ensures r.netClient != null
  ensures r.Env().Valid() && r.Env().ok.ok() ==> ok
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && (|| Q_LScheduler_Next(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), ios)
               || HostNextIgnoreUnsendable(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), netEventLog))
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && old(r.Env().net.history()) + netEventLog == r.Env().net.history()
{
  //print ("Replica_Next_main Enter\n");
  if r.nextActionIndex == 0 {
    ok, netEventLog, ios := ReplicaNextMainProcessPacketX(r);
  }
  else if r.nextActionIndex == 1 || r.nextActionIndex == 2 || r.nextActionIndex == 4 || r.nextActionIndex == 5 || r.nextActionIndex == 6 {
    ok, netEventLog, ios := ReplicaNextMainNoClock(r);
  }
  else if (r.nextActionIndex == 3 || 7 <= r.nextActionIndex <= 9) {
    ok, netEventLog, ios := ReplicaNextMainReadClock(r);
  }
  //print ("Replica_Next_main Exit\n");
}

}
