include "Environment.s.dfy"
include "EnvironmentSynchrony.s.dfy"
include "../Logic/Temporal/Heuristics.i.dfy"
include "../Logic/Temporal/Rules.i.dfy"
include "../Logic/Temporal/Induction.i.dfy"

module Liveness__HostQueueLemmas_i {
import opened Environment_s
import opened EnvironmentSynchrony_s
import opened Temporal__Heuristics_i
import opened Temporal__Rules_i
import opened Temporal__Induction_i
import opened Collections__Maps2_s

predicate LEnvironmentInvariant<IdType, MessageType>(
  e:LEnvironment<IdType, MessageType>
  )
{
  forall p, id :: id in e.hostInfo && p in e.hostInfo[id].queue ==> p in e.sentPackets
}

lemma Lemma_LEnvironmentInitEstablishesInvariant<IdType, MessageType>(
  e:LEnvironment<IdType, MessageType>
  )
  requires LEnvironment_Init(e)
  requires HostQueues_Init(e)
  ensures  LEnvironmentInvariant(e)
{
}

lemma Lemma_HostQueuePerformIosProducesTail<IdType, MessageType>(
  hostQueue:seq<LPacket<IdType, MessageType>>,
  hostQueue':seq<LPacket<IdType, MessageType>>,
  ios:seq<LIoOp<IdType, MessageType>>
  )
  returns (i:int)
  requires HostQueue_PerformIos(hostQueue, hostQueue', ios)
  ensures  0 <= i <= |hostQueue|
  ensures  hostQueue' == hostQueue[i..]
{
  if |ios| > 0 && ios[0].LIoOpReceive? {
    var j := Lemma_HostQueuePerformIosProducesTail(hostQueue[1..], hostQueue', ios[1..]);
    i := j + 1;
  }
  else {
    i := 0;
  }
}

lemma Lemma_LEnvironmentNextPreservesInvariant<IdType, MessageType>(
  e:LEnvironment<IdType, MessageType>,
  e':LEnvironment<IdType, MessageType>
  )
  requires LEnvironmentInvariant(e)
  requires LEnvironment_Next(e, e')
  requires HostQueues_Next(e, e')
  ensures  LEnvironmentInvariant(e')
{
  if e.nextStep.LEnvStepHostIos?
  {
    var actor := e.nextStep.actor;
    var ios := e.nextStep.ios;
    forall p, id | id in e'.hostInfo && p in e'.hostInfo[id].queue
      ensures p in e'.sentPackets
    {
      assert id in mapdomain(e'.hostInfo);
      assert id in e.hostInfo;
      if (id == actor) {
        assert HostQueue_PerformIos(e.hostInfo[id].queue, e'.hostInfo[id].queue, ios);
        var i := Lemma_HostQueuePerformIosProducesTail(e.hostInfo[id].queue, e'.hostInfo[id].queue, ios);
        assert p in e'.hostInfo[id].queue ==> p in e.hostInfo[id].queue;
        assert p in e'.sentPackets;
      }
      else {
        assert e'.hostInfo[id].queue == e.hostInfo[id].queue;
        assert p in e'.sentPackets;
      }
    }
  }
}

lemma Lemma_IfOpSeqIsCompatibleWithReductionThenSoIsSuffix<IdType, MessageType>(
  ios:seq<LIoOp<IdType, MessageType>>,
  j:int
  )
  requires LIoOpSeqCompatibleWithReduction(ios)
  requires 0 <= j <= |ios|
  ensures  LIoOpSeqCompatibleWithReduction(ios[j..])
{
  forall i | 0 <= i < |ios[j..]| - 1
    ensures LIoOpOrderingOKForAction(ios[j..][i], ios[j..][i+1])
  {
    assert ios[j..][i] == ios[j+i];
    assert ios[j..][i+1] == ios[j+i+1];
  }
}

lemma Lemma_IfOpSeqIsCompatibleWithReductionAndFirstIsntReceiveThenNoneAreReceives<IdType, MessageType>(
  ios:seq<LIoOp<IdType, MessageType>>
  )
  requires LIoOpSeqCompatibleWithReduction(ios)
  ensures  |ios| > 0 && !ios[0].LIoOpReceive? ==> (forall io :: io in ios ==> !io.LIoOpReceive?)
{
  if |ios| > 1 && !ios[0].LIoOpReceive?
  {
    var i := 0;
    assert 0 <= i < |ios| - 1;
    assert LIoOpOrderingOKForAction(ios[i], ios[i+1]);
    assert ios[1].LIoOpSend?;
    Lemma_IfOpSeqIsCompatibleWithReductionThenSoIsSuffix(ios, 1);
    Lemma_IfOpSeqIsCompatibleWithReductionAndFirstIsntReceiveThenNoneAreReceives(ios[1..]);
  }
}

predicate HostQueueDecomposition<IdType, MessageType>(
  hostQueue:seq<LPacket<IdType, MessageType>>,
  hostQueue':seq<LPacket<IdType, MessageType>>,
  s1:seq<LPacket<IdType, MessageType>>,
  s2:seq<LPacket<IdType, MessageType>>,
  p:LPacket<IdType, MessageType>
  )
{
  hostQueue == s1 + [p] + s2 + hostQueue'
}

lemma{:timeLimitMultiplier 2} Lemma_ReceiveRemovesPacketFromHostQueue<IdType, MessageType>(
  hostQueue:seq<LPacket<IdType, MessageType>>,
  hostQueue':seq<LPacket<IdType, MessageType>>,
  ios:seq<LIoOp<IdType, MessageType>>,
  p:LPacket<IdType, MessageType>
  )
  requires HostQueue_PerformIos(hostQueue, hostQueue', ios)
  requires LIoOpReceive(p) in ios
  requires LIoOpSeqCompatibleWithReduction(ios)
  ensures  exists s1, s2 :: HostQueueDecomposition(hostQueue, hostQueue', s1, s2, p)
{
  if (!ios[0].LIoOpReceive?)
  {
    Lemma_IfOpSeqIsCompatibleWithReductionAndFirstIsntReceiveThenNoneAreReceives(ios);
    assert false;
  }
  
  if ios[0].r == p
  {
    assert hostQueue[0] == p;       
    var j := Lemma_HostQueuePerformIosProducesTail(hostQueue[1..], hostQueue', ios[1..]);
    assert 0 <= j <= |hostQueue[1..]| && hostQueue' == hostQueue[1..][j..];
    var s1 := [];
    var s2 := hostQueue[1..j+1];
    calc {
      hostQueue;
      [hostQueue[0]] + hostQueue[1..];
      [hostQueue[0]] + hostQueue[1..j+1] + hostQueue[j+1..];
      [hostQueue[0]] + hostQueue[1..j+1] + hostQueue[1..][j..];
    }
    assert HostQueueDecomposition(hostQueue, hostQueue', s1, s2, p);
  }
  else
  {
    Lemma_IfOpSeqIsCompatibleWithReductionThenSoIsSuffix(ios, 1);
    Lemma_ReceiveRemovesPacketFromHostQueue(hostQueue[1..], hostQueue', ios[1..], p);
    var s1', s2 :| hostQueue[1..] == s1' + [p] + s2 + hostQueue';
    var j := Lemma_HostQueuePerformIosProducesTail(hostQueue[1..], hostQueue', ios[1..]);
    assert 0 <= j <= |hostQueue[1..]| && hostQueue' == hostQueue[1..][j..];
    calc {
      hostQueue;
      [hostQueue[0]] + hostQueue[1..];
      [hostQueue[0]] + s1' + [p] + s2 + hostQueue';
    }
    var s1 := [hostQueue[0]] + s1';
    assert HostQueueDecomposition(hostQueue, hostQueue', s1, s2, p);
  }
  assert exists s1, s2 :: HostQueueDecomposition(hostQueue, hostQueue', s1, s2, p);
}

lemma Lemma_RemovePacketFromHostQueueImpliesReceive<IdType, MessageType>(
  hostQueue:seq<LPacket<IdType, MessageType>>,
  hostQueue':seq<LPacket<IdType, MessageType>>,
  ios:seq<LIoOp<IdType, MessageType>>,
  p:LPacket<IdType, MessageType>
  )
  requires HostQueue_PerformIos(hostQueue, hostQueue', ios)
  requires exists s1, s2 :: HostQueueDecomposition(hostQueue, hostQueue', s1, s2, p)
  requires LIoOpSeqCompatibleWithReduction(ios)
  ensures  LIoOpReceive(p) in ios
{
  var s1, s2 :| HostQueueDecomposition(hostQueue, hostQueue', s1, s2, p);
  if |s1| > 0
  {
    if (!ios[0].LIoOpReceive?)
    {
      Lemma_IfOpSeqIsCompatibleWithReductionAndFirstIsntReceiveThenNoneAreReceives(ios);
      assert false;
    }

    assert HostQueue_PerformIos(hostQueue[1..], hostQueue', ios[1..]);
    assert HostQueueDecomposition(hostQueue[1..], hostQueue', s1[1..], s2, p);
    Lemma_IfOpSeqIsCompatibleWithReductionThenSoIsSuffix(ios, 1);
    Lemma_RemovePacketFromHostQueueImpliesReceive(hostQueue[1..], hostQueue', ios[1..], p);
  }
}

lemma Lemma_ReceiveMakesHostQueueSmaller<IdType, MessageType>(
  hostQueue:seq<LPacket<IdType, MessageType>>,
  hostQueue':seq<LPacket<IdType, MessageType>>,
  ios:seq<LIoOp<IdType, MessageType>>,
  p:LPacket<IdType, MessageType>
  )
  requires HostQueue_PerformIos(hostQueue, hostQueue', ios)
  requires LIoOpReceive(p) in ios
  requires LIoOpSeqCompatibleWithReduction(ios)
  ensures  |hostQueue'| < |hostQueue|
{
  Lemma_ReceiveRemovesPacketFromHostQueue(hostQueue, hostQueue', ios, p);
}

lemma Lemma_HostQueuePerformIosReceivesFromHostQueue<IdType, MessageType>(
  hostQueue:seq<LPacket<IdType, MessageType>>,
  hostQueue':seq<LPacket<IdType, MessageType>>,
  ios:seq<LIoOp<IdType, MessageType>>
  )
  requires HostQueue_PerformIos(hostQueue, hostQueue', ios)
  requires LIoOpSeqCompatibleWithReduction(ios)
  ensures  forall io :: io in ios && io.LIoOpReceive? ==> io.r in hostQueue
  decreases |ios|
{
  if |ios| == 0
  {
  }
  else if ios[0].LIoOpReceive?
  {
    assert ios[0].r in hostQueue;
    Lemma_IfOpSeqIsCompatibleWithReductionThenSoIsSuffix(ios, 1);
    Lemma_HostQueuePerformIosReceivesFromHostQueue(hostQueue[1..], hostQueue', ios[1..]);
  }
  else
  {
    Lemma_IfOpSeqIsCompatibleWithReductionAndFirstIsntReceiveThenNoneAreReceives(ios);
  }
}

} 
