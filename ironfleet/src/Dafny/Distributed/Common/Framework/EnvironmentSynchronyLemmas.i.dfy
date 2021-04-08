include "EnvironmentSynchrony.s.dfy"
include "HostQueueLemmas.i.dfy"
include "../Logic/Temporal/Heuristics.i.dfy"
include "../Logic/Temporal/Rules.i.dfy"
include "../Logic/Temporal/Induction.i.dfy"
include "../Logic/Temporal/Time.i.dfy"
include "../../../Libraries/Math/mul_auto.i.dfy"
include "../Collections/Sets.i.dfy"

module Liveness__EnvironmentSynchronyLemmas_i {
import opened Environment_s
import opened EnvironmentSynchrony_s
import opened Liveness__HostQueueLemmas_i
import opened Temporal__Temporal_s
import opened Temporal__Heuristics_i
import opened Temporal__Monotonicity_i
import opened Temporal__Rules_i
import opened Temporal__Induction_i
import opened Temporal__Time_s
import opened Temporal__Time_i
import opened Collections__Sets_i
import opened Collections__Maps2_s
import opened Collections__Maps2_i
import opened Math__mul_auto_i
import opened Math__mul_i

function{:opaque} HostQueueEmptyTemporal<IdType, MessageType>(
  b:Behavior<LEnvironment<IdType, MessageType>>,
  host:IdType
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, HostQueueEmptyTemporal(b, host))} ::
             sat(i, HostQueueEmptyTemporal(b, host)) <==> (host in b[i].hostInfo ==> |b[i].hostInfo[host].queue| == 0)
{
  stepmap(imap i :: host in b[i].hostInfo ==> |b[i].hostInfo[host].queue| == 0)
}

function{:opaque} PacketInHostQueueTemporal<IdType, MessageType>(
  b:Behavior<LEnvironment<IdType, MessageType>>,
  p:LPacket<IdType, MessageType>
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, PacketInHostQueueTemporal(b, p))} :: sat(i, PacketInHostQueueTemporal(b, p)) <==>
                                                                  (p.dst in b[i].hostInfo && p in b[i].hostInfo[p.dst].queue)
{
  stepmap(imap i :: p.dst in b[i].hostInfo && p in b[i].hostInfo[p.dst].queue)
}

predicate PacketReceivedDuringAction<IdType, MessageType>(
  e:LEnvironment<IdType, MessageType>,
  p:LPacket<IdType, MessageType>
  )
{
  e.nextStep.LEnvStepHostIos? && LIoOpReceive(p) in e.nextStep.ios
}

function{:opaque} PacketReceivedTemporal<IdType, MessageType>(
  b:Behavior<LEnvironment<IdType, MessageType>>,
  p:LPacket<IdType, MessageType>
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, PacketReceivedTemporal(b, p))} ::
             sat(i, PacketReceivedTemporal(b, p)) <==> PacketReceivedDuringAction(b[i], p)
{
  stepmap(imap i :: PacketReceivedDuringAction(b[i], p))
}

predicate AllPacketsReceivedWithin<IdType(!new), MessageType(!new)>(
  b:Behavior<LEnvironment<IdType, MessageType>>,
  i:int,
  receive_period:int,
  sources:set<IdType>,
  destinations:set<IdType>
  )
  requires imaptotal(b)
{
  forall p {:trigger PacketSentBetweenHosts(b[i], p, sources, destinations)} ::
      PacketSentBetweenHosts(b[i], p, sources, destinations) ==>
      sat(i, next(eventuallynextwithin(PacketReceivedTemporal(b, p), receive_period, BehaviorToTimeMap(b))))
}

function{:opaque} AllPacketsReceivedWithinTemporal<IdType(!new), MessageType(!new)>(
  b:Behavior<LEnvironment<IdType, MessageType>>,
  receive_period:int,
  sources:set<IdType>,
  destinations:set<IdType>
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, AllPacketsReceivedWithinTemporal(b, receive_period, sources, destinations))} ::
             sat(i, AllPacketsReceivedWithinTemporal(b, receive_period, sources, destinations)) <==>
             AllPacketsReceivedWithin(b, i, receive_period, sources, destinations)
{
  stepmap(imap i :: AllPacketsReceivedWithin(b, i, receive_period, sources, destinations))
}

predicate ReceiveAttemptedInStep<IdType, MessageType>(
  e:LEnvironment<IdType, MessageType>,
  host:IdType
  )
{
  && e.nextStep.LEnvStepHostIos?
  && e.nextStep.actor == host
  && |e.nextStep.ios| > 0
  && (e.nextStep.ios[0].LIoOpTimeoutReceive? || e.nextStep.ios[0].LIoOpReceive?)
}

function{:opaque} ReceiveAttemptedTemporal<IdType, MessageType>(
  b:Behavior<LEnvironment<IdType, MessageType>>,
  host:IdType
  ):temporal
  requires imaptotal(b)
  ensures  forall i {:trigger sat(i, ReceiveAttemptedTemporal(b, host))} ::
               sat(i, ReceiveAttemptedTemporal(b, host)) <==> ReceiveAttemptedInStep(b[i], host)
{
  stepmap(imap i :: ReceiveAttemptedInStep(b[i], host))
}

lemma Lemma_TimeOnlyAdvancesBetweenSteps<IdType, MessageType>(
  b:Behavior<LEnvironment<IdType, MessageType>>,
  i:int,
  j:int
  )
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires 0 <= i <= j
  ensures  b[i].time <= b[j].time
  decreases j - i
{
  if j > i
  {
    Lemma_TimeOnlyAdvancesBetweenSteps(b, i, j-1);
    TemporalDeduceFromAlways(0, j-1, EnvironmentNextTemporal(b));
  }
}

lemma Lemma_EstablishMonotonicFromOpaque<IdType, MessageType>(
  b:Behavior<LEnvironment<IdType, MessageType>>,
  start:int
  )
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires 0 <= start
  ensures  monotonic_from_opaque(start, BehaviorToTimeMap(b))
{
  var f := BehaviorToTimeMap(b);
  forall i1, i2 | i1 in f && i2 in f && start <= i1 <= i2
    ensures f[i1] <= f[i2]
  {
    Lemma_TimeOnlyAdvancesBetweenSteps(b, i1, i2);
  }
  reveal monotonic_from_opaque();
}

lemma Lemma_IfOpSeqIsCompatibleWithReductionAndFirstIsntReceiveThenNoneAreReceives2<IdType, MessageType>(
  ios:seq<LIoOp<IdType, MessageType>>
  )
  requires LIoOpSeqCompatibleWithReduction(ios)
  ensures  |ios| > 0 && !ios[0].LIoOpReceive? && !ios[0].LIoOpTimeoutReceive? ==> (forall io :: io in ios ==> !io.LIoOpReceive? && !io.LIoOpTimeoutReceive?)
{
  if |ios| > 1 && !ios[0].LIoOpReceive? && !ios[0].LIoOpTimeoutReceive?
  {
    var i := 0;
    assert 0 <= i < |ios| - 1;
    assert LIoOpOrderingOKForAction(ios[i], ios[i+1]);
    assert ios[1].LIoOpSend?;
    Lemma_IfOpSeqIsCompatibleWithReductionThenSoIsSuffix(ios, 1);
    Lemma_IfOpSeqIsCompatibleWithReductionAndFirstIsntReceiveThenNoneAreReceives2(ios[1..]);
  }
}

lemma Lemma_ReceiveMakesHostQueueSmaller2<IdType, MessageType>(
  q:seq<LPacket<IdType, MessageType>>,
  q':seq<LPacket<IdType, MessageType>>,
  ios:seq<LIoOp<IdType, MessageType>>,
  io:LIoOp<IdType, MessageType>
  )
  requires HostQueue_PerformIos(q, q', ios)
  requires LIoOpSeqCompatibleWithReduction(ios)
  requires io.LIoOpTimeoutReceive? || io.LIoOpReceive?
  ensures  |q'| <= |q|
  ensures  io in ios ==> |q| == 0 || |q'| < |q|
  decreases |ios|
{
  if (|ios| == 0)
  {
    assert q == q';
    assert io !in ios;
    return;
  }
  var io0 := ios[0];
  assert ios == [io0] + ios[1..];
  if (io0.LIoOpTimeoutReceive?)
  {
    assert |q| == 0;
  }
  else if (io0.LIoOpReceive?)
  {
    Lemma_IfOpSeqIsCompatibleWithReductionThenSoIsSuffix(ios, 1);
    Lemma_ReceiveMakesHostQueueSmaller2(q[1..], q', ios[1..], io);
  }
  else
  {
    Lemma_IfOpSeqIsCompatibleWithReductionAndFirstIsntReceiveThenNoneAreReceives2(ios);
  }
}

function{:opaque} QueuePosition<IdType, MessageType>(q:seq<LPacket<IdType, MessageType>>, p:LPacket<IdType, MessageType>):int
  requires p in q
  ensures  0 <= QueuePosition(q, p) < |q|
{
  if q[0] == p then 0
  else 1 + QueuePosition(q[1..], p)
}

lemma Lemma_QueuePosition<IdType, MessageType>(q:seq<LPacket<IdType, MessageType>>, p:LPacket<IdType, MessageType>)
  requires p in q
  ensures QueuePosition(q, p) > 0 ==> |q| > 0 && p in q[1..] && QueuePosition(q[1..], p) < QueuePosition(q, p)
{
  reveal QueuePosition();
}

lemma Lemma_QueuePositionTail<IdType, MessageType>(
  q:seq<LPacket<IdType, MessageType>>,
  p:LPacket<IdType, MessageType>,
  q':seq<LPacket<IdType, MessageType>>
  )
  requires p in q
  ensures  QueuePosition(q, p) == QueuePosition(q + q', p)
{
  reveal QueuePosition();
  if (q[0] == p)
  {
    assert QueuePosition(q, p) == QueuePosition(q + q', p);
  }
  else
  {
    Lemma_QueuePositionTail(q[1..], p, q');
    assert q[1..] + q' == (q + q')[1..];
  }
}

lemma Lemma_DeliverIsInstantaneous<IdType, MessageType>(
  b:Behavior<LEnvironment<IdType, MessageType>>,
  i:int,
  host:IdType
  )
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires 0 <= i
  ensures  sat(i, always(ActionIsInstantaneousTemporal(PacketDeliveredToHostTemporal(b, host), BehaviorToTimeMap(b))))
{
  var x := PacketDeliveredToHostTemporal(b, host);
  var f := BehaviorToTimeMap(b);
    
  forall j | i <= j
    ensures sat(j, ActionIsInstantaneousTemporal(x, f))
  {
    if sat(j, x)
    {
      TemporalDeduceFromAlways(0, j, EnvironmentNextTemporal(b));
      assert f[j] == f[j+1];
    }
  }
  TemporalAlways(i, ActionIsInstantaneousTemporal(x, f));
}

lemma Lemma_ReceiveIsInstantaneous<IdType, MessageType>(
  b:Behavior<LEnvironment<IdType, MessageType>>,
  i:int,
  host:IdType
  )
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires 0 <= i
  ensures  sat(i, always(ActionIsInstantaneousTemporal(ReceiveAttemptedTemporal(b, host), BehaviorToTimeMap(b))))
{
  var x := ReceiveAttemptedTemporal(b, host);
  var f := BehaviorToTimeMap(b);
    
  forall j | i <= j
    ensures sat(j, ActionIsInstantaneousTemporal(x, f));
  {
    if sat(j, x)
    {
      TemporalDeduceFromAlways(0, j, EnvironmentNextTemporal(b));
      assert f[j] == f[j+1];
    }
  }
  TemporalAlways(i, ActionIsInstantaneousTemporal(x, f));
}


lemma Lemma_DeliverIncrReceiveDecr<IdType, MessageType>(
  i1:int,
  i2:int,
  b:Behavior<LEnvironment<IdType, MessageType>>,
  host:IdType,
  d:imap<int, int>
  )
  requires imaptotal(b)
  requires imaptotal(d)
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires HostQueuesLive(b)
  requires TLe(0, i1)
  requires TLe(i1, i2)
  requires d[i1] >= 0
  requires d[i2] >= 1
  requires d == imap i :: if host in b[i].hostInfo then |b[i].hostInfo[host].queue| else 0
  ensures || (sat(i2, PacketDeliveredToHostTemporal(b, host)) && !sat(i2, ReceiveAttemptedTemporal(b, host)) && d[i2 + 1] == d[i2] + 1)
          || (!sat(i2, PacketDeliveredToHostTemporal(b, host)) && sat(i2, ReceiveAttemptedTemporal(b, host)) && d[i2 + 1] < d[i2])
          || (!sat(i2, PacketDeliveredToHostTemporal(b, host)) && !sat(i2, ReceiveAttemptedTemporal(b, host)) && d[i2 + 1] == d[i2])
{
  TemporalAssist();
  assert TLe(i1, i1);
  var incr := PacketDeliveredToHostTemporal(b, host);
  var decr := ReceiveAttemptedTemporal(b, host);

  assert TLe(0, i2);
  assert i2 == i1 || TLe(i1, i2 - 1);
  assert sat(i2, EnvironmentNextTemporal(b));
  var e := b[i2];
  var e' := b[i2 + 1];
  assert LEnvironment_Next(e, e');
  assert HostQueues_Next(e, e');

  assert 0 < d[i2];
  assert host in e.hostInfo;

  var q := e.hostInfo[host].queue;

  if e.nextStep.LEnvStepHostIos?
  {
    if e.nextStep.actor != host
    {
      assert d[i2 + 1] == d[i2];
    }
    else if ReceiveAttemptedInStep(e, host)
    {
      var actor := e.nextStep.actor;
      var ios := e.nextStep.ios;
      var io := e.nextStep.ios[0];
      var q' := e'.hostInfo[host].queue;
      Lemma_ReceiveMakesHostQueueSmaller2(q, q', ios, io);
      assert d[i2 + 1] < d[i2];
    }
    else
    {
      assert d[i2+1] == d[i2];
    }
  }
  else if e.nextStep.LEnvStepDeliverPacket?
  {
    var p := e.nextStep.p;
    if (p.dst == host)
    {
      assert d[i2 + 1] == d[i2] + 1;
    }
  }
}

// TODO: merge with Lemma_DeliverIncrReceiveDecr
lemma Lemma_DeliverIncr<IdType, MessageType>(
  i1:int,
  i2:int,
  b:Behavior<LEnvironment<IdType, MessageType>>,
  host:IdType,
  d:imap<int, int>
  )
  requires imaptotal(b)
  requires imaptotal(d)
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires HostQueuesLive(b)
  requires TLe(0, i1)
  requires TLe(i1, i2)
  requires d[i1] >= 0
  requires d == imap i :: if host in b[i].hostInfo then |b[i].hostInfo[host].queue| else 0
  ensures  || (sat(i2, PacketDeliveredToHostTemporal(b, host)) && d[i2 + 1] == d[i2] + 1)
           || (!sat(i2, PacketDeliveredToHostTemporal(b, host)) && d[i2 + 1] <= d[i2])
{
  TemporalAssist();
  assert TLe(i1, i1);
  var incr := PacketDeliveredToHostTemporal(b, host);
  var decr := ReceiveAttemptedTemporal(b, host);

  assert TLe(0, i2);
  assert i2 == i1 || TLe(i1, i2 - 1);
  assert sat(i2, EnvironmentNextTemporal(b));
  var e := b[i2];
  var e' := b[i2 + 1];
  assert LEnvironment_Next(e, e');
  assert HostQueues_Next(e, e');

  if (sat(i2, decr))
  {
    if (host in e.hostInfo)
    {
      var ios := e.nextStep.ios;
      var io := e.nextStep.ios[0];
      var q := e.hostInfo[host].queue;
      var q' := e'.hostInfo[host].queue;
      Lemma_ReceiveMakesHostQueueSmaller2(q, q', ios, io);
      assert d[i2 + 1] <= d[i2];
    }
  }
  else if e.nextStep.LEnvStepDeliverPacket?
  {
    var p := e.nextStep.p;
    if (p.dst == host)
    {
      assert d[i2 + 1] == d[i2] + 1;
    }
  }
  else if e.nextStep.LEnvStepAdvanceTime?
  {
    assert d[i2 + 1] == d[i2];
  }
  else if e.nextStep.LEnvStepHostIos?
  {
    assert !sat(i2, PacketDeliveredToHostTemporal(b, host));
    var actor := e.nextStep.actor;
    var ios := e.nextStep.ios;
    if (host == actor)
    {
      if (!sat(i2+1, decr) && |ios| != 0)
      {
        if (ios[0].LIoOpReceive?)
        {
          assert ReceiveAttemptedInStep(e, host);
        }
      }
    }
  }
}

lemma Lemma_HostQueueEmptiesAgain<IdType, MessageType>(
  latency_bound:int,
  host:IdType,
  b:Behavior<LEnvironment<IdType, MessageType>>,
  i1:int,
  burst_size:int,
  receive_period:int
  ) returns(i2:int)
  requires imaptotal(b)
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires HostQueuesLive(b)
  requires TLe(0, i1)
  requires 1 <= receive_period
  requires 1 <= burst_size
  requires sat(i1, HostQueueEmptyTemporal(b, host))
  requires sat(i1, always(eventuallynextwithin(ReceiveAttemptedTemporal(b, host), receive_period, BehaviorToTimeMap(b))))
  requires sat(i1, always(NetworkDeliveryRateForHostBoundedTemporal(b, burst_size, burst_size * receive_period + 1, host)))
  ensures  sat(i2, HostQueueEmptyTemporal(b, host))
  ensures  i1 < i2
  ensures  forall i :: i1 <= i <= i2 && host in b[i].hostInfo ==> |b[i].hostInfo[host].queue| <= burst_size
{
  var timefun := BehaviorToTimeMap(b);
  var goal := HostQueueEmptyTemporal(b, host);
  var d := imap i :: if host in b[i].hostInfo then |b[i].hostInfo[host].queue| else 0;
  var bs := burst_size;
  var r := receive_period;
  var p := bs * r;
  var incr := PacketDeliveredToHostTemporal(b, host);
  var decr := ReceiveAttemptedTemporal(b, host);
  var nIncr:int := bs;
  var nDecr:int := bs;
  TemporalAssist();

  Lemma_EstablishMonotonicFromOpaque(b, i1);
  Lemma_DeliverIsInstantaneous(b, i1, host);
  Lemma_ReceiveIsInstantaneous(b, i1, host);

  forall ensures 1 <= p { lemma_mul_increases(bs, r); }

  assert TLe(i1, i1);
  forall ensures sat(i1, countWithinGe(nDecr, decr, p, timefun))
  {
    Lemma_CountWithinGeOne(i1, decr, r, timefun);
    Lemma_CountWithinGeMultiple(i1, bs, 1, decr, r, timefun);
  }

  forall ensures sat(i1, countWithinLe(nIncr, incr, p, timefun))
  {
    lemma_mul_is_commutative(bs, r);
    assert sat(i1, always(NetworkDeliveryRateForHostBoundedTemporal(b, burst_size, burst_size * receive_period + 1, host)));
    assert sat(i1, always(countWithinLe(bs, incr, p + 1, timefun)));
    assert sat(i1, always(countWithinLe(bs, incr, p, timefun)));
  }

  if (d[i1 + 1] == 0)
  {
    i2 := i1 + 1;
    return;
  }

  assert sat(i1, PacketDeliveredToHostTemporal(b, host));
  assert sat(i1, ActionIsInstantaneousTemporal(PacketDeliveredToHostTemporal(b, host), timefun));
  assert timefun[i1] == timefun[i1+1];
  if (forall i :: TLe(i1, i) && i1 != i && timefun[i] <= timefun[i1] + p ==> d[i] > 0)
  {
    assert TLe(i1, i1);
    forall i {:trigger TLe(i1, i)} | TLe(i1, i) && i1 != i && timefun[i] <= timefun[i1] + p
      ensures || (sat(i, incr) && !sat(i, decr) && d[i + 1] == d[i] + 1)
              || (!sat(i, incr) && sat(i, decr) && d[i + 1] < d[i])
              || (!sat(i, incr) && !sat(i, decr) && d[i + 1] == d[i])
    {
      Lemma_DeliverIncrReceiveDecr(i1, i, b, host, d);
    }

    forall ensures sat(i1, incr) && !sat(i1, decr) && d[i1 + 1] == d[i1] + 1
    {
      if (!(host in b[i1].hostInfo))
      {
        assert !(host in b[i1 + 1].hostInfo);
      }
      if (sat(i1, decr))
      {
        if (host in b[i1].hostInfo)
        {
          var ios := b[i1].nextStep.ios;
          var io := ios[0];
          Lemma_ReceiveMakesHostQueueSmaller2(b[i1].hostInfo[host].queue, b[i1 + 1].hostInfo[host].queue, ios, io);
        }
        else
        {
        }
        assert false; // proof by contradiction
      }
    }

    i2 := Lemma_CountIncrDecr(i1, d, nIncr, nDecr, incr, decr, p, timefun);
    var f1 := imap i :: d[i] <= d[i1] + nIncr - nDecr;
    assert TLe(i1, i2) && sat(i2, stepmap(f1)) && timefun[i2] <= timefun[i1] + p;
    assert d[i2] <= d[i1];
    assert TLe(i1, i2);
    assert i1 != i2;
    assert timefun[i2] <= timefun[i1] + p;

    assert false; // proof by contradiction
  }

  i2 :| i1 < i2 && timefun[i2] <= timefun[i1] + p && d[i2] == 0;

  forall i {:trigger TLe(i1, i)} | TLe(i1, i) && timefun[i] <= timefun[i1] + p
    ensures || (sat(i, incr) && d[i + 1] == d[i] + 1)
            || (!sat(i, incr) && d[i + 1] <= d[i])
  {
    Lemma_DeliverIncr(i1, i, b, host, d);
  }
  Lemma_CountIncr(i1, d, nIncr, incr, p, timefun);
  var f2 := imap i :: d[i] <= d[i1] + nIncr;
  assert sat(i1, alwayswithin(stepmap(f2), p, timefun));

  forall i | i1 <= i <= i2 && host in b[i].hostInfo
    ensures |b[i].hostInfo[host].queue| <= burst_size
  {
    Lemma_TimeOnlyAdvancesBetweenSteps(b, i, i2);
    TemporalDeduceFromAlways(i1, i, untilabsolutetime(stepmap(f2), timefun[i1] + p, timefun));
    assert sat(i, stepmap(f2));
  }
}

lemma Lemma_ReceiveAttemptNoDecr<IdType, MessageType>(
  i2:int,
  i3:int,
  i4:int,
  b:Behavior<LEnvironment<IdType, MessageType>>,
  p:LPacket<IdType, MessageType>,
  d:imap<int, int>,
  r:int,
  timefun:imap<int, int>
  )   
  requires imaptotal(b)
  requires imaptotal(timefun)
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires HostQueuesLive(b)
  requires TLe(0, i2)
  requires TLe(i2 + 1, i3)
  ensures  TLe(i3, i4)
  requires sat(i3, eventuallynextwithin(ReceiveAttemptedTemporal(b, p.dst), r, timefun))
  requires d == imap i ::
                (if TLe(i2, i) && p.dst in b[i].hostInfo && p in b[i].hostInfo[p.dst].queue
                    then 1 + QueuePosition(b[i].hostInfo[p.dst].queue, p)
                    else 0)
  requires monotonic_from(i3, timefun)
  requires i4 == earliestActionWithin(i3, ReceiveAttemptedTemporal(b, p.dst), r, timefun)
  requires d[i3] >= 1
  ensures  d[i4] == d[i3]
  decreases i4 - i3
{
  TemporalAssist();
  if (i3 < i4)
  {
    assert TLe(0, i3);
    var e := b[i3];
    var e' := b[i3 + 1];
    var q := e.hostInfo[p.dst].queue;
    assert !sat(i3, ReceiveAttemptedTemporal(b, p.dst));

    assert LEnvironment_Next(e, e');
    assert HostQueues_Next(e, e');

    if e.nextStep.LEnvStepDeliverPacket?
    {
      var q' := e'.hostInfo[p.dst].queue;
      if (q != q')
      {
        var p' :| q' == q + [p'];
        Lemma_QueuePositionTail(q, p, [p']);
        assert d[i3] == d[i3 + 1];
      }
      assert d[i3] == d[i3 + 1];
    }
    else if e.nextStep.LEnvStepAdvanceTime?
    {
      assert d[i3] == d[i3 + 1];
    }
    else if e.nextStep.LEnvStepHostIos?
    {
      var actor := e.nextStep.actor;
      var ios := e.nextStep.ios;
      if (actor == p.dst)
      {
        var q' := e'.hostInfo[p.dst].queue;
        assert HostQueue_PerformIos(q, q', ios);
        if (|ios| > 0 && ios[0].LIoOpReceive?)
        {
          var io := ios[0];
          assert ReceiveAttemptedInStep(e, p.dst);
        }
      }
    }

    assert d[i3] == d[i3 + 1];
    var k := TemporalDeduceFromEventual(i3, nextbefore(ReceiveAttemptedTemporal(b, p.dst), timefun[i3] + r, timefun));
    assert k != i3;
    TemporalEventually(i3 + 1, k, nextbefore(ReceiveAttemptedTemporal(b, p.dst), timefun[i3] + r, timefun));
    Lemma_ReceiveAttemptNoDecr(i2, i3 + 1, i4, b, p, d, r, timefun);
  }
}

lemma Lemma_PromoteInQueue<IdType, MessageType>(
  q:seq<LPacket<IdType, MessageType>>,
  q':seq<LPacket<IdType, MessageType>>,
  p:LPacket<IdType, MessageType>,
  ios:seq<LIoOp<IdType, MessageType>>
  )
  requires p in q
  requires HostQueue_PerformIos(q, q', ios)
  requires (forall i :: 0 <= i < |ios| && ios[i].LIoOpReceive? ==> ios[i].r != p)
  ensures  p in q'
  ensures  QueuePosition(q', p) <= QueuePosition(q, p)
  ensures  |ios| >= 1 && ios[0].LIoOpReceive? ==> QueuePosition(q', p) < QueuePosition(q, p)
  decreases ios
{
  reveal QueuePosition();
  if (|ios| > 0)
  {
    var io := ios[0];
    if (io.LIoOpReceive?)
    {
      Lemma_QueuePosition(q, p);
      Lemma_PromoteInQueue(q[1..], q', p, ios[1..]);
    }
  }
}

lemma Lemma_ReceiveAttemptDecr<IdType, MessageType>(
  i2:int,
  i3:int,
  b:Behavior<LEnvironment<IdType, MessageType>>,
  p:LPacket<IdType, MessageType>,
  d:imap<int, int>,
  r:int,
  timefun:imap<int, int>
  ) returns(i4:int)
  requires imaptotal(b)
  requires imaptotal(timefun)
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires HostQueuesLive(b)
  requires TLe(0, i2)
  requires TLe(i2 + 1, i3)
  requires monotonic_from(i3, timefun)
  requires sat(i3, eventuallynextwithin(ReceiveAttemptedTemporal(b, p.dst), r, timefun))
  requires d == imap i ::
                (if TLe(i2, i) && p.dst in b[i].hostInfo && p in b[i].hostInfo[p.dst].queue
                    then 1 + QueuePosition(b[i].hostInfo[p.dst].queue, p)
                    else 0)
  ensures  TLe(i3, i4)
  ensures  sat(i3, actionGoalDecreaseWithin(PacketReceivedTemporal(b, p), d, r, timefun))
{
  TemporalAssist();
  var goal := PacketReceivedTemporal(b, p);

  i4 := earliestActionWithin(i3, ReceiveAttemptedTemporal(b, p.dst), r, timefun);

  if (d[i3] != 0)
  {
    assert d[i3] == (if TLe(i2, i3) && p.dst in b[i3].hostInfo && p in b[i3].hostInfo[p.dst].queue
                    then 1 + QueuePosition(b[i3].hostInfo[p.dst].queue, p)
                    else 0);
    assert d[i3] > 0;
    Lemma_ReceiveAttemptNoDecr(i2, i3, i4, b, p, d, r, timefun);
    assert d[i3] == d[i4];
    assert d[i4] > 0;

    TemporalDeduceFromAlways(0, i4, HostQueuesNextTemporal(b));
    var e := b[i4];
    var e' := b[i4 + 1];
    var ios := b[i4].nextStep.ios;
    var io := ios[0];
    var q := e.hostInfo[p.dst].queue;
    Lemma_IfOpSeqIsCompatibleWithReductionAndFirstIsntReceiveThenNoneAreReceives2(ios);
    assert io.LIoOpTimeoutReceive? || io.LIoOpReceive?;

    if (ios[0].LIoOpTimeoutReceive?)
    {
      assert |q| == 0;
    }
    if (ios[0].LIoOpReceive?)
    {
      assert p.dst in e'.hostInfo;
      var q' := e'.hostInfo[p.dst].queue;
      assert HostQueue_PerformIos(q, q', ios);
      if (exists i :: 0 <= i < |ios| && ios[i].LIoOpReceive? && ios[i].r == p)
      {
        assert sat(i4, goal);
      }
      else
      {
        Lemma_PromoteInQueue(q, q', p, ios);
        assert p in q' && QueuePosition(q', p) < QueuePosition(q, p);
        assert (0 < d[i4 + 1] && d[i4 + 1] < d[i3]);
      }
    }

    assert (0 < d[i4 + 1] && d[i4 + 1] < d[i3]) || sat(i4, goal);
    assert sat(i3, actionGoalDecreaseWithin(PacketReceivedTemporal(b, p), d, r, timefun));
  }
}

lemma Lemma_HostQueueSizeBoundedAfterEmptyHelper<IdType, MessageType>(
  latency_bound:int,
  host:IdType,
  b:Behavior<LEnvironment<IdType, MessageType>>,
  i1:int,
  i2:int,
  burst_size:int,
  receive_period:int
  )
  requires imaptotal(b)
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires HostQueuesLive(b)
  requires TLe(0, i1)
  requires TLe(i1, i2)
  requires 1 <= receive_period
  requires 1 <= burst_size
  requires sat(i1, HostQueueEmptyTemporal(b, host))
  requires sat(i1, always(eventuallynextwithin(ReceiveAttemptedTemporal(b, host), receive_period, BehaviorToTimeMap(b))))
  requires sat(i1, always(NetworkDeliveryRateForHostBoundedTemporal(b, burst_size, burst_size * receive_period + 1, host)))
  ensures  forall i :: i1 <= i <= i2 && host in b[i].hostInfo ==> |b[i].hostInfo[host].queue| <= burst_size
  decreases i2 - i1
{
  TemporalAssist();
  Lemma_EstablishMonotonicFromOpaque(b, 0);
  var i1' := Lemma_HostQueueEmptiesAgain(latency_bound, host, b, i1, burst_size, receive_period);
  if (i1' < i2)
  {
    Lemma_HostQueueSizeBoundedAfterEmptyHelper(latency_bound, host, b, i1', i2, burst_size, receive_period);
  }
}

function{:opaque} QueueBounded<IdType, MessageType>(b:Behavior<LEnvironment<IdType, MessageType>>, host:IdType, burst_size:int):temporal
  requires imaptotal(b)
  ensures  forall i{:trigger sat(i, QueueBounded(b, host, burst_size))} ::
             sat(i, QueueBounded(b, host, burst_size)) <==> (host in b[i].hostInfo ==> |b[i].hostInfo[host].queue| <= burst_size)
{
  stepmap(imap i :: host in b[i].hostInfo ==> |b[i].hostInfo[host].queue| <= burst_size)
}

lemma Lemma_HostQueueSizeBoundedAfterEmpty<IdType, MessageType>(
  latency_bound:int,
  host:IdType,
  b:Behavior<LEnvironment<IdType, MessageType>>,
  i1:int,
  burst_size:int,
  receive_period:int
  )
  requires imaptotal(b)
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires HostQueuesLive(b)
  requires TLe(0, i1)
  requires 1 <= receive_period
  requires 1 <= burst_size
  requires sat(i1, HostQueueEmptyTemporal(b, host))
  requires sat(i1, always(eventuallynextwithin(ReceiveAttemptedTemporal(b, host), receive_period, BehaviorToTimeMap(b))))
  requires sat(i1, always(NetworkDeliveryRateForHostBoundedTemporal(b, burst_size, burst_size * receive_period + 1, host)))
  ensures  sat(i1, always(QueueBounded(b, host, burst_size)))
{
  TemporalAssist();
  forall i2 | TLe(i1, i2)
    ensures sat(i2, QueueBounded(b, host, burst_size))
  {
    if (host in b[i2].hostInfo)
    {
      Lemma_HostQueueSizeBoundedAfterEmptyHelper(latency_bound, host, b, i1, i2, burst_size, receive_period);
      assert |b[i2].hostInfo[host].queue| <= burst_size;
    }
    assert host in b[i2].hostInfo ==> |b[i2].hostInfo[host].queue| <= burst_size;
    assert sat(i2, stepmap(imap i :: host in b[i].hostInfo ==> |b[i].hostInfo[host].queue| <= burst_size));
    assert sat(i2, QueueBounded(b, host, burst_size));
  }
  assert sat(i1, always(QueueBounded(b, host, burst_size)));
}

lemma Lemma_EventuallyEachHostQueueEmpties<IdType, MessageType>(
  latency_bound:int,
  destinations:set<IdType>,
  b:Behavior<LEnvironment<IdType, MessageType>>,
  synchrony_start:int,
  burst_size:int,
  receive_period:int
  )
  requires imaptotal(b)
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires HostQueuesLive(b)
  requires TLe(0, synchrony_start)
  requires 1 <= receive_period
  requires 1 <= burst_size

  // Starting from the synchrony point, each host attempts to receive a packet at least once every receive_period.
  // That is, it performs an I/O that's either a Receive or a TimeoutReceive.
  requires forall host :: host in destinations ==> sat(synchrony_start, always(eventuallynextwithin(ReceiveAttemptedTemporal(b, host), receive_period, BehaviorToTimeMap(b))))

  // Starting from the synchrony point, the network stops overwhelming each host with
  // delivered packets.  That is, there are at most burst_size packets delivered to any host during any period
  // of length <= burst_size * receive_period + 1
  requires forall host :: host in destinations ==> sat(synchrony_start, always(NetworkDeliveryRateForHostBoundedTemporal(b, burst_size, burst_size * receive_period + 1, host)))

  // At some point after the synchrony point, possibly different for each host, that host's queue becomes empty.
  ensures  forall host:: host in destinations ==> sat(synchrony_start, eventual(HostQueueEmptyTemporal(b, host)))
{
  var timefun := BehaviorToTimeMap(b);

  forall host | host in destinations
    ensures sat(synchrony_start, eventual(HostQueueEmptyTemporal(b, host)))
  {
    // If   []t :: <>(goal || d' < d[t]')
    // and  [](0 <= d)
    // then []<>(goal)
    // goal = (|Q| == 0)
    // d = |Q|
    var i0 := synchrony_start;
    var goal := HostQueueEmptyTemporal(b, host);

    var d := imap i :: if host in b[i].hostInfo then |b[i].hostInfo[host].queue| else 0;

    TemporalAssist();
    var start := i0;
    forall i1 | TLe(i0, i1)
      ensures sat(i1, nextOrDecrease(goal, d))
    {
      if (!sat(i1, eventual(or(goal, nextDecrease(i1, d)))))
      {
        assert forall i :: TLe(i1, i) ==> !sat(i, goal);
        assert forall i :: TLe(i1, i) ==> !sat(i, nextDecrease(i1, d));
        assert forall i :: TLe(i1, i) ==> d[i + 1] >= d[i1];
        assert TLe(i1, i1);
        assert !sat(i1, HostQueueEmptyTemporal(b, host));
        assert !(host in b[i1].hostInfo ==> |b[i1].hostInfo[host].queue| == 0);
        assert d[i1] > 0;

        Lemma_EstablishMonotonicFromOpaque(b, i1);

        var bs := burst_size;
        var r := receive_period;
        var p := bs * r;
        forall ensures 1 <= p { lemma_mul_increases(bs, r); }
        forall ensures 0 <= p * (p + 1) { lemma_mul_nonnegative(p, p + 1); }
        forall ensures p * (p + 1) == (p + 1) * p { lemma_mul_auto(); }
        forall ensures bs * p < bs * (p + 1) { lemma_mul_auto(); }

        // In time p * (p + 1), we'll deliver >= bs * (p + 1) messages
        // In time (p + 1) * p, we'll receive <= bs * p messages
        // So in time p * (p + 1) == (p + 1) * p, we'll decrease d by bs

        // use d >= 1 to prove that delivery decrements
        // define decr_action as d' = d - 1
        // define incr_action as d' = d + 1
        // p * (p + 1): |decr_action| >= bs * (p + 1)
        //   p: |decr_action| >= bs
        //     r: |decr_action| >= 1
        // (p * 1) * p: |incr_action| <= bs * p
        //   p + 1: |incr_action| <= bs
        // d' = d + |incr_action| - |decr_action|
        var incr := PacketDeliveredToHostTemporal(b, host);
        var decr := ReceiveAttemptedTemporal(b, host);

        assert TLe(i1, i1);
        forall ensures sat(i1, countWithinGe(bs * (p + 1), decr, p * (p + 1), timefun))
        {
          Lemma_CountWithinGeOne(i1, decr, r, timefun);
          Lemma_CountWithinGeMultiple(i1, bs, 1, decr, r, timefun);
          Lemma_CountWithinGeMultiple(i1, p + 1, bs, decr, p, timefun);
        }
                
        forall ensures sat(i1, countWithinLe(bs * p, incr, p * (p + 1), timefun))
        {
          assert sat(synchrony_start,
                     always(NetworkDeliveryRateForHostBoundedTemporal(b, burst_size, burst_size * receive_period + 1, host)));
          assert sat(i1, always(NetworkDeliveryRateForHostBoundedTemporal(b, burst_size, burst_size * receive_period + 1, host)));
          assert sat(i1, always(countWithinLe(bs, incr, p + 1, timefun)));
          Lemma_DeliverIsInstantaneous(b, i1, host);
          Lemma_CountWithinLeMultiple(i1, p, bs, incr, p + 1, timefun);
        }

        var nIncr:int := bs * p;
        var nDecr:int := bs * (p + 1);
        var span := p * (p + 1);
        assert sat(i1, countWithinLe(nIncr, incr, span, timefun));
        assert sat(i1, countWithinGe(nDecr, decr, span, timefun));

        forall i2 {:trigger TLe(i1, i2)} | TLe(i1, i2)
          ensures || (sat(i2, PacketDeliveredToHostTemporal(b, host)) && !sat(i2, ReceiveAttemptedTemporal(b, host)) && d[i2 + 1] == d[i2] + 1)
                  || (!sat(i2, PacketDeliveredToHostTemporal(b, host)) && sat(i2, ReceiveAttemptedTemporal(b, host)) && d[i2 + 1] < d[i2])
                  || (!sat(i2, PacketDeliveredToHostTemporal(b, host)) && !sat(i2, ReceiveAttemptedTemporal(b, host)) && d[i2 + 1] == d[i2]);
        {
          Lemma_DeliverIncrReceiveDecr(i1, i2, b, host, d);
        }

        var i2 := Lemma_CountIncrDecr(i1, d, nIncr, nDecr, incr, decr, span, timefun);
        assert nDecr > 0;
        assert TLe(i1, i2 - 1);
        assert nIncr < nDecr;
        assert d[i2] < d[i1];
        assert sat(i2, stepDecrease(i1, d));
        assert i2 - 1 + 1 == i2;
        assert sat(i2 - 1 + 1, stepDecrease(i1, d));
        assert sat(i2 - 1, nextDecrease(i1, d));
        assert !sat(i2 - 1, nextDecrease(i1, d));
        assert false; // proof by contradiction
      }
      var i2 :| TLe(i1, i2) && sat(i2, or(goal, nextDecrease(i1, d)));
      assert sat(i1, eventual(or(goal, nextDecrease(i1, d))));
    }
    assert imaptotal(d);
    assert forall i :: start <= i ==> 0 <= d[i];
    assert sat(start, always(nextOrDecrease(goal, d)));
    Lemma_EventuallyNext(i0, d, goal);
    assert sat(start, always(eventual(goal)));
  }
}

lemma Lemma_EventuallyAllPacketsAlwaysReceivedInTimeHelper3<IdType(!new), MessageType(!new)>(
  synchrony_start:int,
  latency_bound:int,
  sources:set<IdType>,
  destinations:set<IdType>,
  b:Behavior<LEnvironment<IdType, MessageType>>,
  burst_size:int,
  receive_period:int
  ) returns
  (processing_bound:int)
  requires imaptotal(b)
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires HostQueuesLive(b)
  requires TLe(0, synchrony_start)
  requires 1 <= receive_period
  requires 1 <= burst_size

  // Eventually we reach a point where packets sent between these hosts are delivered within latency_bound.
  requires sat(synchrony_start, always(PacketsSynchronousForHostsTemporal(b, latency_bound, sources, destinations)))

  // Each of the destinations eventually reaches a point where it attempts to receive a packet at least once every receive_period.
  // That is, it performs an I/O that's either a Receive or a TimeoutReceive.
  requires forall host :: host in destinations ==> sat(synchrony_start, always(eventuallynextwithin(ReceiveAttemptedTemporal(b, host), receive_period, BehaviorToTimeMap(b))))

  requires forall host :: host in destinations ==> sat(synchrony_start, always(QueueBounded(b, host, burst_size)));

  // Eventually we reach a point where any packet sent between these hosts is received within burst_size *
  // receive_period after it is sent.
  ensures  sat(synchrony_start, always(AllPacketsReceivedWithinTemporal(b, latency_bound + burst_size * receive_period, sources, destinations)))
  ensures  processing_bound == latency_bound + burst_size * receive_period
{
  forall i1 | TLe(synchrony_start, i1)
    ensures sat(i1, AllPacketsReceivedWithinTemporal(b, latency_bound + burst_size * receive_period, sources, destinations))
  {
    forall p {:trigger PacketSentBetweenHosts(b[i1], p, sources, destinations)} | PacketSentBetweenHosts(b[i1], p, sources, destinations)
      ensures sat(i1, next(eventuallynextwithin(PacketReceivedTemporal(b, p), latency_bound + burst_size * receive_period, BehaviorToTimeMap(b))))
    {
      var timefun := BehaviorToTimeMap(b);
      var bs := burst_size;
      var r := receive_period;
      var lb := latency_bound;
      var goal := PacketReceivedTemporal(b, p);
      assert p.dst in destinations;

      forall ensures (exists i2 :: TLe(i1, i2) && sat(i2, PacketDeliveredTemporal(b, p)) && timefun[i2 + 1] <= timefun[i1+1] + lb)
      {
        TemporalDeduceFromAlways(synchrony_start, i1, PacketsSynchronousForHostsTemporal(b, latency_bound, sources, destinations));
        TemporalDeduceFromAlways(0, i1, EnvironmentNextTemporal(b));
        assert p in b[i1 + 1].sentPackets;
        var i2 := TemporalDeduceFromEventual(i1 + 1, nextbefore(PacketDeliveredTemporal(b, p), timefun[i1 + 1] + lb, timefun));
        Lemma_TimeOnlyAdvancesBetweenSteps(b, i2, i2 + 1);
      }
      var i2 :| TLe(i1, i2) && sat(i2, PacketDeliveredTemporal(b, p)) && timefun[i2 + 1] <= timefun[i1+1] + lb;
      TemporalDeduceFromAlways(0, i2, HostQueuesNextTemporal(b));
      var d := imap i ::
                (if TLe(i2, i) && p.dst in b[i].hostInfo && p in b[i].hostInfo[p.dst].queue
                    then 1 + QueuePosition(b[i].hostInfo[p.dst].queue, p)
                    else 0);
      forall ensures sat(i2 + 1, eventuallynextwithin(goal, r * bs, timefun))
      {
        assert p in b[i2 + 1].hostInfo[p.dst].queue;
        assert TLe(synchrony_start, i2 + 1);
        forall i | TLe(synchrony_start, i) && p.dst in b[i].hostInfo
          ensures |b[i].hostInfo[p.dst].queue| <= bs
        {
          TemporalAssist();
          assert TLe(synchrony_start, i);
          TemporalDeduceFromAlways(synchrony_start, i, QueueBounded(b, p.dst, bs));
          assert |b[i].hostInfo[p.dst].queue| <= bs;
        }
        forall i3 | TLe(i2 + 1, i3)
          ensures sat(i3, actionGoalDecreaseWithin(goal, d, r, timefun))
        {
          TemporalAssist();
          assert TLe(synchrony_start, i3);
          assert sat(i3, eventuallynextwithin(ReceiveAttemptedTemporal(b, p.dst), r, timefun));
          Lemma_EstablishMonotonicFromOpaque(b, i3);
          reveal monotonic_from_opaque();
          var i4 := Lemma_ReceiveAttemptDecr(i2, i3, b, p, d, r, timefun);
          assert sat(i3, actionGoalDecreaseWithin(goal, d, r, timefun));
        }
        forall ensures sat(i2 + 1, eventuallynextwithinspans(d, goal, r, timefun))
        {
          forall ensures sat(i2 + 1, always(actionGoalDecreaseWithin(goal, d, r, timefun)))
          {
            TemporalAssist();
            assert forall i3 :: TLe(i2 + 1, i3) ==> sat(i3, actionGoalDecreaseWithin(goal, d, r, timefun));
            assert sat(i2 + 1, always(actionGoalDecreaseWithin(goal, d, r, timefun)));
          }
          Lemma_EventuallyNextGoalSpans(i2 + 1, d, goal, r, timefun);
        }
        forall ensures sat(i2 + 1, eventuallynextwithin(goal, r * bs, timefun))
        {
          TemporalAssist();
          assert sat(i2 + 1, eventuallynextwithinspans(d, goal, r, timefun));
          assert sat(i2 + 1, eventuallynextwithin(goal, r * d[i2 + 1], timefun));
          assert d[i2 + 1] <= bs;
          forall ensures r * d[i2 + 1] <= r * bs { lemma_mul_inequality_forall(); lemma_mul_auto(); }
          assert sat(i2 + 1, eventuallynextwithin(goal, r * bs, timefun));
        }
      }
      forall ensures sat(i1, next(eventuallynextwithin(goal, lb + bs * r, timefun)))
      {
        var i3 := TemporalDeduceFromEventual(i2 + 1, nextbefore(goal, timefun[i2 + 1] + (r * bs), timefun));
        calc {
          timefun[i3 + 1];
          <= timefun[i2 + 1] + (r * bs);
          == { lemma_mul_auto(); }
             timefun[i2 + 1] + (bs * r);
          <= { assert timefun[i2 + 1] <= timefun[i1 + 1] + lb; }
            (timefun[i1 + 1] + lb) + (bs * r);
          == timefun[i1 + 1] + (lb + (bs * r));
        }
        TemporalEventually(i1 + 1, i3, nextbefore(goal, timefun[i1 + 1] + (lb + bs * r), timefun));
      }
    }
  }
  forall ensures sat(synchrony_start, always(AllPacketsReceivedWithinTemporal(b, latency_bound + burst_size * receive_period, sources, destinations)))
  {
    TemporalAssist();
  }

  processing_bound := latency_bound + burst_size * receive_period;
}

lemma Lemma_EventuallyAllPacketsAlwaysReceivedInTimeHelper2<IdType(!new), MessageType(!new)>(
  synchrony_start:int,
  i1:int,
  latency_bound:int,
  sources:set<IdType>,
  destinations:set<IdType>,
  b:Behavior<LEnvironment<IdType, MessageType>>,
  burst_size:int,
  receive_period:int
  ) returns (
  processing_sync_start:int,
  processing_bound:int
  )
  requires imaptotal(b)
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires HostQueuesLive(b)
  requires TLe(0, synchrony_start)
  requires TLe(synchrony_start, i1)
  requires 1 <= receive_period
  requires 1 <= burst_size

  // Eventually we reach a point where packets sent between these hosts are delivered within latency_bound.
  requires sat(synchrony_start, always(PacketsSynchronousForHostsTemporal(b, latency_bound, sources, destinations)))

  // Each of the destinations eventually reaches a point where it attempts to receive a packet at least once every receive_period.
  // That is, it performs an I/O that's either a Receive or a TimeoutReceive.
  requires forall host :: host in destinations ==> sat(synchrony_start, always(eventuallynextwithin(ReceiveAttemptedTemporal(b, host), receive_period, BehaviorToTimeMap(b))))

  // Each of the destinations eventually reaches a point after which the network stops overwhelming it with
  // delivered packets.  That is, there are at most burst_size packets delivered to it during any period
  // of length <= burst_size * receive_period + 1
  requires forall host :: host in destinations ==> sat(synchrony_start, always(NetworkDeliveryRateForHostBoundedTemporal(b, burst_size, burst_size * receive_period + 1, host)))

  requires forall host :: host in destinations ==> sat(i1, always(QueueBounded(b, host, burst_size)))

  // Eventually we reach a point where any packet sent between these hosts is received within burst_size *
  // receive_period after it is sent.
  ensures  synchrony_start <= processing_sync_start
  ensures  processing_bound == latency_bound + burst_size * receive_period
  ensures  sat(processing_sync_start, always(AllPacketsReceivedWithinTemporal(b, latency_bound + burst_size * receive_period, sources, destinations)))
{
  Lemma_AlwaysImpliesLaterAlways(synchrony_start, i1, PacketsSynchronousForHostsTemporal(b, latency_bound, sources, destinations));
  forall host | host in destinations
    ensures sat(i1, always(eventuallynextwithin(ReceiveAttemptedTemporal(b, host), receive_period, BehaviorToTimeMap(b))))
    ensures sat(i1, always(NetworkDeliveryRateForHostBoundedTemporal(b, burst_size, burst_size * receive_period + 1, host)))
  {
    Lemma_AlwaysImpliesLaterAlways(synchrony_start, i1,
                                   eventuallynextwithin(ReceiveAttemptedTemporal(b, host), receive_period, BehaviorToTimeMap(b)));
    Lemma_AlwaysImpliesLaterAlways(synchrony_start, i1,
                                   NetworkDeliveryRateForHostBoundedTemporal(b, burst_size, burst_size * receive_period + 1, host));
  }
  processing_bound :=
    Lemma_EventuallyAllPacketsAlwaysReceivedInTimeHelper3(i1, latency_bound, sources, destinations, b, burst_size, receive_period);
  processing_sync_start := i1;
}

lemma Lemma_EventuallyAllPacketsAlwaysReceivedInTime<IdType(!new), MessageType(!new)>(
  synchrony_start:int,
  latency_bound:int,
  sources:set<IdType>,
  destinations:set<IdType>,
  b:Behavior<LEnvironment<IdType, MessageType>>,
  burst_size:int,
  receive_period:int
  ) returns (
  processing_sync_start:int,
  processing_bound:int
  )
  requires imaptotal(b)
  requires LEnvironment_BehaviorSatisfiesSpec(b)
  requires HostQueuesLive(b)
  requires TLe(0, synchrony_start)
  requires 1 <= receive_period
  requires 1 <= burst_size

  // All packets sent between these hosts are delivered within latency_bound.
  requires NetworkSynchronousForHosts(b, synchrony_start, latency_bound, sources, destinations)

  // The network does not overwhelm any of the destinations with delivered packets.  That is,
  // there are at most burst_size packets delivered to it during any period of
  // length <= burst_size * receive_period + 1.
  requires NetworkDeliveryRateBoundedForHosts(b, synchrony_start, burst_size, burst_size * receive_period + 1, destinations)

  // Each of the destinations attempts to receive a packet at least once every receive_period.
  // That is, it performs an I/O that's either a Receive or a TimeoutReceive.
  requires forall host :: host in destinations ==> sat(synchrony_start, always(eventuallynextwithin(ReceiveAttemptedTemporal(b, host), receive_period, BehaviorToTimeMap(b))))

  // Any packet sent between these hosts is received within burst_size * receive_period after it is sent.
  ensures  synchrony_start <= processing_sync_start
  ensures  processing_bound == latency_bound + burst_size * receive_period
  ensures  sat(processing_sync_start, always(AllPacketsReceivedWithinTemporal(b, latency_bound + burst_size * receive_period, sources, destinations)))
{
  Lemma_EventuallyEachHostQueueEmpties(latency_bound, destinations, b, synchrony_start, burst_size, receive_period);

  forall host | host in destinations
    ensures exists i0a :: TLe(synchrony_start, i0a) && sat(i0a, always(QueueBounded(b, host, burst_size)))
  {
    TemporalAssist();
    var i0a :| TLe(synchrony_start, i0a) && sat(i0a, HostQueueEmptyTemporal(b, host));
    Lemma_HostQueueSizeBoundedAfterEmpty(latency_bound, host, b, i0a, burst_size, receive_period);
  }
  var i0as := set host | host in destinations ::
                (var i0a :| TLe(synchrony_start, i0a) && sat(i0a, always(QueueBounded(b, host, burst_size))); i0a);
  var i0s := {synchrony_start} + i0as;
  var i1 := intsetmax(i0s);

  assert synchrony_start <= i1;
  assert forall i :: i in i0as ==> i <= i1;

  forall host | host in destinations
    ensures sat(i1, always(QueueBounded(b, host, burst_size)))
  {
    var i0a :| i0a in i0as && sat(i0a, always(QueueBounded(b, host, burst_size)));
    assert i0a <= i1;
    TemporalAssist();
  }
  processing_sync_start, processing_bound :=
    Lemma_EventuallyAllPacketsAlwaysReceivedInTimeHelper2(synchrony_start, i1, latency_bound, sources, destinations,
                                                          b, burst_size, receive_period);
}

} 
