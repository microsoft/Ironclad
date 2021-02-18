include "AppInterface.i.dfy"
include "LearnerState.i.dfy"

module LiveRSL__LearnerModel_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__AppInterface_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__Environment_i
import opened LiveRSL__ExecutorState_i
import opened LiveRSL__Learner_i
import opened LiveRSL__LearnerState_i
import opened LiveRSL__Message_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__ReplicaConstantsState_i
import opened LiveRSL__Types_i
import opened Collections__Maps_i
import opened Collections__Sets_i
import opened Common__NodeIdentity_i
import opened Common__SeqIsUnique_i
import opened Common__SeqIsUniqueDef_i
import opened Common__UdpClient_i
import opened Concrete_NodeIdentity_i

lemma lemma_Received2bPacketsSameSizeAsAbstraction(l_learner_tuple:CLearnerTuple, h_learner_tuple:LearnerTuple)
  requires LearnerTupleIsAbstractable(l_learner_tuple)
  requires h_learner_tuple == AbstractifyCLearnerTupleToLearnerTuple(l_learner_tuple)
  requires SeqIsUnique(l_learner_tuple.received_2b_message_senders)
  ensures  |l_learner_tuple.received_2b_message_senders| == |h_learner_tuple.received_2b_message_senders|
  decreases |l_learner_tuple.received_2b_message_senders|
{
  forall i1, i2
    ensures 0 <= i1 < |l_learner_tuple.received_2b_message_senders| && 0 <= i2 < |l_learner_tuple.received_2b_message_senders| && i1 != i2 ==>
                l_learner_tuple.received_2b_message_senders[i1] != l_learner_tuple.received_2b_message_senders[i2]
  {
    reveal SeqIsUnique();
  }

  if |l_learner_tuple.received_2b_message_senders| > 0
  {
    var src := l_learner_tuple.received_2b_message_senders[0];
    var l_received_2b_message_senders' := l_learner_tuple.received_2b_message_senders[1..];
    var l_learner_tuple' := CLearnerTuple(l_received_2b_message_senders', l_learner_tuple.candidate_learned_value);
    var h_learner_tuple' := AbstractifyCLearnerTupleToLearnerTuple(l_learner_tuple');

    assert src in l_learner_tuple.received_2b_message_senders;

    forall x | x in l_received_2b_message_senders'
      ensures EndPointIsValidIPV4(x)
      ensures AbstractifyEndPointToNodeIdentity(x) in h_learner_tuple'.received_2b_message_senders
    {
      var idx :| 0 <= idx < |l_received_2b_message_senders'| && x == l_received_2b_message_senders'[idx];
      assert x == l_learner_tuple.received_2b_message_senders[idx+1];
      assert x in l_learner_tuple.received_2b_message_senders[1..];
      assert AbstractifyEndPointToNodeIdentity(x) in AbstractifyEndPointsToNodeIdentities(l_learner_tuple.received_2b_message_senders[1..]);
      assert AbstractifyEndPointToNodeIdentity(x) in MapSeqToSet(AbstractifyEndPointsToNodeIdentities(l_learner_tuple.received_2b_message_senders[1..]), u=>u);
    }

    forall x | EndPointIsValidIPV4(x) && AbstractifyEndPointToNodeIdentity(x) in h_learner_tuple'.received_2b_message_senders
      ensures x in l_received_2b_message_senders'
    {
      var idx :| 0 <= idx < |l_learner_tuple'.received_2b_message_senders| && AbstractifyEndPointToNodeIdentity(x) == AbstractifyEndPointToNodeIdentity(l_learner_tuple'.received_2b_message_senders[idx]);
      lemma_AbstractifyEndPointToNodeIdentity_injective(x, l_learner_tuple'.received_2b_message_senders[idx]);
      assert x == l_learner_tuple'.received_2b_message_senders[idx];
      assert l_learner_tuple.received_2b_message_senders[idx+1] == l_learner_tuple'.received_2b_message_senders[idx];
      assert x == l_learner_tuple.received_2b_message_senders[idx+1];
    }

    assert forall x :: x in h_learner_tuple.received_2b_message_senders ==> x in h_learner_tuple'.received_2b_message_senders || x == AbstractifyEndPointToNodeIdentity(src);

    forall x | x in h_learner_tuple'.received_2b_message_senders || x == AbstractifyEndPointToNodeIdentity(src)
      ensures x in h_learner_tuple.received_2b_message_senders
    {
      if x == AbstractifyEndPointToNodeIdentity(src)
      {
        assert src in l_learner_tuple.received_2b_message_senders;
        assert x in AbstractifyEndPointsToNodeIdentities(l_learner_tuple.received_2b_message_senders);
        assert x in MapSeqToSet(AbstractifyEndPointsToNodeIdentities(l_learner_tuple.received_2b_message_senders), u=>u);
        assert x in h_learner_tuple.received_2b_message_senders;
      }
      else
      {
        assert x in h_learner_tuple.received_2b_message_senders;
        var idx :| 0 <= idx < |l_learner_tuple'.received_2b_message_senders| && x == AbstractifyEndPointToNodeIdentity(l_learner_tuple'.received_2b_message_senders[idx]);
        assert l_learner_tuple.received_2b_message_senders[idx+1] == l_learner_tuple'.received_2b_message_senders[idx];
        assert x == AbstractifyEndPointToNodeIdentity(l_learner_tuple.received_2b_message_senders[idx+1]);
      }
    }

    assert h_learner_tuple.received_2b_message_senders == h_learner_tuple'.received_2b_message_senders + {AbstractifyEndPointToNodeIdentity(src)};
    reveal SeqIsUnique();
    lemma_Received2bPacketsSameSizeAsAbstraction(l_learner_tuple', h_learner_tuple');
  }
}


lemma lemma_AbstractifyCLearnerTupleOfOneSource(l_tup:CLearnerTuple, h_tup:LearnerTuple, src:EndPoint)
  requires l_tup.received_2b_message_senders == [src]
  requires EndPointIsValidIPV4(src)
  requires LearnerTupleIsAbstractable(l_tup)
  requires h_tup.received_2b_message_senders == {AbstractifyEndPointToNodeIdentity(src)}
  requires h_tup.candidate_learned_value == AbstractifyCRequestBatchToRequestBatch(l_tup.candidate_learned_value)
  ensures  h_tup == AbstractifyCLearnerTupleToLearnerTuple(l_tup)
{
  var s := AbstractifyCLearnerTupleToLearnerTuple(l_tup).received_2b_message_senders;

  forall x
    ensures x in s <==> x in h_tup.received_2b_message_senders
  {
    if x in s
    {
      assert x == AbstractifyEndPointToNodeIdentity(src);
      assert x in h_tup.received_2b_message_senders;
    }
    if x in h_tup.received_2b_message_senders
    {
      assert src in [src] && x == AbstractifyEndPointToNodeIdentity(src);
      assert x in AbstractifyEndPointsToNodeIdentities([src]);
      assert x in s;
    }
  }

  assert s == h_tup.received_2b_message_senders;
}

lemma lemma_AddingSourceToSequenceAddsToSet(source:EndPoint, sseq1:seq<EndPoint>, sset1:set<NodeIdentity>,
                                            sseq2:seq<EndPoint>, sset2:set<NodeIdentity>)
  requires EndPointIsValidIPV4(source)
  requires SeqOfEndPointsIsAbstractable(sseq1)
  requires SeqOfEndPointsIsAbstractable(sseq2)
  requires sset1 == MapSeqToSet(AbstractifyEndPointsToNodeIdentities(sseq1), x=>x)
  requires sset2 == sset1 + {AbstractifyEndPointToNodeIdentity(source)}
  requires sseq2 == sseq1 + [source]
  ensures  sset2 == MapSeqToSet(AbstractifyEndPointsToNodeIdentities(sseq2), x=>x)
{
  var sset2_alt := MapSeqToSet(AbstractifyEndPointsToNodeIdentities(sseq2), x=>x);

  forall x
    ensures x in sset2 <==> x in sset2_alt
  {
    if x in sset2
    {
      if x in sset1
      {
        assert x in MapSeqToSet(AbstractifyEndPointsToNodeIdentities(sseq1), a=>a);
        assert x in AbstractifyEndPointsToNodeIdentities(sseq1);
        var src :| src in sseq1 && x == AbstractifyEndPointToNodeIdentity(src);
        assert src in sseq2;
        assert AbstractifyEndPointToNodeIdentity(src) in AbstractifyEndPointsToNodeIdentities(sseq2);
        assert AbstractifyEndPointToNodeIdentity(src) in sset2_alt;
        assert x in sset2_alt;
      }
      else
      {
        assert x == AbstractifyEndPointToNodeIdentity(source);
        assert source in sseq2;
        assert AbstractifyEndPointToNodeIdentity(source) in AbstractifyEndPointsToNodeIdentities(sseq2);
        assert AbstractifyEndPointToNodeIdentity(source) in sset2_alt;
        assert x in sset2_alt;
      }
    }
    if x in sset2_alt
    {
      assert x in AbstractifyEndPointsToNodeIdentities(sseq2);
      var src :| src in sseq2 && x == AbstractifyEndPointToNodeIdentity(src);
      if src in sseq1
      {
        assert AbstractifyEndPointToNodeIdentity(src) in AbstractifyEndPointsToNodeIdentities(sseq1);
        assert x in AbstractifyEndPointsToNodeIdentities(sseq1);
        assert x in MapSeqToSet(AbstractifyEndPointsToNodeIdentities(sseq1), a=>a);
        assert x in sset1;
        assert x in sset2;
      }
      else
      {
        assert src == source;
        lemma_AbstractifyEndPointToNodeIdentity_injective(src, source);
        assert x in sset2;
      }
    }
  }
}

predicate Eq_LLearner(x:LLearner, y:LLearner)
{
  && x.constants == y.constants
  && x.max_ballot_seen == y.max_ballot_seen
  && x.unexecuted_learner_state == y.unexecuted_learner_state
}

method LearnerModel_Process2b(learner:CLearnerState, executor:ExecutorState, packet:CPacket) returns (learner':CLearnerState)
  requires LearnerState_Process2b__Preconditions(learner, executor, packet)
  requires Marshallable_2b(packet.msg)
  ensures LearnerState_Process2b__Postconditions(learner, executor, packet, learner')
{
  lemma_AbstractifyEndPointsToNodeIdentities_properties(learner.rcs.all.config.replica_ids);
  lemma_AbstractifyCOperationNumberToOperationNumber_isInjective();

  var msg := packet.msg;
  var src := packet.src;
  var opn := msg.opn_2b;
  var isBalLt1 := CBalLt(msg.bal_2b, learner.max_ballot_seen);
  var isBalLt2 := CBalLt(learner.max_ballot_seen, msg.bal_2b);
  var srcIsReplica := src in learner.rcs.all.config.replica_ids;
  ghost var r_learner := AbstractifyLearnerStateToLLearner(learner);
  ghost var r_packet := AbstractifyCPacketToRslPacket(packet);
  ghost var r_opn := AbstractifyCOperationNumberToOperationNumber(opn);

  assert srcIsReplica <==> AbstractifyCPacketToRslPacket(packet).src in AbstractifyReplicaConstantsStateToLReplicaConstants(learner.rcs).all.config.replica_ids;
  lemma_AbstractifyCLearnerTuplesToLearnerTuples_properties(learner.unexecuted_ops);

  if opn in learner.unexecuted_ops {
    assert CLearnerTupleIsValid(learner.unexecuted_ops[opn]);
    lemma_AbstractifyEndPointsToNodeIdentities_properties(learner.unexecuted_ops[opn].received_2b_message_senders);
  }

  if (!srcIsReplica || isBalLt1)
  {
    learner' := learner;
  }
  else if (isBalLt2)
  {
    var tup' := CLearnerTuple([packet.src], msg.val_2b);
    learner' :=
            learner.(
                max_ballot_seen := msg.bal_2b,
                unexecuted_ops := map[opn := tup']);
    ghost var r_learner' := AbstractifyLearnerStateToLLearner(learner');
    lemma_AbstractifyCLearnerTuplesToLearnerTuples_properties(learner'.unexecuted_ops);

    lemma_AbstractifyCLearnerTuplesToLearnerTuples_properties(map []);

    ghost var r_tup' := LearnerTuple({r_packet.src}, r_packet.msg.val_2b);
    ghost var r'_learner := r_learner.(max_ballot_seen := r_packet.msg.bal_2b,
                                       unexecuted_learner_state := map[r_opn := r_tup']);

    lemma_AbstractifyCLearnerTupleOfOneSource(tup', r_tup', packet.src);

    assert r_tup'.received_2b_message_senders == AbstractifyCLearnerTupleToLearnerTuple(tup').received_2b_message_senders;
    assert r_tup'.candidate_learned_value == AbstractifyCLearnerTupleToLearnerTuple(tup').candidate_learned_value;
    assert r_tup' == AbstractifyCLearnerTupleToLearnerTuple(tup');
    assert Eq_LLearner(r_learner', r'_learner);

    forall ensures CLearnerTupleIsValid(tup')
    {
      reveal SeqIsUnique();
    }      
  }
  else if (opn !in learner.unexecuted_ops)
  {
    assert AbstractifyCOperationNumberToOperationNumber(opn) !in AbstractifyLearnerStateToLLearner(learner).unexecuted_learner_state;
    var tup' := CLearnerTuple([packet.src], msg.val_2b);
    learner' := learner.(unexecuted_ops := learner.unexecuted_ops[opn := tup']);
    ghost var r_learner' := AbstractifyLearnerStateToLLearner(learner');
    ghost var r_tup' := LearnerTuple({r_packet.src}, r_packet.msg.val_2b);
    ghost var r'_learner := r_learner.(unexecuted_learner_state := r_learner.unexecuted_learner_state[r_opn := r_tup']);

    lemma_AbstractifyCLearnerTupleOfOneSource(tup', r_tup', packet.src);

    assert r_tup'.received_2b_message_senders == AbstractifyCLearnerTupleToLearnerTuple(tup').received_2b_message_senders;
    assert r_tup'.candidate_learned_value == AbstractifyCLearnerTupleToLearnerTuple(tup').candidate_learned_value;
    assert r_tup' == AbstractifyCLearnerTupleToLearnerTuple(tup');
    assert Eq_LLearner(r_learner', r'_learner);

    forall ensures CLearnerTupleIsValid(tup')
    {
      reveal SeqIsUnique();
    }
  }  
  else if packet.src in learner.unexecuted_ops[opn].received_2b_message_senders 
  {
    learner' := learner;
  }
  else 
  {
    var tup := learner.unexecuted_ops[opn];
    var tup' := tup.(received_2b_message_senders := tup.received_2b_message_senders + [packet.src]);
    learner' := learner.(unexecuted_ops := learner.unexecuted_ops[opn := tup']);
    ghost var r_learner' := AbstractifyLearnerStateToLLearner(learner');

    ghost var r_tup := r_learner.unexecuted_learner_state[r_opn];
    ghost var r_tup' := r_tup.(received_2b_message_senders := r_tup.received_2b_message_senders + {r_packet.src});
    ghost var r'_learner := r_learner.(unexecuted_learner_state := r_learner.unexecuted_learner_state[r_opn := r_tup']);

    lemma_AddingSourceToSequenceAddsToSet(packet.src, tup.received_2b_message_senders, r_tup.received_2b_message_senders,
                                          tup'.received_2b_message_senders, r_tup'.received_2b_message_senders);
                                         
    assert r_tup'.received_2b_message_senders == AbstractifyCLearnerTupleToLearnerTuple(tup').received_2b_message_senders;
    assert r_tup'.candidate_learned_value == AbstractifyCLearnerTupleToLearnerTuple(tup').candidate_learned_value;
    assert r_tup' == AbstractifyCLearnerTupleToLearnerTuple(tup');
    assert Eq_LLearner(r_learner', r'_learner);
    EstablishAppendToUniqueSeq(tup.received_2b_message_senders, packet.src, tup'.received_2b_message_senders);
  }
}

method LearnerModel_ForgetDecision(learner:CLearnerState, opn:COperationNumber) returns (learner':CLearnerState)
  requires LearnerState_ForgetDecision__Preconditions(learner, opn)
  ensures LearnerState_ForgetDecision__Postconditions(learner, opn, learner')
{
  lemma_AbstractifyCLearnerTuplesToLearnerTuples_properties(learner.unexecuted_ops);
  if (opn in learner.unexecuted_ops)
  {
    learner' := learner.(unexecuted_ops := RemoveElt(learner.unexecuted_ops, opn));
    lemma_map_remove_one(learner.unexecuted_ops, learner'.unexecuted_ops, opn);
    //assert AbstractifyCOperationNumberToOperationNumber(opn) in AbstractifyCLearnerTuplesToLearnerTuples(learner.unexecuted_ops);
    lemma_AbstractifyCLearnerTuplesToLearnerTuples_properties(learner'.unexecuted_ops);
    //lemma_map_remove_one(AbstractifyCLearnerTuplesToLearnerTuples(learner.unexecuted_ops), AbstractifyCLearnerTuplesToLearnerTuples(learner'.unexecuted_ops), AbstractifyCOperationNumberToOperationNumber(opn));
  }
  else
  {
    learner' := learner;
  }
}

lemma lemma_MapEquality<U,V>(m1:map<U,V>, m2:map<U,V>)
  requires forall u :: (u in m1 <==> u in m2)
  requires forall u :: u in m1 ==> m1[u] == m2[u]
  ensures m1 == m2
{
}

lemma lemma_ForgetOperationsBeforeMap(m_before:map<COperationNumber, CLearnerTuple>, m_after:map<COperationNumber, CLearnerTuple>, ops_complete:COperationNumber)
  requires m_after == map op | op in m_before && op.n >= ops_complete.n :: m_before[op]
  requires CLearnerTuplesAreAbstractable(m_before)
  ensures  var rm := AbstractifyCLearnerTuplesToLearnerTuples(m_before);
           var rm_new := map op | op in rm && op >= AbstractifyCOperationNumberToOperationNumber(ops_complete) :: rm[op];
           rm_new == AbstractifyCLearnerTuplesToLearnerTuples(m_after)
{
  lemma_AbstractifyCLearnerTuplesToLearnerTuples_properties(m_before);
  lemma_AbstractifyCLearnerTuplesToLearnerTuples_properties(m_after);

  var r_before := AbstractifyCLearnerTuplesToLearnerTuples(m_before);
  var r_after := AbstractifyCLearnerTuplesToLearnerTuples(m_after);
  var r_op := AbstractifyCOperationNumberToOperationNumber(ops_complete);
  var rm_new := map op | op in r_before && op >= r_op :: r_before[op];

  forall o | o in r_after
    ensures o in rm_new && rm_new[o] == r_after[o]
  {
    var co :| co in m_after && AbstractifyCOperationNumberToOperationNumber(co) == o;
    assert co in m_before && co.n >= ops_complete.n;
    var r_co := AbstractifyCOperationNumberToOperationNumber(co);
    assert r_co in r_before;
    assert r_co >= r_op;
    assert r_co in rm_new;
  }

  forall o | o in rm_new
    ensures o in r_after && rm_new[o] == r_after[o]
  {
  }
  lemma_MapEquality(rm_new, r_after);
}

lemma lemma_LearnerStateForgetOperationsBeforePostconditions(learner:CLearnerState, ops_complete:COperationNumber, learner':CLearnerState)
  requires LearnerState_ForgetOperationsBefore__Preconditions(learner, ops_complete)
  requires LearnerState_CommonPostconditions(learner, learner')
  requires learner'.max_ballot_seen == learner.max_ballot_seen
  requires learner'.unexecuted_ops == map op | op in learner.unexecuted_ops && op.n >= ops_complete.n :: learner.unexecuted_ops[op]
  //requires forall opn :: opn in learner'.unexecuted_ops ==> opn in learner.unexecuted_ops
  ensures LearnerState_ForgetOperationsBefore__Postconditions(learner, ops_complete, learner')
{
  ghost var r_learner := AbstractifyLearnerStateToLLearner(learner);
  ghost var r_learner' := AbstractifyLearnerStateToLLearner(learner');
//  var r_unexecutedOps  := r_learner.unexecuted_learner_state;
//  var r_unexecutedOps' := r_learner'.unexecuted_learner_state;
  var r_opsComplete := AbstractifyCOperationNumberToOperationNumber(ops_complete);

  var r'_learner := r_learner.(unexecuted_learner_state := (map op | op in r_learner.unexecuted_learner_state && op >= r_opsComplete :: r_learner.unexecuted_learner_state[op]));

  /*
  assert forall o :: (o in r'_learner.unexecuted_learner_state <==> o in r_learner'.unexecuted_learner_state);
  assert forall o :: o in r'_learner.unexecuted_learner_state ==> r'_learner.unexecuted_learner_state[o] == r_learner'.unexecuted_learner_state[o];

  ghost var m1 := r'_learner.unexecuted_learner_state;
  ghost var m2 := r_learner'.unexecuted_learner_state;
  assert forall o :: (o in m1 <==> o in m2);
  assert forall o :: o in m1 ==> m1[o] == m2[o];
  assert (forall o :: (o in m1 <==> o in m2)) && (forall o :: o in m1 ==> m1[o] == m2[o]);
  lemma_MapEquality(m1, m2);
  assert m1 == m2;
  */
  lemma_ForgetOperationsBeforeMap(learner.unexecuted_ops, learner'.unexecuted_ops, ops_complete);
  assert r'_learner.unexecuted_learner_state == r_learner'.unexecuted_learner_state;
  assert Eq_LLearner(r'_learner, r_learner');
  /*
  lemma_AbstractifyCLearnerTuplesToLearnerTuples_properties(learner.unexecuted_ops);

  var rOpnComplete := AbstractifyCOperationNumberToOperationNumber(ops_complete);
  var r1 := AbstractifyLearnerStateToLLearner(learner).unexecuted_learner_state;
  var r2 := AbstractifyCLearnerTuplesToLearnerTuples(learner.unexecuted_ops);
  assert r1 == r2;
  var r1' := AbstractifyLearnerStateToLLearner(learner').unexecuted_learner_state;
  var r2' := AbstractifyCLearnerTuplesToLearnerTuples(learner'.unexecuted_ops);
  assert r1' == r2';
  var setO := set o | o in r1 && o >= rOpnComplete;
  forall o | o in domain(r1')
    ensures o in setO
  {
    assert o in r1 && o >= rOpnComplete;
  }
  forall o | o in setO
    ensures o in domain(r1')
  {}
  assert domain(r1') == set o | o in r1 && o >= rOpnComplete;
  assert forall o :: o in domain(r1') ==> r1'[o] == r1[o];
  assert r1' == map o | o in r1 && o >= rOpnComplete :: r1[o];
  assert AbstractifyLearnerStateToLLearner(learner').constants == AbstractifyLearnerStateToLLearner(learner).constants;
  assert learner'.max_ballot_seen == learner.max_ballot_seen;
  assert AbstractifyLearnerStateToLLearner(learner').max_ballot_seen == AbstractifyLearnerStateToLLearner(learner).max_ballot_seen;
  assert AbstractifyLearnerStateToLLearner(learner').learnerState == AbstractifyLearnerStateToLLearner(learner).learnerState;
  assert AbstractifyLearnerStateToLLearner(learner') == AbstractifyLearnerStateToLLearner(learner')[unexecuted_learner_state := r1'];
  var s := AbstractifyLearnerStateToLLearner(learner);
  var s' := AbstractifyLearnerStateToLLearner(learner');
  assert s' == s[unexecuted_learner_state := r1'];
  assert r1' == (map op | op in s.unexecuted_learner_state && op >= rOpnComplete :: s.unexecuted_learner_state[op]);
  assert s' == s[unexecuted_learner_state := (map op | op in s.unexecuted_learner_state && op >= rOpnComplete :: s.unexecuted_learner_state[op])];
  assert LLearnerForgetOperationsBefore(AbstractifyLearnerStateToLLearner(learner), AbstractifyLearnerStateToLLearner(learner'), AbstractifyCOperationNumberToOperationNumber(ops_complete));
  */
}

method LearnerModel_ForgetOperationsBefore(learner:CLearnerState, ops_complete:COperationNumber) returns (learner':CLearnerState)
  requires LearnerState_ForgetOperationsBefore__Preconditions(learner, ops_complete)
  ensures LearnerState_ForgetOperationsBefore__Postconditions(learner, ops_complete, learner')
{
  var unexecuted_ops' := (map op | op in learner.unexecuted_ops && op.n >= ops_complete.n :: learner.unexecuted_ops[op]);
  learner' := learner.(unexecuted_ops := unexecuted_ops');
  lemma_LearnerStateForgetOperationsBeforePostconditions(learner, ops_complete, learner');
}

} 
