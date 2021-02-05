include "../Types.i.dfy"
include "../Configuration.i.dfy"
include "../Proposer.i.dfy"
include "../../../Common/Collections/Sets.i.dfy"
include "../../../../Libraries/Math/mul.i.dfy"
include "../../../../Libraries/Math/div.i.dfy"

module CommonProof__CanonicalizeBallot_i {
import opened LiveRSL__Types_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__Constants_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__Election_i
import opened Collections__Sets_i
import opened Math__mul_i
import opened Math__div_nonlinear_i
import opened Math__div_i
import opened Common__UpperBound_s

predicate IsValidBallot(b:Ballot, c:LConstants)
{
  0 <= b.proposer_id < |c.config.replica_ids|
}

predicate BallotHasSuccessor(b:Ballot, c:LConstants)
{
  || LtUpperBound(b.seqno, c.params.max_integer_val)
  || (b.seqno == c.params.max_integer_val.n && 0 <= b.proposer_id + 1 < |c.config.replica_ids|)
}

//////////////////////////
// CanonicalizeBallot
//////////////////////////

function{:opaque} CanonicalizeBallot(b:Ballot, c:LConstants):int
{
  b.seqno * |c.config.replica_ids| + b.proposer_id
}

lemma lemma_CanonicalizeBallotProperties()
  ensures forall b1:Ballot, b2:Ballot, c:LConstants :: IsValidBallot(b1, c) && IsValidBallot(b2, c) ==>
            && (BalLeq(b1, b2) <==> CanonicalizeBallot(b1, c) <= CanonicalizeBallot(b2, c))
            && (BalLt(b1, b2) <==> CanonicalizeBallot(b1, c) < CanonicalizeBallot(b2, c))
            && (b1 == b2 <==> CanonicalizeBallot(b1, c) == CanonicalizeBallot(b2, c));
{
  reveal CanonicalizeBallot();

  forall b1:Ballot, b2:Ballot, c:LConstants | 0 <= b1.proposer_id < |c.config.replica_ids| && 0 <= b2.proposer_id < |c.config.replica_ids|
    ensures b1.seqno < b2.seqno ==> CanonicalizeBallot(b1, c) < CanonicalizeBallot(b2, c)
  {
    var ids := c.config.replica_ids;

    if b1.seqno < b2.seqno
    {
      calc {
        CanonicalizeBallot(b1, c);
        < b1.seqno * |c.config.replica_ids| + 1 * |ids|;
        == { lemma_mul_is_distributive_add_other_way(|ids|, b1.seqno, 1); } (b1.seqno + 1) * |ids|;
        <= { lemma_mul_properties(); } b2.seqno * |ids|;
        <= CanonicalizeBallot(b2, c);
      }
    }
  }

  forall b1:Ballot, b2:Ballot, c:LConstants | 0 <= b1.proposer_id < |c.config.replica_ids| && 0 <= b2.proposer_id < |c.config.replica_ids|
    ensures b1 != b2 ==> CanonicalizeBallot(b1, c) != CanonicalizeBallot(b2, c)
  {
  }
}

lemma lemma_CanonicalizeBallotPropertiesSpecific(b1:Ballot, b2:Ballot, c:LConstants)
  requires IsValidBallot(b1, c)
  requires IsValidBallot(b2, c)
  ensures  && (BalLeq(b1, b2) <==> CanonicalizeBallot(b1, c) <= CanonicalizeBallot(b2, c))
           && (BalLt(b1, b2) <==> CanonicalizeBallot(b1, c) < CanonicalizeBallot(b2, c))
           && (b1 == b2 <==> CanonicalizeBallot(b1, c) == CanonicalizeBallot(b2, c))
{
  lemma_CanonicalizeBallotProperties();
}

lemma lemma_CanonicalizeSuccessor(b:Ballot, c:LConstants)
  requires 0 <= b.proposer_id < |c.config.replica_ids|
  requires BallotHasSuccessor(b, c)
  ensures  CanonicalizeBallot(ComputeSuccessorView(b, c), c) == CanonicalizeBallot(b, c) + 1
{
  reveal CanonicalizeBallot();
  lemma_CanonicalizeBallotProperties();

  var ids := c.config.replica_ids;
  var params := c.params;

  if b.proposer_id + 1 >= |c.config.replica_ids|
  {
    calc {
      CanonicalizeBallot(ComputeSuccessorView(b, c), c);
      CanonicalizeBallot(Ballot(b.seqno + 1, 0), c);
      (b.seqno + 1) * |ids| + 0;
        { lemma_mul_is_distributive_add_other_way(|ids|, b.seqno, 1); }
      b.seqno * |ids| + 1 * |ids|;
      b.seqno * |ids| + |ids|;
      b.seqno * |ids| + |ids| - 1 + 1;
      CanonicalizeBallot(b, c) + 1;
    }
  }
}

lemma lemma_NothingBetweenViewAndSuccessor(b:Ballot, b':Ballot, c:LConstants)
  requires IsValidBallot(b, c)
  requires BallotHasSuccessor(b, c)
  requires IsValidBallot(b', c)
  ensures  !BalLt(b, b') || !BalLt(b', ComputeSuccessorView(b, c))
{
  lemma_CanonicalizeBallotProperties();

  var b'' := ComputeSuccessorView(b, c);

  if BalLt(b, b') && BalLt(b', b'')
  {
    lemma_CanonicalizeSuccessor(b, c);
    assert CanonicalizeBallot(b, c) < CanonicalizeBallot(b', c) < CanonicalizeBallot(b, c) + 1;
    assert false;
  }
}

function DecanonicalizeBallot(i:int, c:LConstants):Ballot
  requires WellFormedLConfiguration(c.config)
{
  Ballot(i / |c.config.replica_ids|, i % |c.config.replica_ids|)
}

lemma lemma_DecanonicalizeBallotProperties(i:int, c:LConstants)
  requires i >= 0
  requires WellFormedLConfiguration(c.config)
  ensures CanonicalizeBallot(DecanonicalizeBallot(i, c), c) == i
{
  calc {
    CanonicalizeBallot(DecanonicalizeBallot(i, c), c);
    CanonicalizeBallot(Ballot(i / |c.config.replica_ids|, i % |c.config.replica_ids|), c);
      { reveal_CanonicalizeBallot(); }
    (i / |c.config.replica_ids|) * |c.config.replica_ids| + (i % |c.config.replica_ids|);
      { lemma_mul_is_commutative(i / |c.config.replica_ids|, |c.config.replica_ids|); }
    |c.config.replica_ids| * (i / |c.config.replica_ids|) + i % |c.config.replica_ids|;
      { lemma_fundamental_div_mod(i, |c.config.replica_ids|); }
    i;
  }
}

function ComputePredecessorView(b:Ballot, c:LConstants):Ballot
  requires CanonicalizeBallot(b, c) > 0
  requires WellFormedLConfiguration(c.config)
{
  DecanonicalizeBallot(CanonicalizeBallot(b, c) - 1, c)
}

lemma lemma_ComputePredecessorViewProperties(b:Ballot, c:LConstants)
  requires WellFormedLConfiguration(c.config)
  requires IsValidBallot(b, c)
  requires CanonicalizeBallot(b, c) > 0
  requires LeqUpperBound(b.seqno, c.params.max_integer_val)
  ensures  BallotHasSuccessor(ComputePredecessorView(b, c), c)
  ensures  CanonicalizeBallot(ComputePredecessorView(b, c), c) == CanonicalizeBallot(b, c) - 1
  ensures  ComputeSuccessorView(ComputePredecessorView(b, c), c) == b
{
  var i := CanonicalizeBallot(b, c);
  var b' := DecanonicalizeBallot(i-1, c);

  lemma_DecanonicalizeBallotProperties(i-1, c);
  lemma_CanonicalizeBallotPropertiesSpecific(ComputePredecessorView(b, c), b, c);
  lemma_CanonicalizeBallotPropertiesSpecific(b, ComputeSuccessorView(ComputePredecessorView(b, c), c), c);

  lemma_CanonicalizeSuccessor(b', c);
}

lemma lemma_ComputeSuccessorViewProducesValidBallot(b:Ballot, c:LConstants)
  requires WellFormedLConfiguration(c.config)
  requires IsValidBallot(b, c)
  ensures  IsValidBallot(ComputeSuccessorView(b, c), c)
{
}

} 
