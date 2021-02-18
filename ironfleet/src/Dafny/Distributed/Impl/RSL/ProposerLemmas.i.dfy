include "ProposerState.i.dfy"

module LiveRSL__ProposerLemmas_i {
import opened Native__Io_s
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__Proposer_i
import opened LiveRSL__ProposerState_i
import opened Collections__Sets_i
import opened Common__SeqIsUnique_i

predicate SetOfMessage1b(S:set<CPacket>)
{
  forall p :: p in S ==> p.msg.CMessage_1b?
}

predicate SetOfMessage1bAboutBallot(S:set<CPacket>, b:CBallot)
{
  && SetOfMessage1b(S)
  && (forall p :: p in S ==> p.msg.bal_1b == b)
}

predicate IsAfterLogTruncationPoint(opn:COperationNumber, received_1b_packets:set<CPacket>)
{
  forall p :: p in received_1b_packets && p.msg.CMessage_1b? ==> p.msg.log_truncation_point.n <= opn.n
}

predicate AllAcceptorsHadNoProposal(S:set<CPacket>, opn:COperationNumber)
  requires SetOfMessage1b(S)
{
  forall p :: p in S ==> !(opn in p.msg.votes.v)
}

lemma lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(cps:set<CPacket>)
  requires CPacketsIsAbstractable(cps)
  ensures  SetOfInjectiveTypeCPackets(cps) ==> |cps| == |AbstractifySetOfCPacketsToSetOfRslPackets(cps)|
  ensures  AbstractifySetOfCPacketsToSetOfRslPackets({}) == {}
  ensures  SetOfMessage1b(cps) ==> LSetOfMessage1b(AbstractifySetOfCPacketsToSetOfRslPackets(cps))
  ensures  forall bal :: CBallotIsAbstractable(bal) ==> SetOfMessage1bAboutBallot(cps, bal) ==> LSetOfMessage1bAboutBallot(AbstractifySetOfCPacketsToSetOfRslPackets(cps), AbstractifyCBallotToBallot(bal))
  ensures  forall opn {:trigger LIsAfterLogTruncationPoint(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifySetOfCPacketsToSetOfRslPackets(cps))}{:trigger IsAfterLogTruncationPoint(opn, cps)} :: COperationNumberIsAbstractable(opn) ==> IsAfterLogTruncationPoint(opn, cps) == LIsAfterLogTruncationPoint(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifySetOfCPacketsToSetOfRslPackets(cps))
  ensures  SetOfMessage1b(cps) ==>
  (forall opn {:trigger LAllAcceptorsHadNoProposal(AbstractifySetOfCPacketsToSetOfRslPackets(cps), AbstractifyCOperationNumberToOperationNumber(opn))}{:trigger AllAcceptorsHadNoProposal(cps, opn)} :: COperationNumberIsAbstractable(opn) ==> 
              AllAcceptorsHadNoProposal(cps, opn) == LAllAcceptorsHadNoProposal(AbstractifySetOfCPacketsToSetOfRslPackets(cps), AbstractifyCOperationNumberToOperationNumber(opn)))
{
  lemma_AbstractifySetOfCPacketsToSetOfRslPackets_properties(cps);
  if SetOfInjectiveTypeCPackets(cps) {
    lemma_AbstractifySetOfCPacketsToSetOfRslPackets_cardinality(cps);
  }

  reveal AbstractifySetOfCPacketsToSetOfRslPackets();

  forall opn | COperationNumberIsAbstractable(opn) 
    ensures !IsAfterLogTruncationPoint(opn, cps) ==> !LIsAfterLogTruncationPoint(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifySetOfCPacketsToSetOfRslPackets(cps))
  {
    if !IsAfterLogTruncationPoint(opn, cps) {
      //if |cps| > 0 && (exists p :: p in cps && p.msg.CMessage_1b?)
      var p :| p in cps && p.msg.CMessage_1b? && p.msg.log_truncation_point.n > opn.n;
      var ref_p := AbstractifyCPacketToRslPacket(p);

      assert ref_p in AbstractifySetOfCPacketsToSetOfRslPackets(cps);
      assert ref_p.msg.RslMessage_1b?;
      assert ref_p.msg.log_truncation_point > AbstractifyCOperationNumberToOperationNumber(opn);
    }
  }

  if SetOfMessage1b(cps) {
    var ref_cps := AbstractifySetOfCPacketsToSetOfRslPackets(cps);
    forall opn | COperationNumberIsAbstractable(opn) 
      ensures AllAcceptorsHadNoProposal(cps, opn) ==> LAllAcceptorsHadNoProposal(ref_cps, AbstractifyCOperationNumberToOperationNumber(opn))
    {
      var ref_opn := AbstractifyCOperationNumberToOperationNumber(opn);
      if AllAcceptorsHadNoProposal(cps, opn) {
        forall rp | rp in ref_cps
          ensures !(ref_opn in rp.msg.votes)
        {
          reveal AbstractifyCVotesToVotes();
          var p :| p in cps && rp == AbstractifyCPacketToRslPacket(p);
          if ref_opn in rp.msg.votes {
            assert opn in p.msg.votes.v;
            assert false;
          }
        }

      }
    }

    forall opn | COperationNumberIsAbstractable(opn) 
      ensures !AllAcceptorsHadNoProposal(cps, opn) ==> !LAllAcceptorsHadNoProposal(ref_cps, AbstractifyCOperationNumberToOperationNumber(opn))
    {
      var ref_opn := AbstractifyCOperationNumberToOperationNumber(opn);
      if !AllAcceptorsHadNoProposal(cps, opn) {
        assert !(forall p :: p in cps ==> !(opn in p.msg.votes.v));
        var p :| p in cps && opn in p.msg.votes.v;
        var ref_p := AbstractifyCPacketToRslPacket(p);

        reveal AbstractifyCVotesToVotes();

        assert ref_p in ref_cps;
      }
    }
  }

//  calc ==> {
//    SetOfMessage1b(cps);
//      { reveal AbstractifySetOfCPacketsToSetOfRslPackets(); }
//    LSetOfMessage1b(AbstractifySetOfCPacketsToSetOfRslPackets(cps));
//  }
//  calc ==> {
//    true;
//      { reveal AbstractifySetOfCPacketsToSetOfRslPackets(); }
//    AbstractifySetOfCPacketsToSetOfRslPackets({}) == {};
//  }
}

// Name this accessor for the proof below
function PacketSrc(pkt:CPacket) : EndPoint
{
  pkt.src      
}

lemma lemma_Received1bBound(proposer:ProposerState)
  requires ProposerIsValid(proposer)
  ensures  |proposer.received_1b_packets| < 0xFFFF_FFFF_FFFF_FFFF
{
  var srcs := set pkt | pkt in proposer.received_1b_packets :: PacketSrc(pkt);

  reveal Received1bProperties();
  lemma_MapSetCardinalityOver(proposer.received_1b_packets, srcs, PacketSrc);
  assert |srcs| == |proposer.received_1b_packets|;
  var replicas := UniqueSeqToSet(proposer.constants.all.config.replica_ids);
  lemma_seqs_set_cardinality(proposer.constants.all.config.replica_ids, replicas);
  SubsetCardinality(srcs, replicas);
}

} 
