include "../Common/NodeIdentity.i.dfy"
include "../Common/GenericRefinement.i.dfy"
include "../../Protocol/SHT/SingleDelivery.i.dfy"
include "CMessage.i.dfy"
include "Parameters.i.dfy"
include "PacketParsing.i.dfy"

module SHT__SingleDeliveryState_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened Common__NodeIdentity_i
import opened SHT__SingleDelivery_i
import opened GenericRefinement_i
import opened SHT__CMessage_i
import opened Impl_Parameters_i
import opened SHT__PacketParsing_i
import opened SHT__Message_i

// Highest sequence number we have received from each node
type CTombstoneTable = map<EndPoint,uint64>

// State about packets we've sent to each node
datatype CAckState = CAckState(numPacketsAcked:uint64, unAcked:seq<CSingleMessage>)
type CSendState = map<EndPoint, CAckState>

datatype CSingleDeliveryAcct = CSingleDeliveryAcct(receiveState:CTombstoneTable, sendState:CSendState)

//////////////////////////////////////////////////////////////////////////////

// Useful to give this cast a name, so it can be used as a higher-order function
function uint64_to_nat_t(u:uint64) : nat_t { u as nat_t }

predicate CTombstoneTableIsAbstractable(ts:CTombstoneTable) 
{
    forall e :: e in ts ==> EndPointIsAbstractable(e)
}

function AbstractifyCTombstoneTableToTombstoneTable(ts:CTombstoneTable) : TombstoneTable
    requires CTombstoneTableIsAbstractable(ts);
{
    lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
    AbstractifyMap(ts, AbstractifyEndPointToNodeIdentity, uint64_to_nat_t, RefineNodeIdentityToEndPoint)
}

//////////////////////////////////////////////////////////////////////////////
// Unacked list

predicate CAckStateIsAbstractable(cas:CAckState) 
{
    CSingleMessageSeqIsAbstractable(cas.unAcked)
}

function AbstractifyCAskStateToAckState(cas:CAckState) : AckState<Message>
    requires CAckStateIsAbstractable(cas);                                          
{
    AckState(cas.numPacketsAcked as int, AbstractifySeqOfCSingleMessageToSeqOfSingleMessage(cas.unAcked))
}


predicate NoAcksInUnAcked(list:seq<CSingleMessage>)
{
    forall i :: 0 <= i < |list| ==> list[i].CSingleMessage?
}

predicate UnAckedListSequential(list:seq<CSingleMessage>)
    requires NoAcksInUnAcked(list);
{
    forall i, j :: 0 <= i && j == i + 1 && j < |list|
        ==> list[i].seqno as int + 1 == list[j].seqno as int
}

predicate CUnAckedValid(msg:CSingleMessage)
{
    msg.CSingleMessage? && CSingleMessageIsAbstractable(msg) && CSingleMessageMarshallable(msg)
}

predicate CUnAckedListValid(list:seq<CSingleMessage>)
{
    (forall i :: 0 <= i < |list| ==> CUnAckedValid(list[i]))
    &&  UnAckedListSequential(list)
}

predicate CUnAckedListValidForDst(list:seq<CSingleMessage>, dst:EndPoint)
{
    CUnAckedListValid(list) 
 && (forall i :: 0 <= i < |list| ==> list[i].dst == dst)
}

predicate CAckStateIsValid(cas:CAckState, dst:EndPoint, params:CParameters)
{
    CAckStateIsAbstractable(cas) && CUnAckedListValidForDst(cas.unAcked, dst)
 && cas.numPacketsAcked as int + |cas.unAcked| <= params.max_seqno as int
 && (|cas.unAcked| > 0 ==> cas.unAcked[0].seqno as int == cas.numPacketsAcked as int + 1)
}

//////////////////////////////////////////////////////////////////////////////

predicate CSendStateIsAbstractable(sendState:CSendState)
{
    MapIsAbstractable(sendState, AbstractifyEndPointToNodeIdentity, AbstractifyCAskStateToAckState, RefineNodeIdentityToEndPoint)
}

function AbstractifyCSendStateToSendState(sendState:CSendState) : SendState<Message>
    requires CSendStateIsAbstractable(sendState);
{
    AbstractifyMap(sendState, AbstractifyEndPointToNodeIdentity, AbstractifyCAskStateToAckState, RefineNodeIdentityToEndPoint)
}

predicate CSendStateIsValid(sendState:CSendState, params:CParameters)
{
    CSendStateIsAbstractable(sendState) 
    && forall e :: e in sendState ==> CAckStateIsValid(sendState[e], e, params)
}

//////////////////////////////////////////////////////////////////////////////

predicate CSingleDeliveryAcctIsAbstractable(acct:CSingleDeliveryAcct) 
{
    CTombstoneTableIsAbstractable(acct.receiveState) && CSendStateIsAbstractable(acct.sendState)
}

function AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(acct:CSingleDeliveryAcct) : SingleDeliveryAcct<Message>
    requires CSingleDeliveryAcctIsAbstractable(acct);
{
    SingleDeliveryAcct(AbstractifyCTombstoneTableToTombstoneTable(acct.receiveState), AbstractifyCSendStateToSendState(acct.sendState))
} 

predicate CSingleDeliveryAccountIsValid(acct:CSingleDeliveryAcct, params:CParameters) 
{
    CSingleDeliveryAcctIsAbstractable(acct) && CSendStateIsValid(acct.sendState, params)
}

}
