include "Seqno.i.dfy"

module LivenessProof__LivenessProof_i {

import opened LivenessProof__Seqno_i

predicate SendSingleValid<MT>(s:SingleDeliveryAcct, s':SingleDeliveryAcct, sm:SingleMessage, params:Parameters)
{
       sm.SingleMessage?
    && SendSingleMessage<MT>(s, s', sm.m, sm, params, true)
    && var oldAckState := AckStateLookup(sm.dst, s.sendState); 
       var new_seqno := oldAckState.numPacketsAcked + |oldAckState.unAcked| + 1;
       new_seqno <= params.max_seqno
}

lemma Lemma_PacketSentEventuallyReceivedAndNotDiscarded(
    b:Behavior<LSHT_State>,
    asp:AssumptionParameters,
    src_idx:int,
    send_step:int,
    msg:LSHTMessage
    ) returns
    (dst_idx:int,
     received_step:int)
    requires LivenessAssumptions(b, asp);
    requires 0 <= send_step;
    requires 0 <= src_idx < |b[send_step].hosts| == |asp.c.hostIds|;
    requires 0 <= src_idx < |b[send_step + 1].hosts|;
    requires SendSingleValid(b[send_step].hosts[src_idx].host.sd, b[send_step + 1].hosts[src_idx].host.sd, msg, asp.c.params);
    requires msg.dst in asp.c.hostIds;
    requires b[send_step].environment.nextStep.LEnvStepHostIos?;
    requires b[send_step].environment.nextStep.actor == asp.c.hostIds[src_idx];
    requires LIoOpSend(LPacket(msg.dst, asp.c.hostIds[src_idx], msg)) in b[send_step].environment.nextStep.ios;
    ensures  send_step <= received_step;
    ensures  0 <= dst_idx < |asp.c.hostIds| == |b[received_step].hosts|;
    ensures  msg.dst == asp.c.hostIds[dst_idx];
    ensures  0 <= src_idx < |asp.c.hostIds|;
    ensures  b[received_step].hosts[dst_idx].host.receivedPacket == Some(Packet(msg.dst, asp.c.hostIds[src_idx], msg));
{
    Lemma_ConstantsAllConsistent(b, asp.c, send_step);
    Lemma_ConstantsAllConsistent(b, asp.c, send_step+1);
    dst_idx := GetHostIndex(msg.dst, asp.c);
    var src := asp.c.hostIds[src_idx];
    Lemma_GetHostIndexIsUnique(asp.c, src_idx);
    Lemma_GetHostIndexIsUnique(asp.c, dst_idx);

    Lemma_AssumptionsMakeValidTransition(b, asp.c, send_step);
    var p1 := LPacket(msg.dst, asp.c.hostIds[src_idx], msg);
    assert p1 in b[send_step+1].environment.sentPackets;

    var ap1 := Lemma_ActionThatChangesHostIsThatHostsAction(b, asp.c, send_step, src_idx);

    var reached_step := Lemma_IfTheresAnUnackedPacketThenRecipientSequenceNumberReachesItsSequenceNumber(b, asp, send_step+1, src_idx, dst_idx, msg);
    Lemma_ConstantsAllConsistent(b, asp.c, reached_step);

    Lemma_ReceiverHasCanceledNoUnsentSeqno(b, asp.c, send_step, src_idx, dst_idx);
    var prev_step, ap2 := Lemma_GetReceiveStepForSequenceNumber(b, asp.c, send_step, reached_step, src_idx, dst_idx, msg.seqno);
    Lemma_ConstantsAllConsistent(b, asp.c, prev_step);
    var p2 := ap2.ios[0].r;

    Lemma_PacketStaysInSentPackets(b, asp.c, send_step+1, prev_step, p1);
    Lemma_PacketsHaveSenderUniqueSeqnos(b, asp.c, prev_step, p1, p2);
    received_step := prev_step + 1;
}

}
