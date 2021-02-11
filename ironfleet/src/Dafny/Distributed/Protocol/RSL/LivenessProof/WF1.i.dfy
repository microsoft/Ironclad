include "Invariants.i.dfy"
include "RealTime.i.dfy"
include "../../../Common/Logic/Temporal/WF1.i.dfy"
include "../CommonProof/Actions.i.dfy"

module LivenessProof__WF1_i {
import opened LiveRSL__DistributedSystem_i
import opened LivenessProof__Assumptions_i
import opened LivenessProof__Invariants_i
import opened LivenessProof__RealTime_i
import opened CommonProof__Actions_i
import opened Temporal__Rules_i
import opened Temporal__Temporal_s
import opened Temporal__Time_s
import opened Temporal__Time_i
import opened Temporal__WF1_i
import opened Collections__Maps2_i

lemma lemma_EstablishRequirementsForWF1RealTimeDelayed(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  action:temporal,
  span:int
  )
  requires LivenessAssumptions(b, asp)
  requires asp.synchrony_start <= i
  requires sat(asp.synchrony_start, always(eventuallynextwithin(action, span, PaxosTimeMap(b))))
  ensures  sat(i, always(eventuallynextwithin(action, span, PaxosTimeMap(b))))
  ensures  monotonic_from(0, PaxosTimeMap(b))
  ensures  TimeNotZeno(PaxosTimeMap(b))
{
  lemma_TimeMonotonicFromInvariantHolds(b, asp, 0);
  lemma_AfterForm(b, asp);
  Lemma_AlwaysImpliesLaterAlways(asp.synchrony_start, i, eventuallynextwithin(action, span, PaxosTimeMap(b)));
  reveal eventual();
  reveal after();
}

lemma lemma_EstablishRequirementsForWF1RealTime(
  b:Behavior<RslState>,
  asp:AssumptionParameters,
  i:int,
  action:temporal,
  span:int
  )
  requires LivenessAssumptions(b, asp)
  requires asp.synchrony_start <= i
  requires sat(asp.synchrony_start, always(eventuallynextwithin(action, span, PaxosTimeMap(b))))
  ensures  sat(i, always(eventuallynextwithin(action, span, PaxosTimeMap(b))))
  ensures  monotonic_from(i, PaxosTimeMap(b))
{
  lemma_TimeMonotonicFromInvariantHolds(b, asp, i);
  Lemma_AlwaysImpliesLaterAlways(asp.synchrony_start, i, eventuallynextwithin(action, span, PaxosTimeMap(b)));
}
    

}
