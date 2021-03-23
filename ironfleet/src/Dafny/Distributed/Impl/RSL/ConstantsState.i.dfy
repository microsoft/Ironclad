include "CPaxosConfiguration.i.dfy"

module LiveRSL__ConstantsState_i {
import opened LiveRSL__Constants_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__ParametersState_i

datatype ConstantsState = ConstantsState(
  config:CPaxosConfiguration,
  params:ParametersState
  )

predicate ConstantsStateIsAbstractable(constants:ConstantsState)
{
  CPaxosConfigurationIsAbstractable(constants.config)
}

predicate WFConstantsState(constants:ConstantsState)
{
  && WFCPaxosConfiguration(constants.config)
  && WFParametersState(constants.params)
}

predicate ConstantsStateIsValid(cs:ConstantsState)
{
  && CPaxosConfigurationIsValid(cs.config)
  && ConstantsStateIsAbstractable(cs)
  && WFConstantsState(cs)
  && cs.params.max_integer_val > cs.params.max_log_length > 0
  && cs.params.max_log_length as int < max_votes_len()
  && cs.params.max_integer_val < 0x8000_0000_0000_0000
  && 0 <= cs.params.heartbeat_period < cs.params.max_integer_val
  && 0 < cs.params.max_batch_size as int <= RequestBatchSizeLimit()
}

function AbstractifyConstantsStateToLConstants(constants:ConstantsState) : LConstants
  requires ConstantsStateIsAbstractable(constants)
{
  LConstants(
    AbstractifyCPaxosConfigurationToConfiguration(constants.config),
    AbstractifyParametersStateToLParameters(constants.params))
}

} 
