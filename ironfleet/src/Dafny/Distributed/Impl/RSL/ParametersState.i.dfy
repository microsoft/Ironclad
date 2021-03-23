include "../../Common/Native/NativeTypes.s.dfy"
include "../../Protocol/RSL/Parameters.i.dfy"
include "../Common/UpperBound.i.dfy"

module LiveRSL__ParametersState_i {
import opened Native__NativeTypes_s
import opened LiveRSL__Parameters_i
import opened Common__UpperBound_i
import opened Common__UpperBound_s

datatype ParametersState = ParametersState(
  max_log_length:uint64,
  baseline_view_timeout_period:uint64,
  heartbeat_period:uint64,
  max_integer_val:uint64,
  max_batch_size:uint64,
  max_batch_delay:uint64)

function AbstractifyParametersStateToLParameters(params:ParametersState) : LParameters
{
  LParameters(params.max_log_length as int,
              params.baseline_view_timeout_period as int,
              params.heartbeat_period as int,
              UpperBoundFinite(params.max_integer_val as int),
              params.max_batch_size as int,
              params.max_batch_delay as int)
}

function method StaticParams() : ParametersState
{
  ParametersState(7,  // max log length
                  1000, // baseline view timeout period (1000 ms = 1 sec)
                  100,  // heartbeat period (100 ms)
                  0x8000_0000_0000_0000 - 1,  // Max integer value:  2^63 - 1
                  32, // max_batch_size
                  10) // max_batch_delay (10 ms)
}

predicate WFParametersState(params:ParametersState)
{
  && params.max_integer_val > params.max_log_length > 0
  && params.max_integer_val > params.max_batch_delay
  && params.max_integer_val < 0x8000_0000_0000_0000
  && params.baseline_view_timeout_period > 0
  && params.heartbeat_period > 0
  && params.max_batch_size > 0
}

} 
