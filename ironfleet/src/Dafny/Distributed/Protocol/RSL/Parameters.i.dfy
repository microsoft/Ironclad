include "../Common/UpperBound.s.dfy"

module LiveRSL__Parameters_i {

import opened Common__UpperBound_s

datatype LParameters = LParameters(
  max_log_length:int,
  baseline_view_timeout_period:int,
  heartbeat_period:int,
  max_integer_val:UpperBound,
  max_batch_size:int,
  max_batch_delay:int
  )

predicate WFLParameters(p:LParameters)
{
  && p.max_log_length > 0
  && p.baseline_view_timeout_period > 0
  && p.heartbeat_period > 0
  && (p.max_integer_val.UpperBoundFinite? ==> p.max_integer_val.n > p.max_log_length)
  && p.max_batch_size > 0
  && p.max_batch_delay >= 0
}

} 
