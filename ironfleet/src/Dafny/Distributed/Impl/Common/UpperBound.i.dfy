include "../../Common/Native/NativeTypes.s.dfy"
include "../../Protocol/Common/UpperBound.s.dfy"

module Common__UpperBound_i {

import opened Native__NativeTypes_s
import opened Common__UpperBound_s

method UpperBoundedAdditionImpl(x:uint64, y:uint64, u:uint64) returns (sum:uint64)
  ensures sum as int == UpperBoundedAddition(x as int, y as int, UpperBoundFinite(u as int));
{
  if y >= u
  {
    sum := u;
  }
  else if x >= u - y
  {
    sum := u;
  }
  else
  {
    sum := x + y;
  }
}

}
