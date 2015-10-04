include "../../Common/Native/NativeTypes.s.dfy"
include "../../Protocol/Common/UpperBound.s.dfy"

module Common__UpperBound_i {

import opened Native__NativeTypes_s
import opened Common__UpperBound_s

method UpperBoundedAdditionImpl(x:uint64, y:uint64, u:uint64) returns (sum:uint64)
    ensures int(sum) == UpperBoundedAddition(int(x), int(y), UpperBoundFinite(int(u)));
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
