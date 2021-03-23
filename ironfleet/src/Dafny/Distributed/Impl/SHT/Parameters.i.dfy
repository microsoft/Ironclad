include "../../Protocol/SHT/Parameters.i.dfy"
include "../../Common/Native/NativeTypes.s.dfy"

module Impl_Parameters_i {
import opened Protocol_Parameters_i
import opened Native__NativeTypes_s

datatype CParameters = CParameters(max_seqno:uint64, max_delegations:uint64)

function AbstractifyCParametersToParameters(params:CParameters) : Parameters
{
    Parameters(params.max_seqno as int, params.max_delegations as int)
}

predicate CParametersIsValid(params:CParameters)
{
       params.max_seqno == 0xFFFF_FFFF_FFFF_FFFF
    && 3 < params.max_delegations < 0x8000_0000_0000_0000
}

function method StaticParams() : CParameters
{
    CParameters(0xffff_ffff_ffff_ffff,  // max seqno = 2^64-1
                0x7FFF_FFFF_FFFF_FFFF)  // max delegations = 2^63-1
}


}
