include "../../Common/Native/NativeTypes.s.dfy"

module Bytes_s {
import opened Native__NativeTypes_s

function Uint64ToBytes(u:uint64) : seq<byte>
{
    [( u/0x1000000_00000000       ) as byte,
     ((u/  0x10000_00000000)%0x100) as byte,
     ((u/    0x100_00000000)%0x100) as byte,
     ((u/      0x1_00000000)%0x100) as byte,
     ((u/         0x1000000)%0x100) as byte,
     ((u/           0x10000)%0x100) as byte,
     ((u/             0x100)%0x100) as byte,
     ( u                    %0x100) as byte]
}

}
