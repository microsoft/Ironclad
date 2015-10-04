include "NativeTypes.s.dfy"

module Native__NativeTypes_i {
import opened Native__NativeTypes_s

function method Uint64Size() : uint64 { 8 }
function method Uint32Size() : uint64 { 4 }
function method Uint16Size() : uint64 { 2 }

} 
