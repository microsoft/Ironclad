include "../../Libraries/Math/power2.i.dfy"
include "DebugPrint.i.dfy"
//-include "../../Libraries/Net/Udp.i.dfy"

method HaltMachine(error_code:int)
    requires 0 <= error_code < 0x10000;
    ensures false;
{
    lemma_2toX();
    debug_print(0, 0x44440000 + error_code);
    while true
        decreases *;
    {
    }
}
