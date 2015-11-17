include "../../Drivers/IO/pci.i.dfy"
include "../../Drivers/CPU/assembly.i.dfy"
include "seqs_and_ints.i.dfy"

static method debug_print_seq(marker:int, seqn:seq<int>)
    requires 0<=marker<256;
    requires IsByteSeq(seqn);
{
    var i := 0;
    var shifted_marker := marker * 256 * 256;
    debug_print(0x90, 0x41000000 + shifted_marker);
    while (i < |seqn|)
        invariant 0 <= i <= |seqn|;
    {
        debug_print(0x90, 0x48000000 + shifted_marker + seqn[i]);
        i := i + 1;
    }
    debug_print(0x90, 0x4f000000 + shifted_marker);
}

