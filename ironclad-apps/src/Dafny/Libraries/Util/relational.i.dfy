//-<NuBuild BasmEnableSymdiff true />
include "relational.s.dfy"
include "be_sequences.s.dfy"
include "../Math/power2.i.dfy"
include "../../Drivers/CPU/assembly_premium.i.dfy"

method UseDeclassifiedByteSequence(computed:seq<int>, ghost declassed:seq<int>) returns (usable:seq<int>)
    requires |declassed| == |computed|;
    requires IsByteSeq(computed);
    requires public(|computed|);
    requires relation(forall i  :: left(i) == right(i) && 0 <= left(i) < left(|declassed|) ==> declassified(left(declassed[i]), right(declassed[i]), left(computed[i]), right(computed[i])));    
    ensures |usable| == |declassed|;
    ensures forall i  :: 0 <= i < |declassed| ==> declassed[i] == usable[i];
    ensures public(usable);
{   
    var i := 0;
    usable := [];
    while (i < |computed|) 
        invariant 0 <= i <= |computed|;
        invariant |usable| == i;
        invariant forall j  :: 0 <= j < i ==> declassed[j] == usable[j];
        invariant IsByteSeq(computed);
        invariant public(i);
        invariant public(|computed|);
        invariant public(usable);
        invariant relation(forall j  :: left(j) == right(j) && 0 <= left(j) < left(|declassed|) ==> declassified(left(declassed[j]), right(declassed[j]), left(computed[j]), right(computed[j])));    
        invariant |computed| == |declassed|;
    {
        calc {
            computed[i];
            < power2(8);
            < { lemma_power2_strictly_increases(8, 32); }
              power2(32);
        }
        var result := Asm_declassify_result(computed[i], declassed[i]);
        usable := usable + [result];
        i := i + 1;
    }
}
