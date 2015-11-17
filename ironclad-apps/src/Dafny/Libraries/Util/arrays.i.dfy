include "bytes_and_words.s.dfy"

static method ArrayCpy(dst:array<int>, dst_offset:nat, src:array<int>, src_offset:nat, count:nat)
    requires dst != null;
    requires src != null;
    requires dst_offset+count <= dst.Length;
    requires src_offset+count <= src.Length;
    requires src != dst;
    modifies dst;
    ensures dst[..dst_offset] == old(dst)[..dst_offset];
    ensures dst[dst_offset+count..] == old(dst)[dst_offset+count..];
    ensures dst[dst_offset..dst_offset+count] == src[src_offset..src_offset+count];
{
    var i := 0;
    while (i < count)
        invariant 0 <= i <= count;
        invariant dst[..dst_offset] == old(dst)[..dst_offset];
        invariant dst[dst_offset+count..] == old(dst)[dst_offset+count..];
        invariant dst[dst_offset..dst_offset+i] == src[src_offset..src_offset+i];
    {
        ghost var old_src := src[..];
        ghost var old_dst := dst[..];
        ghost var old_i := i;

        assert old_dst[dst_offset..dst_offset+old_i] == old_src[src_offset..src_offset+old_i];
        assert src[..]==old_src;
        dst[dst_offset+i] := src[src_offset+i];
        i := i + 1;
        assert src[..]==old_src;

        assert old_dst[dst_offset..dst_offset+old_i] == old_src[src_offset..src_offset+old_i];

        forall (k | 0<=k<i)
            ensures dst[dst_offset..dst_offset+i][k] == src[src_offset..src_offset+i][k];
        {
            if (k==i-1)
            {
                assert dst[dst_offset..dst_offset+i][k] == src[src_offset..src_offset+i][k];
            }
            else
            {
                assert k<i-1;
                calc {
                    dst[dst_offset..dst_offset+i][k];
                    old_dst[dst_offset..dst_offset+i][k];
                    old_dst[dst_offset..dst_offset+old_i][k];
                    old_src[src_offset..src_offset+old_i][k];
                    src[src_offset..src_offset+old_i][k];
                    src[src_offset..src_offset+i][k];
                }
            }
        }
//-        assert dst[dst_offset..dst_offset+i] == src[src_offset..src_offset+i];
    }
}

static method ArraySet(dst:array<int>, dst_offset:nat, count:nat, value:int)
    requires dst != null;
    requires dst_offset+count <= dst.Length;
    modifies dst;
    ensures forall i :: 0<=i<dst_offset ==> dst[i]==old(dst[..])[i];
    ensures forall i :: dst_offset+count<=i<dst.Length ==> dst[i]==old(dst[..])[i];
    ensures forall i :: dst_offset<=i<dst_offset+count ==> dst[i]==value;
{
    var j := 0;
    while (j < count)
        invariant 0 <= j <= count;
        invariant forall i :: 0<=i<dst_offset ==> dst[i]==old(dst[..])[i];
        invariant forall i :: dst_offset+count<=i<dst.Length ==> dst[i]==old(dst[..])[i];
        invariant forall i :: dst_offset<=i<dst_offset+j ==> dst[i]==value;
    {
        dst[dst_offset+j] := value;
        j := j + 1;
    }
}
