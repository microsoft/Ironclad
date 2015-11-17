//-<NuBuild AddBoogieAxiom Base_axioms />
//-<NuBuild AddBoogieAxiom Word_axioms />
//-<NuBuild AddBoogieAxiom Memory_axioms />
//-<NuBuild AddBoogieAxiom Assembly_axioms />
//-<NuBuild AddBoogieAxiom Io_axioms />
//-private-import Core;
//-private-import LogicalAddressing;
//-private-import Overflow;
//-private-import Util;
//-private-import Stacks;
//-private-import Partition;
//-private-import Instructions;
//-private-import Separation;
//-private-import IntLemmasBase;
//-private-import IntLemmasGc;
//-private-import SimpleGcMemory;
//-private-import SimpleCommon;
//-private-import SimpleCollector;
//-private-import IoMain;
//-private-import IntLemmasMain;
//-private-basmonly-import Trusted;
//-private-basmonly-import Checked;
//-private-import Heap;
//-private-import Seq;
//-private-import dafny_DafnyPrelude;
//-private-import DafnyAssembly;
//-private-import dafny_relational_s;
//-private-import dafny_base_s;
//-private-import dafny_power2_s;
//-private-import dafny_mul_i;
//-private-import dafny_assembly_i;
//-private-import dafny_bit_vector_lemmas_i;
//-private-import dafny_Main_i;
//-<NuBuild AddBoogieFlag /timeLimit:300 />
//-<NuBuild AddBoogieFlag /trace />
//-<NuBuild AddBoogieFlag /z3opt:NL_ARITH=false />

include "../../../Dafny/Libraries/Util/relational.s.dfy"
include "../../../Dafny/Libraries/Math/power2.s.dfy"
include "../../../Dafny/Libraries/Math/mul.i.dfy"
include "../../../Dafny/Drivers/CPU/assembly.i.dfy"
include "../../../Dafny/Libraries/Math/bit_vector_lemmas.i.dfy"

/*
function True(x:int) : bool 
{
    true
}


method rel1(x:int, y:int) returns(z:int)
    requires relation(left(x) == right(x));
    requires relation(True(left(x)) == True(right(x)));   
    requires public(y); //- Equivalent to: relation(left(y) == right(y));
    ensures  relation(left(z) == right(z));
{
    z := x + y;
}

method rel2(x:int, y:int) returns(z:int)
    requires relation(left(x) == right(x));
    ensures  relation(left(z) == right(z));
{
    z := 0;
//-    z := rel1(x, y); //- should fail symdiff checking if uncommented
    z := rel1(x, x);
//-    if (y > 1) //- should fail symdiff checking if uncommented
    if (x > 1)
    {
        z := 1;
    }
}

method rel3(x:int, y:int) returns(z:int, w:int)
    requires relation(left(x) == right(x));
    ensures  relation(left(z) == right(z));
{
    z := 0;
    w := 0;
//-    while (z < y) //- should fail symdiff checking if uncommented
    while (z < x)
        invariant relation(left(x) == right(x));
        invariant relation(left(z) == right(z));
        invariant public(w);
    {
//-        z := z + y; //- should fail symdiff checking if uncommented
        z := z + y + 1 - y;
    }
    z := 5;
}

method rel4(x:int, y:int, s:int) returns(z:int)
    requires public(x);
    requires public(y);
    ensures  public(z);
{
    z := rel1(x, y);
    z := rel1(z, y);
    z := rel1(x, z);
    z := rel1(z, z);
//-    z := rel1(z, s); //- should fail symdiff checking if uncommented
    z := rel1(z, z);
}

method rel5(n:int) returns(s:seq<int>)
    requires public(n);
    ensures  public(s);
{
    var i:int := 0;
    s := [];
    while (i < n)
        invariant public(i);
        invariant public(n);
        invariant public(s);
    {
        s := [i] + s;
    }
}

datatype D = D(d:int);
method rel6(D:D) returns(d:int)
    requires public(D);
    ensures  public(D.d);
    ensures  public(d);
{
    d := D.d;
}

method relQ(x:seq<int>) returns(y:seq<int>)
    requires relation(left(|x|) == right(|x|));
    requires relation(forall i :: 0 <= i < |left(x)| ==> left(x[i]) == right(x[i]));
    ensures  relation(|left(y)| == |right(y)|);
    ensures  relation(forall i :: 0 <= i < right(|y|) ==> left(y)[i] == right(y)[i]);
{
    y := x;
}

/* Example below behaves as expected in SymDiff
   Commented out, since the bodyless gen_secret causes compilation to fail.
   
method gen_secret() returns (s:int)
method rel4(x:int) returns(z:int)
    requires public(x);
    ensures  public(z);
{
    var secret := gen_secret();
    //-z := x + secret;              //- Causes the ensures to fail
    z := x + secret + 1 - secret;
}
*/

method rel5(s:seq<int>) returns (i:int)
    requires |s| == 1;  
    requires public(s);
    ensures  public(i);
{
    i := s[0];      
}

method rel6(s:seq<int>) returns (s_new:seq<int>)
    requires |s| == 10;
    requires public(s);
    ensures  public(s_new);
{
    s_new := s[0..5];
}

method rel7(s:seq<int>, x:int) returns (t:seq<int>)
    requires public(s);
    requires public(x);
    ensures  public(t);
{
    t := s + [x];
}

method clone_array(a:array<int>) returns(b:array<int>)
    ensures  b != a;
    ensures  a.Length == b.Length;
    ensures  (forall i::0 <= i < a.Length ==> b[i] == a[i]);
    ensures  fresh(b);
{
    b := new int[a.Length];
    var k := 0;
    var n := a.Length;
    while (k < n)
        invariant 0 <= k <= a.Length;
        invariant a.Length == b.Length == n;
        invariant (forall i::0 <= i < k ==> b[i] == a[i]);
        invariant fresh(b);
    {
        b[k] := a[k];
        k := k + 1;
    }
}

/*
method test_modifies1(a:array<int>)
    requires a.Length > 0;
    modifies a;
    ensures  a[0] == 10;
{
    a[0] := 10;
}

method test_modifies2(a:array<int>, b:array<int>)
    requires a != null;
    requires a.Length > 0;
    requires b.Length > 0;
    requires b[0] == 20;
    requires a != b;
    modifies a;
    ensures  a[0] == 10;
    ensures  b[0] == 20;
{
    var k:int := 0;
    test_modifies1(a);
    while(k < 10)
        invariant a[0] == 10;
    {
        test_modifies1(a);
        k := k + 1;
    }
    assert a[0] == 10;
    assert b[0] == 20;
}


method test_seq()
{
//-    assert [10,20] + [30] == [10,20,30];
//-    assert [10,20,30][1..] == [20,30];
//-    assert [10,20,30][1] == 20;
//-    assert [10,20,30][..1] == [10];
//-    assert [10,20,30][1:=40] == [10,40,30];
    var x := [10,20] + [30,40];
//-    var n := |x|;
//-    assert n == 4;
//-    x := x[1..3];
//-    assert x == [20,30];
    var n := x[2];
    assert n == 30;
}



method testNat(x:nat) returns(y:nat)
{
    y := 0;
    while (y < 100)
    {
        y := y + 1 + x;
    }
    assert power2(100) > 0;
}

datatype List<A> = Nil() | Cons(hd:A, tl:List<A>);

datatype DT = DT1(x1:int, y1:int) | DT2(x2:int, a2:List<int>, y2:int, b2:DT, z2:int);

function len<A>(l:List<A>):int
    ensures len(l) >= 0;
{
    if l.Cons? then 1 + len(l.tl) else 0
}

ghost method Length<A>(l:List<A>) returns(n:int)
    ensures n == len(l);
{
    if (l.Cons?)
    {
        var m:int := Length(l.tl);
        n := 1 + m;
    }
    else
    {
        n := 0;
    }
}

ghost method TestLength()
{
    var n:int;
    n := Length(Cons(10, Cons(20, Nil())));
    assert unroll(1) && unroll(2);
    assert n == 2;
}

method GetLength<A>(l:List<A>) returns(n:int)
    ensures n == len(l);
{
    n := 0;
    var iter := l;
    while (iter.Cons?)
        decreases len(iter);
        invariant n + len(iter) == len(l);
    {
        iter := iter.tl;
        n := n + 1;
    }
}

method TestGetLength()
{
    var n:int;
    n := GetLength(Cons(10, Cons(20, Nil())));
    assert unroll(1) && unroll(2);
    assert n == 2;
}

function method id<A>(a:A):A { a }

method Foo(i:int, j:int) returns(k:int)
    requires i >= 5 && j >= 6;
    ensures  k == id(i) + j;
{
    TestLength();
    k := i + id(j);
}

method Bar() returns(k:int)
    ensures  k == 15;
{
    k := Foo(7, 8);
}

method A<A>(x:List<A>) returns(y:List<A>)
    ensures  x == y;
{
    var i:int := 0;
    var z:List<A>;
    z := x;
    y := z;
    while (i < 10)
        invariant y == x;
    {
        Skip();
        i := i + 1;
    }
}

method Skip()
{
}

method B<A>(x:List<A>) returns(y:List<A>)
    ensures  x == y;
{
    var i:int := 0;
    var z:List<A>;
    z := x;
    while (i < 10)
        invariant z == x;
    {
        Skip();
        z := A(z);
        Skip();
        i := i + 1;
    }
    y := z;
}

method TestAlloc(x:List<int>) returns(y:List<int>)
    ensures  y.tl.hd == 20;
    ensures  y == Cons(10, Cons(20, Nil()));
    ensures  y.Cons?;
{
    y := B(Cons(10, Cons(20, Nil())));
    var b:bool := y.Nil?;
    assert y.hd == 10;
    assert y.tl.hd == 20;
    var i:int := y.hd;
    var j:int := y.tl.hd;
    assert !b;
    assert i == 10;
    assert j == 20;
    var d:DT := DT2(100, x, 200, DT1(1000, 2000), 300);
    assert d.DT2?;
    b := d.DT2?;
    assert b;
    assert d.b2.y1 == 2000;
    i := d.b2.y1;
    assert i == 2000;
}
*/

*/

//- From Dafny sample files
method Cube(N: int) returns (c: int)
    requires 0 <= N;
    ensures c == N*N*N;
{
    c := 0;
    var n := 0;
    var k := 1;
    var m := 6;
    while (n < N)
        invariant n <= N;
        invariant c == n*n*n;
        invariant k == 3*n*n + 3*n + 1;
        invariant m == 6*n + 6;
    {
        calc
        {
            3 * (n + 1) * (n + 1) + 3 * (n + 1) + 1;
            (3 * n + 3) * (n + 1) + 3 * n + 4;
            { lemma_mul_is_distributive_forall(); }
            (3 * n + 3) * n + (3 * n + 3) * 1 + 3 * n + 4;
            { lemma_mul_is_distributive_forall(); }
            3 * n * n + 3 * n + 3 * n + 3 + 3 * n + 4;
            k + m;
        }
        calc
        {
            (n + 1) * (n + 1) * (n + 1);
            { lemma_mul_is_distributive_forall(); }
            ((n + 1) * n + (n + 1) * 1) * (n + 1);
            { lemma_mul_is_distributive_forall(); }
            ((n * n + 1 * n) + (n * 1 + 1 * 1)) * (n + 1);
            (n * n + 2 * n + 1) * (n + 1);
            { lemma_mul_is_distributive_forall(); }
            (n * n + 2 * n + 1) * n + (n * n + 2 * n + 1) * 1;
            { lemma_mul_is_distributive_forall(); }
            n * n * n + 2 * n * n + 1 * n + n * n + 2 * n + 1;
            n * n * n + ((2 * n * n + 1 * n * n) + (1 * n + 2 * n) + 1);
            { lemma_mul_is_distributive_forall(); }
            n * n * n + ((2 + 1) * n * n + (1 + 2) * n + 1);
            c + k;
        }
        c := c + k;
        k := k + m;
        m := m + 6;
        n := n + 1;
    }
    return;
}

method Main() returns (result:int)
{
    //-lemma_xor_bytes(0, 0);
    result := Cube(5);
}
/*
function method{:axiom}{:imported} word_32(x:int):bool
function method{:axiom}{:imported} and (x:int, y:int):int
function method{:axiom}{:imported} or  (x:int, y:int):int
function method{:axiom}{:imported} xor (x:int, y:int):int

/*
//- mutural summay ensures that M_1[r_1] == M_2[r_2]
//- ghost method Sample (M:map<int,int>) returns (r:int)
//-   requires (forall x:int, y:int :: x in M && y in M ==> M[x] == M[y] ==> x == y);
method{:axiom}{:imported} serialPortOut (x:int)
method{:axiom}{:imported} serialPortIn () returns (r:int)
    ensures (word_32(r));
method{:axiom}{:imported} sample (ghost M:map<int, int>) returns (r:int)

ghost method{:axiom}{:imported} SampleLemma(p:int, M:map<int,int>)
    ensures (forall x:int :: x in M ==> M[x] == xor(x,p));
*/

ghost method{:axiom}{:imported} XorLemmas()
    ensures (forall x:int::xor(x, x) == 0);
    ensures (forall x:int::word_32(x) ==> xor(x, 0) == x);
    ensures (forall x:int, y:int::xor(x, y) == xor(y, x));
    ensures (forall x:int, y:int:: word_32(x) && word_32(y) ==> word_32(xor(x, y)));
    ensures (forall x:int, y:int, z:int:: xor(x, xor(y,z)) == xor(y, xor(x,z)));
    ensures (forall x:int, y:int:: xor(x,xor(y,x)) == y);

method XorIdentity(a:int) returns(r:int)
    requires word_32(a);
    ensures  r == a;
{
    XorLemmas();
    lemma_word32(a);
    r := xor(xor(a, a), a);
    var z := asm_BitwiseXor(a, a);
}

/*
method pad_one_block (p:int) returns (r:int)
    requires word_32(p);
//-  ensures r == One_Time_Pad(p, old(sample_index));
//-  ensures (exists s:int :: sampleCall(old(index), index, s) && r == xor(p,s));
//-  relational verification should verify that true ==> r<1> == r<2>
{
    XorLemmas();
    //- var i:int := 0;
    var k:int;
    ghost var M:map<int,int>;
    SampleLemma(p, M);
    k := sample(M);
    r := xor(k,p);
    assert r == xor(k,p);
    //- return r;
}


method one_time_pad( ) returns ()
    modifies this;
//-    add requirement on maintaining the serial port queue later
//-    requires ps != null;
//-    requires forall i :: 0<= i < index ==> word_32(ps[i]);
//-    ensures  rs != null;
//-    ensures  ps.Length == rs.Length;
//-    ensures  forall i :: 0<= i < index ==> rs[i] == xor (k, ps[i]);
//-    ensures  forall i :: 0<= i < index ==> word_32(rs[i]);
{
    //- read in a value (plain text) from serial port
    var length:int := 10;
    var index:int := 0;
    var p:int := 0;
    var r:int := 0;
    //-while (index < length) {
        p := serialPortIn();
        r := pad_one_block (p);
        //- write the xor(p,k) (encryption) to the serial port
        serialPortOut(r);
        index := index+1;
    //-}
}
*/

/* encryption of multiple blocks. This function ensures that:
     1. each block b is encrypted into xor(b,k), where k is the global key
     2. each encrypted blocks are still words
*/
/*
method Encrypt (ps: array<int>, k:int) returns (rs: array<int>)
    requires ps != null;
    requires forall i :: 0<= i < ps.Length ==> word_32(ps[i]);
    requires word_32(k);
    ensures  rs != null;
    ensures  ps.Length == rs.Length;
    ensures  forall i :: 0<= i < ps.Length ==> rs[i] == xor (k, ps[i]);
    ensures  forall i :: 0<= i < ps.Length ==> word_32(rs[i]);
{
    var index:int := 0;
    rs := new int[ps.Length];

    while (index < ps.Length)
        invariant 0 <= index <= ps.Length;
        invariant forall i :: 0 <= i < index ==> rs[i] == xor(k, ps[i]);
    {
        if (index == ps.Length) {break;}
        rs := encrypt_nat(ps, k, index);
        index := index + 1;
    }
}
*/
*/
