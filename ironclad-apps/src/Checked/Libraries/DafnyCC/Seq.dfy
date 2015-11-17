include "Base.dfy"
include "../../../Trusted/DafnySpec/Seq.s.dfy"

//- Untrusted sequence definitions

ghost method Seq_Empty_ToZero<A>()
    ensures Seq_Length<A>(Seq_Empty<A>()) == 0;
{
    reveal_Seq_Length(){:typearg "A"};
    Seq_Cons_All<A>();
}

ghost method Seq_Empty_FromZero<A>()
    ensures (forall s:Seq<A> {:trigger Seq_Length<A>(s)}::Seq_Length<A>(s) == 0 ==> s == Seq_Empty<A>());
{
    reveal_Seq_Length(){:typearg "A"};
    assert unroll_all(1);
    Seq_Cons_All<A>();
}

ghost method Seq_Singleton_Length<A>()
    ensures  (forall a:A {:trigger Seq_Length(Seq_Singleton(a))}::Seq_Length(Seq_Singleton(a)) == 1);
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Singleton(){:typearg "A"};
    Seq_Cons_All<A>();
}

ghost method Seq_Index_Negative<A>(s:Seq<A>, k:int)
    ensures  k < 0 ==> Seq_Index(s, k) == Seq_Dummy();
{
    reveal_Seq_Index(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s.Seq_Cons?)
    {
        Seq_Seq(s);
        Seq_Index_Negative(s.tl, k - 1);
    }
}

ghost method Seq_Build_LengthRec<A>(s:Seq<A>, a:A)
    ensures  Seq_Length(Seq_Build(s, a)) == 1 + Seq_Length(s);
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Singleton(){:typearg "A"};
    reveal_Seq_Build(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s.Seq_Cons?)
    {
        Seq_Seq(s);
        Seq_Build_LengthRec(s.tl, a);
    }
}

ghost method Seq_Build_Length<A>()
    ensures  (forall s:Seq<A>, a:A {:trigger Seq_Length(Seq_Build(s, a))}::Seq_Length(Seq_Build(s, a)) == INTERNAL_add_raw(1, Seq_Length(s)));
{
    forall s:Seq<A>, a:A
        ensures Seq_Length(Seq_Build(s, a)) == 1 + Seq_Length(s);
    {
        Seq_Build_LengthRec(s, a);
    }
}

ghost method Seq_Build_IndexRec<A>(s:Seq<A>, k:int, a:A)
    ensures  k == Seq_Length(s) ==> Seq_Index(Seq_Build(s, a), k) == a;
    ensures  k != Seq_Length(s) ==> Seq_Index(Seq_Build(s, a), k) == Seq_Index(s, k);
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Singleton(){:typearg "A"};
    reveal_Seq_Build(){:typearg "A"};
    reveal_Seq_Index(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s.Seq_Cons?)
    {
        Seq_Seq(s);
        Seq_Build_IndexRec(s.tl, k - 1, a);
    }
}

ghost method Seq_Build_Index<A>()
    ensures  forall s:Seq<A>, k:int, a:A {:trigger Seq_Index(Seq_Build(s, a), k)}::
                  (k == Seq_Length(s) ==> Seq_Index(Seq_Build(s, a), k) == a)
               && (k != Seq_Length(s) ==> Seq_Index(Seq_Build(s, a), k) == Seq_Index(s, k));
{
    forall s:Seq<A>, k:int, a:A
        ensures (k == Seq_Length(s) ==> Seq_Index(Seq_Build(s, a), k) == a)
             && (k != Seq_Length(s) ==> Seq_Index(Seq_Build(s, a), k) == Seq_Index(s, k));
    {
        Seq_Build_IndexRec(s, k, a);
    }
}

ghost method Seq_Append_LengthRec<A>(s0:Seq<A>, s1:Seq<A>)
    ensures  Seq_Length(Seq_Append(s0, s1)) == Seq_Length(s0) + Seq_Length(s1);
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Append(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s0.Seq_Cons?)
    {
        Seq_Seq(s0);
        Seq_Append_LengthRec(s0.tl, s1);
    }
}

ghost method Seq_Append_Length<A>()
    ensures  forall s0:Seq<A>, s1:Seq<A> {:trigger Seq_Length(Seq_Append(s0, s1))}::
                            Seq_Length(Seq_Append(s0, s1)) == INTERNAL_add_raw(Seq_Length(s0), Seq_Length(s1));
{
    forall s0:Seq<A>, s1:Seq<A>
        ensures Seq_Length(Seq_Append(s0, s1)) == Seq_Length(s0) + Seq_Length(s1);
    {
        Seq_Append_LengthRec(s0, s1);
    }
}

ghost method Seq_Index_Singleton<A>()
    ensures  forall a:A {:trigger Seq_Index(Seq_Singleton(a), 0)}::Seq_Index(Seq_Singleton(a), 0) == a;
{
    reveal_Seq_Singleton(){:typearg "A"};
    reveal_Seq_Index(){:typearg "A"};
    Seq_Cons_All<A>();
}

ghost method Seq_Append_IndexRec<A>(s0:Seq<A>, s1:Seq<A>, n:int)
    ensures  n < Seq_Length(s0) ==> Seq_Index(Seq_Append(s0, s1), n) == Seq_Index(s0, n);
    ensures  Seq_Length(s0) <= n ==> Seq_Index(Seq_Append(s0, s1), n) == Seq_Index(s1, n - Seq_Length(s0));
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Index(){:typearg "A"};
    reveal_Seq_Append(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s0.Seq_Cons?)
    {
        Seq_Seq(s0);
        Seq_Append_IndexRec(s0.tl, s1, n - 1);
    }
    if (n < 0)
    {
        Seq_Index_Negative(Seq_Append(s0, s1), n);
    }
}

ghost method Seq_Append_Index<A>()
    ensures  forall s0:Seq<A>, s1:Seq<A>, n:int {:trigger Seq_Index(Seq_Append(s0, s1), n)}::
                 (n < Seq_Length(s0) ==> Seq_Index(Seq_Append(s0, s1), n) == Seq_Index(s0, n))
              && (Seq_Length(s0) <= n ==> Seq_Index(Seq_Append(s0, s1), n) == Seq_Index(s1, INTERNAL_sub_raw(n, Seq_Length(s0))));
{
    forall s0:Seq<A>, s1:Seq<A>, n:int
        ensures  (n < Seq_Length(s0) ==> Seq_Index(Seq_Append(s0, s1), n) == Seq_Index(s0, n))
             && (Seq_Length(s0) <= n ==> Seq_Index(Seq_Append(s0, s1), n) == Seq_Index(s1, n - Seq_Length(s0)));
    {
        Seq_Append_IndexRec(s0, s1, n);
    }
}

ghost method Seq_Update_LengthRec<A>(s:Seq<A>, k:int, a:A)
    ensures  0 <= k && k < Seq_Length(s) ==> Seq_Length(Seq_Update(s, k, a)) == Seq_Length(s);
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Update(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s.Seq_Cons?)
    {
        Seq_Seq(s);
        Seq_Update_LengthRec(s.tl, k - 1, a);
    }
}

ghost method Seq_Update_Length<A>()
    ensures  forall s:Seq<A>, k:int, a:A {:trigger Seq_Length(Seq_Update(s, k, a))}::
                            0 <= k && k < Seq_Length(s) ==> Seq_Length(Seq_Update(s, k, a)) == Seq_Length(s);
{
    forall s:Seq<A>, k:int, a:A
        ensures 0 <= k && k < Seq_Length(s) ==> Seq_Length(Seq_Update(s, k, a)) == Seq_Length(s);
    {
        Seq_Update_LengthRec(s, k, a);
    }
}

ghost method Seq_Index_UpdateRec<A>(s:Seq<A>, k:int, a:A, n:int)
    ensures  0 <= n && n < Seq_Length(s) ==>
                 (k == n ==> Seq_Index(Seq_Update(s, k, a), n) == a)
              && (k != n ==> Seq_Index(Seq_Update(s, k, a), n) == Seq_Index(s, n));
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Singleton(){:typearg "A"};
    reveal_Seq_Build(){:typearg "A"};
    reveal_Seq_Index(){:typearg "A"};
    reveal_Seq_Update(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s.Seq_Cons?)
    {
        Seq_Seq(s);
        Seq_Index_UpdateRec(s.tl, k - 1, a, n - 1);
    }
}

ghost method Seq_Index_Update<A>()
    ensures  (forall s:Seq<A>, k:int, a:A, n:int {:trigger Seq_Index(Seq_Update(s, k, a), n)}::
                 0 <= n && n < Seq_Length(s) ==>
                     (k == n ==> Seq_Index(Seq_Update(s, k, a), n) == a)
                  && (k != n ==> Seq_Index(Seq_Update(s, k, a), n) == Seq_Index(s, n)));
{
    forall s:Seq<A>, k:int, a:A, n:int
        ensures  0 <= n && n < Seq_Length(s) ==>
                     (k == n ==> Seq_Index(Seq_Update(s, k, a), n) == a)
                  && (k != n ==> Seq_Index(Seq_Update(s, k, a), n) == Seq_Index(s, n));
    {
        Seq_Index_UpdateRec(s, k, a, n);
    }
}

function{:private} Seq_Equal_Trigger(i:int):bool { true }

ghost method Seq_Equal_EquivRec<A>(s0:Seq<A>, s1:Seq<A>, n:int)
    requires Seq_Length(s0) == Seq_Length(s1);
    requires (forall i:int::Seq_Equal_Trigger(i) && n <= i < n + Seq_Length(s0) ==> Seq_Index(s0, i - n) == Seq_Index(s1, i - n));
    ensures  s0 == s1;
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Index(){:typearg "A"};
    Seq_Empty_FromZero<A>();
    Seq_Cons_All<A>();
    if (s0.Seq_Cons? && s1.Seq_Cons?)
    {
        Seq_Seq(s0);
        Seq_Seq(s1);
        Seq_Equal_EquivRec(s0.tl, s1.tl, n + 1);
        assert Seq_Equal_Trigger(n);
    }
}

ghost method{:loop_lemma} Seq_Equal_Equiv<A>()
    ensures  (forall s0:Seq<A>, s1:Seq<A> {:trigger Seq_Equal(s0, s1)}::Seq_Equal(s0, s1) ==> s0 == s1);
    ensures  (forall s0:Seq<A>, s1:Seq<A> {:trigger Seq_Equal(s0, s1)}::
                 Seq_Equal(s0, s1) <==>
                     Seq_Length(s0) == Seq_Length(s1)
                  && (forall i:int {:trigger Seq_Index(s0, i)}{:trigger Seq_Index(s1, i)}::
                         0 <= i && i < Seq_Length(s0) ==> Seq_Index(s0, i) == Seq_Index(s1, i)));
{
    forall s0:Seq<A>, s1:Seq<A>
        ensures  Seq_Equal(s0, s1) <==>
                     Seq_Length(s0) == Seq_Length(s1)
                  && (forall i:int::0 <= i && i < Seq_Length(s0) ==> Seq_Index(s0, i) == Seq_Index(s1, i));
    {
        if ( Seq_Length(s0) == Seq_Length(s1)
            && (forall i:int::0 <= i && i < Seq_Length(s0) ==> Seq_Index(s0, i) == Seq_Index(s1, i)))
        {
            Seq_Equal_EquivRec(s0, s1, 0);
        }
    }
}

ghost method Seq_Take_LengthRec<A>(s:Seq<A>, n:int)
    ensures  0 <= n ==>
                 (n <= Seq_Length(s) ==> Seq_Length(Seq_Take(s, n)) == n)
              && (Seq_Length(s) < n ==> Seq_Length(Seq_Take(s, n)) == Seq_Length(s));
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Take(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s.Seq_Cons?)
    {
        Seq_Seq(s);
        Seq_Take_LengthRec(s.tl, n - 1);
    }
}

ghost method Seq_Take_Length<A>()
    ensures  forall s:Seq<A>, n:int {:trigger Seq_Length(Seq_Take(s, n))}::0 <= n ==>
                 (n <= Seq_Length(s) ==> Seq_Length(Seq_Take(s, n)) == n)
              && (Seq_Length(s) < n ==> Seq_Length(Seq_Take(s, n)) == Seq_Length(s));
{
    forall s:Seq<A>, n:int
        ensures  0 <= n ==>
                     (n <= Seq_Length(s) ==> Seq_Length(Seq_Take(s, n)) == n)
                  && (Seq_Length(s) < n ==> Seq_Length(Seq_Take(s, n)) == Seq_Length(s));
    {
        Seq_Take_LengthRec(s, n);
    }
}

ghost method Seq_Take_IndexRec<A>(s:Seq<A>, n:int, i:int)
    ensures  0 <= i < n && i < Seq_Length(s) ==> Seq_Index(Seq_Take(s, n), i) == Seq_Index(s, i);
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Index(){:typearg "A"};
    reveal_Seq_Take(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s.Seq_Cons?)
    {
        Seq_Seq(s);
        Seq_Take_IndexRec(s.tl, n - 1, i - 1);
    }
}

ghost method Seq_Take_Index<A>()
    ensures  forall s:Seq<A>, n:int, i:int {:trigger Seq_Index(Seq_Take(s, n), i)}::
                 0 <= i < n && i < Seq_Length(s) ==> Seq_Index(Seq_Take(s, n), i) == Seq_Index(s, i);
{
    forall s:Seq<A>, n:int, i:int
        ensures 0 <= i < n && i < Seq_Length(s) ==> Seq_Index(Seq_Take(s, n), i) == Seq_Index(s, i);
    {
        Seq_Take_IndexRec(s, n, i);
    }
}

ghost method Seq_Drop_LengthRec<A>(s:Seq<A>, n:int)
    ensures  0 <= n ==>
                 (n <= Seq_Length(s) ==> Seq_Length(Seq_Drop(s, n)) == Seq_Length(s) - n)
              && (Seq_Length(s) < n ==> Seq_Length(Seq_Drop(s, n)) == 0);
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Drop(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s.Seq_Cons?)
    {
        Seq_Seq(s);
        Seq_Drop_LengthRec(s.tl, n - 1);
    }
}

ghost method Seq_Drop_Length<A>()
    ensures  (forall s:Seq<A>, n:int {:trigger Seq_Length(Seq_Drop(s, n))}::0 <= n ==>
                 (n <= Seq_Length(s) ==> Seq_Length(Seq_Drop(s, n)) == INTERNAL_sub_raw(Seq_Length(s), n))
              && (Seq_Length(s) < n ==> Seq_Length(Seq_Drop(s, n)) == 0));
{
    forall s:Seq<A>, n:int
        ensures  0 <= n ==>
                     (n <= Seq_Length(s) ==> Seq_Length(Seq_Drop(s, n)) == Seq_Length(s) - n)
                  && (Seq_Length(s) < n ==> Seq_Length(Seq_Drop(s, n)) == 0);
    {
        Seq_Drop_LengthRec(s, n);
    }
}

ghost method Seq_Drop_IndexRec<A>(s:Seq<A>, n:int, i:int)
    ensures  0 <= n && 0 <= i ==> Seq_Index(Seq_Drop(s, n), i) == Seq_Index(s, i + n);
{
    reveal_Seq_Index(){:typearg "A"};
    reveal_Seq_Drop(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s.Seq_Cons?)
    {
        Seq_Seq(s);
        Seq_Drop_IndexRec(s.tl, n - 1, i);
    }
}

ghost method Seq_Drop_Index<A>()
    ensures  forall s:Seq<A>, n:int, i:int {:trigger Seq_Index(Seq_Drop(s, n), i)}::
                 0 <= n && 0 <= i && i < Seq_Length(s) - n ==> Seq_Index(Seq_Drop(s, n), i) == Seq_Index(s, INTERNAL_add_raw(i, n));
{
    forall s:Seq<A>, n:int, i:int
        ensures 0 <= n && 0 <= i && i < Seq_Length(s) - n ==> Seq_Index(Seq_Drop(s, n), i) == Seq_Index(s, i + n);
    {
        Seq_Drop_IndexRec(s, n, i);
    }
}

function{:private} Seq_FromArrayRange(a:INTERNAL_ArrayElems, j:int, k:int):Seq<int>
    decreases k - j;
{
    if j < k then Seq_Cons(INTERNAL_array_elems_index(a, j), Seq_FromArrayRange(a, j + 1, k)) else Seq_Nil()
}

function{:private}{:opaque} Seq_FromArrayElems(a:INTERNAL_ArrayElems, len:int):Seq<int>
{
    Seq_FromArrayRange(a, 0, len)
}

//- declared public so that old(a[..]) == a[..] is more evident across calls that don't modify a
function Seq_FromArray(a:array<int>):Seq<int>
{
    Seq_FromArrayElems(INTERNAL_array_elems(a), a.Length)
}

function{:private} Seq_FromArrayRange_INTERNAL_HEAP(heap:INTERNAL_AbsMem, a:array<int>, j:int, k:int):Seq<int>
function{:private} Seq_FromArray_INTERNAL_HEAP(heap:INTERNAL_AbsMem, a:array<int>):Seq<int>

ghost method Seq_FromArray_LengthRec(a:INTERNAL_ArrayElems, j:int, k:int)
    ensures  Seq_Length(Seq_FromArrayRange(a, j, k)) == if j <= k then k - j else 0;
    decreases k - j;
{
    reveal_Seq_Length(){:typearg "int"};
    Seq_Cons_All<int>();
    if (j < k)
    {
        Seq_FromArray_LengthRec(a, j + 1, k);
    }
}


ghost method Seq_FromArray_Length()
    ensures  forall INTERNAL_absMem:INTERNAL_AbsMem, a:array<int> {:trigger Seq_Length(Seq_FromArray(a))}::
                 a.Length >= 0 ==> Seq_Length(Seq_FromArray(a)) == a.Length;
    ensures  forall INTERNAL_absMem:INTERNAL_AbsMem, a:array<int> {:trigger Seq_Length(Seq_FromArray(a))}::
                 Seq_Length(Seq_FromArray(a)) > 0 ==> Seq_Length(Seq_FromArray(a)) == a.Length;
{
    reveal_Seq_FromArrayElems();
    forall INTERNAL_absMem:INTERNAL_AbsMem, a:array<int>
        ensures  a.Length >= 0 ==> Seq_Length(Seq_FromArray(a)) == a.Length;
        ensures  Seq_Length(Seq_FromArray(a)) > 0 ==> Seq_Length(Seq_FromArray(a)) == a.Length;
    {
        Seq_FromArray_LengthRec(INTERNAL_array_elems(a), 0, a.Length);
    }
}

ghost method Seq_FromArray_IndexRec(a:INTERNAL_ArrayElems, i:int, j:int, k:int)
    ensures  0 <= j <= i < k ==> Seq_Index(Seq_FromArrayRange(a, j, k), i - j)
                              == INTERNAL_array_elems_index(a, i);
    decreases i - j;
{
    reveal_Seq_Length(){:typearg "int"};
    reveal_Seq_Index(){:typearg "int"};
    Seq_Cons_All<int>();
    if (j < i)
    {
        Seq_FromArray_IndexRec(a, i, j + 1, k);
    }
}

ghost method Seq_FromArray_Index()
    ensures  forall INTERNAL_absMem:INTERNAL_AbsMem, a:array<int>, i:int
                            {:trigger Seq_Index(Seq_FromArray(a), i)}
                            {:trigger Seq_FromArray(a), a[i]}::
                            0 <= i < Seq_Length(Seq_FromArray(a)) ==> Seq_Index(Seq_FromArray(a), i) == a[i];
{
    reveal_Seq_FromArrayElems();
    forall INTERNAL_absMem:INTERNAL_AbsMem, a:array<int>, i:int
        ensures  0 <= i < Seq_Length(Seq_FromArray(a)) ==> Seq_Index(Seq_FromArray(a), i) == a[i];
    {
        if (0 <= i < Seq_Length(Seq_FromArray(a)))
        {
            Seq_FromArray_LengthRec(INTERNAL_array_elems(a), 0, a.Length);
            Seq_FromArray_IndexRec(INTERNAL_array_elems(a), i, 0, a.Length);
        }
    }
}

ghost method Seq_FromArray_UpdateRec(a:INTERNAL_ArrayElems, i:int, v:int, j:int, k:int)
    ensures  0 <= j <= i < k ==>
                 Seq_FromArrayRange(INTERNAL_array_elems_update(a, i, v), j, k)
              == Seq_Update(Seq_FromArrayRange(a, j, k), i - j, v);
    ensures  i < j <= k ==>
                 Seq_FromArrayRange(INTERNAL_array_elems_update(a, i, v), j, k)
              == Seq_FromArrayRange(a, j, k);
    decreases k - j;
{
    reveal_Seq_Update(){:typearg "int"};
    if (j < k)
    {
        Seq_FromArray_UpdateRec(a, i, v, j + 1, k);
        Seq_Cons_All<int>();
    }
}

ghost method Seq_FromArray_Update()
    ensures  forall INTERNAL_absMem:INTERNAL_AbsMem, a:array<int>, i:int, v:int
                 {:trigger Seq_FromArray_INTERNAL_HEAP(INTERNAL_array_update(a, i, v), a)}::
                 0 <= i < a.Length ==>
                     Seq_FromArray_INTERNAL_HEAP(INTERNAL_array_update(a, i, v), a)
                  == Seq_Update(Seq_FromArray(a), i, v);
{
    reveal_Seq_FromArrayElems();
    forall INTERNAL_absMem:INTERNAL_AbsMem, a:array<int>, i:int, v:int
        ensures  0 <= i < a.Length ==>
                     Seq_FromArray_INTERNAL_HEAP(INTERNAL_array_update(a, i, v), a)
                  == Seq_Update(Seq_FromArray(a), i, v);
    {
        if (0 <= i < a.Length)
        {
            Seq_FromArray_UpdateRec(INTERNAL_array_elems(a), i, v, 0, a.Length);
        }
    }
}

/*
axiom (forall<alpha> h: HeapType, o: ref, f: Field alpha, v: alpha, a: ref ::
    { Seq#FromArray(update(h, o, f, v), a) }
        o != a ==> Seq#FromArray(update(h, o, f, v), a) == Seq#FromArray(h, a) );
*/


ghost method Seq_Append_TakeDropRec<A>(s0:Seq<A>, s1:Seq<A>)
    ensures  Seq_Take(Seq_Append(s0, s1), Seq_Length(s0)) == s0;
    ensures  Seq_Drop(Seq_Append(s0, s1), Seq_Length(s0)) == s1;
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Append(){:typearg "A"};
    reveal_Seq_Take(){:typearg "A"};
    reveal_Seq_Drop(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s0.Seq_Cons?)
    {
        Seq_Seq(s0);
        Seq_Append_TakeDropRec(s0.tl, s1);
    }
}

ghost method Seq_Append_TakeDrop<A>()
    ensures  forall s0:Seq<A>, s1:Seq<A>
            {:trigger Seq_Append(s0, s1)}:: //- default Dafny trigger
//



                 Seq_Take(Seq_Append(s0, s1), Seq_Length(s0)) == s0
              && Seq_Drop(Seq_Append(s0, s1), Seq_Length(s0)) == s1;
{
    forall s0:Seq<A>, s1:Seq<A>
        ensures Seq_Take(Seq_Append(s0, s1), Seq_Length(s0)) == s0
                 && Seq_Drop(Seq_Append(s0, s1), Seq_Length(s0)) == s1;
    {
        Seq_Append_TakeDropRec(s0, s1);
    }
}

ghost method Seq_Append_TakeDrop_Restricted<A>()
    ensures  forall s0:Seq<A>, s1:Seq<A>

//- [ckh] The default Dafny trigger is very liberal here, but I've seen some slow performance and timeouts, so I made it more restrictive
             {:trigger Seq_Take(Seq_Append(s0, s1), Seq_Length(s0))}
             {:trigger Seq_Drop(Seq_Append(s0, s1), Seq_Length(s0))}
             ::
                 Seq_Take(Seq_Append(s0, s1), Seq_Length(s0)) == s0
              && Seq_Drop(Seq_Append(s0, s1), Seq_Length(s0)) == s1;
{
    forall s0:Seq<A>, s1:Seq<A>
        ensures Seq_Take(Seq_Append(s0, s1), Seq_Length(s0)) == s0
                 && Seq_Drop(Seq_Append(s0, s1), Seq_Length(s0)) == s1;
    {
        Seq_Append_TakeDropRec(s0, s1);
    }
}

ghost method Seq_Update_CommuteTake1Rec<A>(s:Seq<A>, i:int, a:A, n:int)
    ensures  0 <= i && i < n && n <= Seq_Length(s) ==> Seq_Take(Seq_Update(s, i, a), n) == Seq_Update(Seq_Take(s, n), i, a);
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Update(){:typearg "A"};
    reveal_Seq_Take(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s.Seq_Cons?)
    {
        Seq_Seq(s);
        Seq_Update_CommuteTake1Rec(s.tl, i - 1, a, n - 1);
    }
}

ghost method Seq_Update_CommuteTake1<A>()
    ensures  forall s:Seq<A>, i:int, a:A, n:int {:trigger Seq_Take(Seq_Update(s, i, a), n)}::
                 0 <= i && i < n && n <= Seq_Length(s) ==> Seq_Take(Seq_Update(s, i, a), n) == Seq_Update(Seq_Take(s, n), i, a);
{
    forall s:Seq<A>, i:int, a:A, n:int
        ensures 0 <= i && i < n && n <= Seq_Length(s) ==> Seq_Take(Seq_Update(s, i, a), n) == Seq_Update(Seq_Take(s, n), i, a);
    {
        Seq_Update_CommuteTake1Rec(s, i, a, n);
    }
}

ghost method Seq_Update_CommuteTake2Rec<A>(s:Seq<A>, i:int, a:A, n:int)
    ensures  n <= i && i < Seq_Length(s) ==> Seq_Take(Seq_Update(s, i, a), n) == Seq_Take(s, n);
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Update(){:typearg "A"};
    reveal_Seq_Take(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s.Seq_Cons?)
    {
        Seq_Seq(s);
        Seq_Update_CommuteTake2Rec(s.tl, i - 1, a, n - 1);
    }
}

ghost method Seq_Update_CommuteTake2<A>()
    ensures  forall s:Seq<A>, i:int, a:A, n:int {:trigger Seq_Take(Seq_Update(s, i, a), n)}::
                            n <= i && i < Seq_Length(s) ==> Seq_Take(Seq_Update(s, i, a), n) == Seq_Take(s, n);
{
    forall s:Seq<A>, i:int, a:A, n:int
        ensures n <= i && i < Seq_Length(s) ==> Seq_Take(Seq_Update(s, i, a), n) == Seq_Take(s, n);
    {
        Seq_Update_CommuteTake2Rec(s, i, a, n);
    }
}

ghost method Seq_Update_CommuteDrop1Rec<A>(s:Seq<A>, i:int, a:A, n:int)
    ensures  0 <= n && n < i && i <= Seq_Length(s) ==> Seq_Drop(Seq_Update(s, i, a), n) == Seq_Update(Seq_Drop(s, n), i - n, a);
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Update(){:typearg "A"};
    reveal_Seq_Drop(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s.Seq_Cons?)
    {
        Seq_Seq(s);
        Seq_Update_CommuteDrop1Rec(s.tl, i - 1, a, n - 1);
    }
}

ghost method Seq_Update_CommuteDrop1<A>()
    ensures  forall s:Seq<A>, i:int, a:A, n:int {:trigger Seq_Drop(Seq_Update(s, i, a), n)}::
                 0 <= n && n < i && i <= Seq_Length(s) ==> Seq_Drop(Seq_Update(s, i, a), n) == Seq_Update(Seq_Drop(s, n), i - n, a);
{
    forall s:Seq<A>, i:int, a:A, n:int
        ensures 0 <= n && n < i && i <= Seq_Length(s) ==> Seq_Drop(Seq_Update(s, i, a), n) == Seq_Update(Seq_Drop(s, n), i - n, a);
    {
        Seq_Update_CommuteDrop1Rec(s, i, a, n);
    }
}

ghost method Seq_Update_CommuteDrop2Rec<A>(s:Seq<A>, i:int, a:A, n:int)
    ensures  0 <= i && i < n && n < Seq_Length(s) ==> Seq_Drop(Seq_Update(s, i, a), n) == Seq_Drop(s, n);
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Update(){:typearg "A"};
    reveal_Seq_Drop(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s.Seq_Cons?)
    {
        Seq_Seq(s);
        Seq_Update_CommuteDrop2Rec(s.tl, i - 1, a, n - 1);
    }
}

ghost method Seq_Update_CommuteDrop2<A>()
    ensures  forall s:Seq<A>, i:int, a:A, n:int {:trigger Seq_Drop(Seq_Update(s, i, a), n)}::
                 0 <= i && i < n && n < Seq_Length(s) ==> Seq_Drop(Seq_Update(s, i, a), n) == Seq_Drop(s, n);
{
    forall s:Seq<A>, i:int, a:A, n:int
        ensures 0 <= i && i < n && n < Seq_Length(s) ==> Seq_Drop(Seq_Update(s, i, a), n) == Seq_Drop(s, n);
    {
        Seq_Update_CommuteDrop2Rec(s, i, a, n);
    }
}

ghost method Seq_Build_CommuteDropRec<A>(s:Seq<A>, a:A, n:int)
    ensures  0 <= n && n <= Seq_Length(s) ==> Seq_Drop(Seq_Build(s, a), n) == Seq_Build(Seq_Drop(s, n), a);
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Singleton(){:typearg "A"};
    reveal_Seq_Build(){:typearg "A"};
    reveal_Seq_Drop(){:typearg "A"};
    Seq_Cons_All<A>();
    if (s.Seq_Cons?)
    {
        Seq_Seq(s);
        Seq_Build_CommuteDropRec(s.tl, a, n - 1);
    }
}

ghost method Seq_Build_CommuteDrop<A>()
    ensures  forall s:Seq<A>, a:A, n:int {:trigger Seq_Drop(Seq_Build(s, a), n)}::
                 0 <= n && n <= Seq_Length(s) ==> Seq_Drop(Seq_Build(s, a), n) == Seq_Build(Seq_Drop(s, n), a);
{
    forall s:Seq<A>, a:A, n:int
        ensures 0 <= n && n <= Seq_Length(s) ==> Seq_Drop(Seq_Build(s, a), n) == Seq_Build(Seq_Drop(s, n), a);
    {
        Seq_Build_CommuteDropRec(s, a, n);
    }
}

ghost method Seq_Take_Empty<A>()
    ensures Seq_Take<A>(Seq_Empty<A>(), 0) == Seq_Empty<A>();
{
    reveal_Seq_Take(){:typearg "A"};
}

ghost method Seq_Drop_Empty<A>()
    ensures Seq_Drop<A>(Seq_Empty<A>(), 0) == Seq_Empty<A>();
{
    reveal_Seq_Drop(){:typearg "A"};
}

ghost method lemma_Seq_Case<A>(s:Seq<A>)
    ensures s.Seq_Cons? <==> Seq_Length<A>(s) > 0;
    ensures s.Seq_Cons? <==> !s.Seq_Nil?;
{
    reveal_Seq_Length(){:typearg "A"};
    Seq_Seq(s);
}

ghost method lemma_Seq_Cons<A>(a:A, s:Seq<A>)
    ensures  Seq_Equal(Seq_Cons(a, s), Seq_Append(Seq_Build(Seq_Empty(), a), s));
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Build(){:typearg "A"};
    reveal_Seq_Singleton(){:typearg "A"};
    reveal_Seq_Append(){:typearg "A"};
    Seq_Cons_All<A>();
    Seq_Seq<A>(Seq_Nil());
    Seq_Seq(s);
}

ghost method lemma_Seq_Head<A>(s:Seq<A>)
    ensures  Seq_Length(s) > 0 ==> s.hd == Seq_Index(s, 0);
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Index(){:typearg "A"};
}

ghost method lemma_Seq_Tail<A>(s:Seq<A>)
    ensures  Seq_Length(s) > 0 ==> Seq_Equal(s.tl, Seq_Drop(s, 1));
{
    reveal_Seq_Length(){:typearg "A"};
    reveal_Seq_Drop(){:typearg "A"};
    lemma_Seq_Case(s);
    Seq_Seq(s);
}

method seq_Length<A>(s:Seq<A>) returns(n:int)
    ensures  n == Seq_Length(s);
{
    reveal_Seq_Length(){:typearg "A"};
    Seq_Cons_All<A>();
    n := 0;
    var iter := s;
    while (iter.Seq_Cons?)
        decreases Seq_Length(iter);
        invariant n + Seq_Length(iter) == Seq_Length(s);
    {
        Seq_Seq(iter);
        iter := iter.tl;
        n := n + 1;
    }
}

method seq_Empty<A>() returns(s:Seq<A>)
    ensures s == Seq_Empty<A>();
{
    Seq_Cons_All<A>();
    s := Seq_Nil();
}

method seq_Build<A>(s:Seq<A>, a:A) returns(r:Seq<A>)
    ensures  Seq_Equal(r, Seq_Build(s, a));
{
    lemma_Seq_Cons(a, Seq_Nil());
    r := seq_Append(s, Seq_Cons(a, Seq_Nil()));
}

method seq_Index<A>(s:Seq<A>, k:int) returns(a:A)
    requires 0 <= k < Seq_Length(s);
    ensures  a == Seq_Index(s, k);
{
    Seq_Cons_All<A>();
    var iter := s;
    var j := k;
    while (j != 0)
        decreases j;
        invariant 0 <= j < Seq_Length(iter);
        invariant Seq_Index(iter, j) == Seq_Index(s, k);
    {
        j := j - 1;
        lemma_Seq_Tail(iter);
        iter := iter.tl;
    }
    lemma_Seq_Head(iter);
    a := iter.hd;
}

method seq_Append0<A>(s0:Seq<A>) returns(rev0:Seq<A>)
    ensures Seq_Length(rev0) == Seq_Length(s0);
    ensures forall i {:trigger Seq_Index(rev0, i)}::0 <= i < Seq_Length(rev0) ==> Seq_Index(rev0, i) == Seq_Index(s0, Seq_Length(rev0) - i - 1);
{
    rev0 := Seq_Nil();
    var iter := s0;
    reveal_Seq_Drop(){:typearg "A"};
    while (iter.Seq_Cons?)
        decreases Seq_Length(iter);
        invariant Seq_Length(rev0) + Seq_Length(iter) == Seq_Length(s0);
        invariant forall i::0 <= i < Seq_Length(rev0) ==> Seq_Index(rev0, i) == Seq_Index(s0, Seq_Length(rev0) - i - 1);
        invariant Seq_Equal(iter, Seq_Drop(s0, Seq_Length(s0) - Seq_Length(iter)));
    {
        lemma_Seq_Case(iter);
        lemma_Seq_Head(iter);
        lemma_Seq_Tail(iter);
        lemma_Seq_Cons(iter.hd, rev0);
        rev0 := Seq_Cons(iter.hd, rev0);
        iter := iter.tl;
    }
    lemma_Seq_Case(iter);
}

ghost method lemma_Seq_Length<A>(s:Seq<A>)
    ensures  Seq_Length(s) >= 0;
{
}

method{:dafnycc_no_lemmas} seq_Append<A>(s0:Seq<A>, s1:Seq<A>) returns(s:Seq<A>)
    ensures  Seq_Equal(s, Seq_Append(s0, s1));
{
    assert unroll(0);
    assert unroll(1);
    lemma_Seq_Length(s0);
    lemma_Seq_Length(s1);

    var rev0 := seq_Append0(s0);
    s := s1;
    var iter := rev0;
    calc
    {
        Seq_Equal(s, Seq_Append(Seq_Drop(s0, Seq_Length(iter)), s1));
        { Seq_Drop_LengthRec(s0, Seq_Length(iter)); }
        { Seq_Empty_FromZero<A>(); }
        Seq_Equal(s, Seq_Append(Seq_Empty(), s1));
        Seq_Equal(s, Seq_Append(Seq_Nil(), s1));
        { Seq_Seq<A>(Seq_Nil()); }
        { reveal_Seq_Append(){:typearg "A"}; }
        Seq_Equal(s, s1);
        { Seq_Equal_Equiv<A>(); }
        true;
    }
    while (iter.Seq_Cons?)
        decreases Seq_Length(iter);
        invariant Seq_Length(s) + Seq_Length(iter) == Seq_Length(s0) + Seq_Length(s1);
        invariant forall i::0 <= i < Seq_Length(iter) ==> Seq_Index(iter, i) == Seq_Index(s0, Seq_Length(iter) - i - 1);
        invariant Seq_Equal(s, Seq_Append(Seq_Drop(s0, Seq_Length(iter)), s1));
    {
        lemma_Seq_Case(iter);
        lemma_Seq_Head(iter);
        lemma_Seq_Tail(iter);
        lemma_Seq_Cons(iter.hd, s);
        s := Seq_Cons(iter.hd, s);
        iter := iter.tl;
        Seq_Empty_ToZero<A>();
        Seq_Empty_FromZero<A>();
        Seq_Build_Length<A>();
        Seq_Build_Index<A>();
        Seq_Append_Length<A>();
        Seq_Append_Index<A>();
        Seq_Equal_Equiv<A>();
        Seq_Drop_Length<A>();
        Seq_Drop_Index<A>();
    }
    calc
    {
        Seq_Equal(s, Seq_Append(Seq_Drop(s0, Seq_Length(iter)), s1));
        { lemma_Seq_Length(iter); }
        { lemma_Seq_Case(iter); }
        Seq_Equal(s, Seq_Append(Seq_Drop(s0, 0), s1));
        { Seq_Drop_LengthRec(s0, 0); }
        { Seq_Drop_Index<A>(); }
        { Seq_Equal_EquivRec(s0, Seq_Drop(s0, 0), 0); }
        Seq_Equal(s, Seq_Append(s0, s1));
    }
}

method seq_Update<A>(s:Seq<A>, k:int, a:A) returns(r:Seq<A>)
    requires 0 <= k < Seq_Length(s);
    ensures  Seq_Equal(r, Seq_Update(s, k, a));
{
    Seq_Cons_All<A>();
    var iter := s;
    var j := k;
    var rev0 := Seq_Nil();
    while (j != 0)
        decreases j;
        invariant 0 <= j;
        invariant k == j + Seq_Length(rev0);
        invariant Seq_Length(rev0) + Seq_Length(iter) == Seq_Length(s);
        invariant forall i {:trigger Seq_Index(rev0, i)}::0 <= i < Seq_Length(rev0) ==> Seq_Index(rev0, i) == Seq_Index(s, Seq_Length(rev0) - i - 1);
        invariant Seq_Equal(iter, Seq_Drop(s, Seq_Length(s) - Seq_Length(iter)));
    {
        lemma_Seq_Head(iter);
        lemma_Seq_Tail(iter);
        lemma_Seq_Cons(iter.hd, rev0);
        j := j - 1;
        rev0 := Seq_Cons(iter.hd, rev0);
        iter := iter.tl;
    }
    lemma_Seq_Tail(iter);
    r := iter.tl;
    lemma_Seq_Cons(a, r);
    r := Seq_Cons(a, r);
    iter := rev0;
    while (iter.Seq_Cons?)
        decreases Seq_Length(iter);
        invariant Seq_Length(r) + Seq_Length(iter) == Seq_Length(s);
        invariant forall i {:trigger Seq_Index(iter, i)}::0 <= i < Seq_Length(iter) ==> Seq_Index(iter, i) == Seq_Index(s, Seq_Length(iter) - i - 1);
        
        invariant Seq_Equal(r,
            Seq_Append(Seq_Drop(Seq_Take(s, k), Seq_Length(iter)),
                Seq_Append(Seq_Build(Seq_Empty(), a),
                    Seq_Drop(s, k + 1))));
    {
        Seq_Seq(iter);
        lemma_Seq_Case(iter);
        lemma_Seq_Head(iter);
        lemma_Seq_Tail(iter);
        lemma_Seq_Cons(iter.hd, r);
        r := Seq_Cons(iter.hd, r);
        iter := iter.tl;
    }
    lemma_Seq_Case(iter);
}

method seq_Take<A>(s:Seq<A>, k:int) returns(r:Seq<A>)
    requires 0 <= k <= Seq_Length(s);
    ensures  Seq_Equal(r, Seq_Take(s, k));
{
    Seq_Cons_All<A>();
    var iter := s;
    var j := k;
    var rev0 := Seq_Nil();
    while (j != 0)
        decreases j;
        invariant 0 <= j;
        invariant k == j + Seq_Length(rev0);
        invariant Seq_Length(rev0) + Seq_Length(iter) == Seq_Length(s);
        invariant forall i {:trigger Seq_Index(rev0, i)}::0 <= i < Seq_Length(rev0) ==> Seq_Index(rev0, i) == Seq_Index(s, Seq_Length(rev0) - i - 1);
        invariant Seq_Equal(iter, Seq_Drop(s, Seq_Length(s) - Seq_Length(iter)));
    {
        lemma_Seq_Head(iter);
        lemma_Seq_Tail(iter);
        lemma_Seq_Cons(iter.hd, rev0);
        j := j - 1;
        rev0 := Seq_Cons(iter.hd, rev0);
        iter := iter.tl;
    }
    iter := rev0;
    r := Seq_Nil();
    while (iter.Seq_Cons?)
        decreases Seq_Length(iter);
        invariant Seq_Length(r) + Seq_Length(iter) == k;
        invariant forall i {:trigger Seq_Index(iter, i)}::0 <= i < Seq_Length(iter) ==> Seq_Index(iter, i) == Seq_Index(s, Seq_Length(iter) - i - 1);
        
        invariant Seq_Equal(r, Seq_Drop(Seq_Take(s, k), Seq_Length(iter)));
    {
        Seq_Seq(iter);
        lemma_Seq_Case(iter);
        lemma_Seq_Head(iter);
        lemma_Seq_Tail(iter);
        lemma_Seq_Cons(iter.hd, r);
        r := Seq_Cons(iter.hd, r);
        iter := iter.tl;
    }
    lemma_Seq_Case(iter);
}

method seq_Drop<A>(s:Seq<A>, k:int) returns(r:Seq<A>)
    requires 0 <= k <= Seq_Length(s);
    ensures  Seq_Equal(r, Seq_Drop(s, k));
{
    Seq_Cons_All<A>();
    var iter := s;
    var j := k;
    var rev0 := Seq_Nil();
    while (j != 0)
        decreases j;
        invariant 0 <= j;
        invariant k == j + Seq_Length(rev0);
        invariant Seq_Length(rev0) + Seq_Length(iter) == Seq_Length(s);
        invariant forall i {:trigger Seq_Index(rev0, i)}::0 <= i < Seq_Length(rev0) ==> Seq_Index(rev0, i) == Seq_Index(s, Seq_Length(rev0) - i - 1);
        invariant Seq_Equal(iter, Seq_Drop(s, Seq_Length(s) - Seq_Length(iter)));
    {
        lemma_Seq_Head(iter);
        lemma_Seq_Tail(iter);
        lemma_Seq_Cons(iter.hd, rev0);
        j := j - 1;
        rev0 := Seq_Cons(iter.hd, rev0);
        iter := iter.tl;
    }
    r := iter;
}

method seq_TakeDrop<A>(s:Seq<A>, k1:int, k2:int) returns(r:Seq<A>)
    requires 0 <= k1 <= k2 <= Seq_Length(s);
    ensures  Seq_Equal(r, Seq_Drop(Seq_Take(s, k2), k1));
{
    r := seq_Drop(s, k1);
    r := seq_Take(r, k2 - k1);
}

method seq_Equal<A(==)>(s1:Seq<A>, s2:Seq<A>) returns(b:bool)
    ensures  b == Seq_Equal(s1, s2);
{
    Seq_Cons_All<A>();
    var iter1 := s1;
    var iter2 := s2;
    while (iter1.Seq_Cons? && iter2.Seq_Cons?)
        decreases Seq_Length(iter1);
        invariant Seq_Length(iter1) <= Seq_Length(s1);
        invariant Seq_Length(iter2) <= Seq_Length(s2);
        invariant Seq_Equal(Seq_Take(s1, Seq_Length(s1) - Seq_Length(iter1)), Seq_Take(s2, Seq_Length(s2) - Seq_Length(iter2)));
        invariant Seq_Equal(iter1, Seq_Drop(s1, Seq_Length(s1) - Seq_Length(iter1)));
        invariant Seq_Equal(iter2, Seq_Drop(s2, Seq_Length(s2) - Seq_Length(iter2)));
    {
        Seq_Seq(iter1);
        lemma_Seq_Head(iter1);
        lemma_Seq_Tail(iter1);
        lemma_Seq_Head(iter2);
        lemma_Seq_Tail(iter2);
        if (iter1.hd != iter2.hd)
        {
            b := false;
            return;
        }
        ghost var n1 := Seq_Length(s1) - Seq_Length(iter1);
        assert Seq_Equal(
            Seq_Append(Seq_Take(s1, n1), Seq_Singleton(Seq_Index(s1, n1))),
            Seq_Take(s1, n1 + 1));
        ghost var n2 := Seq_Length(s2) - Seq_Length(iter2);
        assert Seq_Equal(
            Seq_Append(Seq_Take(s2, n2), Seq_Singleton(Seq_Index(s2, n2))),
            Seq_Take(s2, n2 + 1));
        iter1 := iter1.tl;
        iter2 := iter2.tl;
    }
    if (iter1.Seq_Nil? && iter2.Seq_Nil?)
    {
        b := true;
        assert Seq_Equal(s1, Seq_Take(s1, Seq_Length(s1)));
        assert Seq_Equal(s2, Seq_Take(s2, Seq_Length(s2)));
        return;
    }
    b := false;
    return;
}

method seq_FromArray(a:array<int>) returns (r:Seq<int>)
    ensures  Seq_Equal(r, Seq_FromArray(a));
{
    Seq_Cons_All<int>();
    r := Seq_Nil();
    var j := a.Length;
    while (j != 0)
        invariant 0 <= j <= a.Length;
        invariant r == Seq_FromArrayRange(INTERNAL_array_elems(a), j, a.Length);
    {
        j := j - 1;
        r := Seq_Cons(a[j], r);
    }
    reveal_Seq_FromArrayElems();
}
