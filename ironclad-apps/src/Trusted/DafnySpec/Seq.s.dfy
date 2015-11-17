include "../../Dafny/Libraries/base.s.dfy"

//- Trusted sequence definitions (used in trusted specifications)

datatype Seq<A> = Seq_Nil() | Seq_Cons(hd:A, tl:Seq<A>);

function{:opaque} Seq_Length<A>(s:Seq<A>):int
    ensures  Seq_Length(s) >= 0;
{
    if s.Seq_Cons? then 1 + Seq_Length(s.tl) else 0
}

function Seq_Empty<A>():Seq<A> { Seq_Nil() }

function{:opaque} Seq_Singleton<A>(a:A):Seq<A> { Seq_Cons(a, Seq_Nil()) }

function{:opaque} Seq_Build<A>(s:Seq<A>, a:A):Seq<A>
{
    if s.Seq_Cons? then Seq_Cons(s.hd, Seq_Build(s.tl, a)) else Seq_Singleton(a)
}

function Seq_Dummy<A>():A

function{:opaque} Seq_Index<A>(s:Seq<A>, k:int):A
{
    if s.Seq_Cons? then
        if k == 0 then s.hd
        else Seq_Index(s.tl, k - 1)
    else Seq_Dummy()
}




function Seq_Equal<A>(s0:Seq<A>, s1:Seq<A>):bool { s0 == s1 }

function{:opaque} Seq_Append<A>(s0:Seq<A>, s1:Seq<A>):Seq<A>
{
    if s0.Seq_Cons? then Seq_Cons(s0.hd, Seq_Append(s0.tl, s1)) else s1
}

function{:opaque} Seq_Update<A>(s:Seq<A>, k:int, a:A):Seq<A>
{
    if s.Seq_Cons? then
        if k == 0 then Seq_Cons(a, s.tl)
        else Seq_Cons(s.hd, Seq_Update(s.tl, k - 1, a))
    else s
}

function{:opaque} Seq_Take<A>(s:Seq<A>, n:int):Seq<A>
{
    if s.Seq_Cons? && n > 0 then Seq_Cons(s.hd, Seq_Take(s.tl, n - 1)) else Seq_Nil()
}

function{:opaque} Seq_Drop<A>(s:Seq<A>, n:int):Seq<A>
{
    if s.Seq_Cons? && n > 0 then Seq_Drop(s.tl, n - 1) else s
}

lemma Seq_Seq<A>(s:Seq<A>)
    ensures  0 <= sizeof(s);
    ensures  s.Seq_Nil? != s.Seq_Cons?;
    ensures{:typearg "A"}  s.Seq_Nil? <==> s == Seq_Nil();
    ensures  s.Seq_Cons? ==> Seq_Cons(s.hd, s.tl) == s;
    ensures  s.Seq_Cons? ==> 0 <= sizeof(s.tl) < sizeof(s);
{
}

lemma Seq_Cons_All<A>()
    ensures  forall s:Seq<A> :: s.Seq_Nil? != s.Seq_Cons?;
    ensures{:typearg "A"}  forall s:Seq<A> :: s.Seq_Nil? <==> s == Seq_Nil();
    ensures  forall hd:A, tl:Seq<A> :: Seq_Cons(hd, tl).Seq_Cons?;
    ensures  forall hd:A, tl:Seq<A> :: Seq_Cons(hd, tl).hd == hd;
    ensures  forall hd:A, tl:Seq<A> :: Seq_Cons(hd, tl).tl == tl;
{
}




//






