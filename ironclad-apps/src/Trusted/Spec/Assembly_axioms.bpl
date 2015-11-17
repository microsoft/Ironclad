//-
//- Copyright (c) Microsoft Corporation.  All rights reserved.
//-

//-////////////////////////////////////////////////////////////////////////////
//- ASSEMBLY LANGUAGE
//-////////////////////////////////////////////////////////////////////////////

//-///// Flag Handling ////////////

axiom (forall f:int, x:int, y:int::{Je (Efl_Cmp(f, x, y))} Je (Efl_Cmp(f, x, y)) == (x == y));
axiom (forall f:int, x:int, y:int::{Jne(Efl_Cmp(f, x, y))} Jne(Efl_Cmp(f, x, y)) == (x != y));
axiom (forall f:int, x:int, y:int::{Jbe(Efl_Cmp(f, x, y))} Jbe(Efl_Cmp(f, x, y)) == (x <= y));
axiom (forall f:int, x:int, y:int::{Jb (Efl_Cmp(f, x, y))} Jb (Efl_Cmp(f, x, y)) == (x <  y));
axiom (forall f:int, x:int, y:int::{Jae(Efl_Cmp(f, x, y))} Jae(Efl_Cmp(f, x, y)) == (x >= y));
axiom (forall f:int, x:int, y:int::{Ja (Efl_Cmp(f, x, y))} Ja (Efl_Cmp(f, x, y)) == (x >  y));

axiom (forall f:int, x:int, y:int::{Cf (Efl_Add(f, x, y))} Cf (Efl_Add(f, x, y)) == (x + y >=  WORD_HI));
