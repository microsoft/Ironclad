//-
//- Copyright (c) Microsoft Corporation.  All rights reserved.
//-

//-////////////////////////////////////////////////////////////////////////////
//- GC-CONTROLLED MEMORY
//-////////////////////////////////////////////////////////////////////////////

//- Aligned(i) <==> i is a multiple of 4
axiom (forall i:int, j:int::{TV(i), TO(j)} TV(i) && TO(j) ==> Aligned(i) == Aligned(i + 4 * j));

axiom NULL < ?memLo;

axiom ?memLo <= ?memHi;
axiom ?memHi < WORD_HI;

axiom Aligned(?memLo);
axiom Aligned(?memHi);

