//-
//- Copyright (c) Microsoft Corporation.  All rights reserved.
//-

//-////////////////////////////////////////////////////////////////////////////
//- WORDS
//-////////////////////////////////////////////////////////////////////////////

axiom WORD_HI >= 100; // REVIEW: should we go ahead and set WORD_HI to exactly 2^32?

// REVIEW: one would hope that this axiom is derivable from
// Mult(a, b) == a * b, using b = b1 + b2, but Z3 couldn't seem to do it yet:
axiom (forall a:int, b1:int, b2:int::{TVM3(a, b1, b2)} Mult(a, b1 + b2) == a * (b1 + b2));

