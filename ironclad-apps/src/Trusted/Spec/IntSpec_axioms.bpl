//-
//- Copyright (c) Microsoft Corporation.  All rights reserved.
//-

//- Axioms about bit vectors

axiom I(1bv32) == 1;

axiom (forall i1:int, i2:int::{B(i1),B(i2)} word(i1) && word(i2) ==> (i1 == i2 <==> B(i1) == B(i2)));
axiom (forall b1:bv32, b2:bv32::{I(b1),I(b2)} b1 == b2 <==> I(b1) == I(b2));

axiom (forall b:bv32::{I(b)} word(I(b)));
axiom (forall b:bv32::{B(I(b))} B(I(b)) == b);
axiom (forall i:int::{I(B(i))} word(i) ==> I(B(i)) == i);

axiom (forall i1:int, i2:int::{add(i1, i2)} word(i1) && word(i2) && word(add(i1, i2)) ==> add(i1, i2) == I($add(B(i1), B(i2))));
axiom (forall i1:int, i2:int::{sub(i1, i2)} word(i1) && word(i2) && word(sub(i1, i2)) ==> sub(i1, i2) == I($sub(B(i1), B(i2))));
axiom (forall i1:int, i2:int::{mul(i1, i2)} word(i1) && word(i2) && word(mul(i1, i2)) ==> mul(i1, i2) == I($mul(B(i1), B(i2))));
axiom (forall i1:int, i2:int::{_div(i1, i2)} word(i1) && word(i2) && word(_div(i1, i2)) ==> _div(i1, i2) == I($div(B(i1), B(i2))));
axiom (forall i1:int, i2:int::{_mod(i1, i2)} word(i1) && word(i2) && word(_mod(i1, i2)) ==> _mod(i1, i2) == I($mod(B(i1), B(i2))));
axiom (forall i1:int, i2:int::{le(i1, i2)}  word(i1) && word(i2) ==> le(i1, i2) == $le(B(i1), B(i2)) );
axiom (forall i1:int, i2:int::{lt(i1, i2)}  word(i1) && word(i2) ==> lt(i1, i2) == $lt(B(i1), B(i2)) );
axiom (forall i1:int, i2:int::{ge(i1, i2)}  word(i1) && word(i2) ==> ge(i1, i2) == $ge(B(i1), B(i2)) );
axiom (forall i1:int, i2:int::{gt(i1, i2)}  word(i1) && word(i2) ==> gt(i1, i2) == $gt(B(i1), B(i2)) );

axiom (forall i1:int, i2:int::{and(i1, i2)}  and(i1, i2) == I($and(B(i1), B(i2))) );
axiom (forall i1:int, i2:int::{or(i1, i2)}   or (i1, i2) == I($or (B(i1), B(i2))) );
axiom (forall i1:int, i2:int::{xor(i1, i2)}  xor(i1, i2) == I($xor(B(i1), B(i2))) );
axiom (forall i1:int, i2:int::{shl(i1, i2)}  shl(i1, i2) == I($shl(B(i1), B(i2))) );
axiom (forall i1:int, i2:int::{shr(i1, i2)}  shr(i1, i2) == I($shr(B(i1), B(i2))) );
axiom (forall i:int::{neg(i)} neg(i) == I($neg(B(i))));

axiom (forall i:int::{Aligned(i)} word(i) ==> Aligned(i) == ($and(B(i), 3bv32) == 0bv32));

