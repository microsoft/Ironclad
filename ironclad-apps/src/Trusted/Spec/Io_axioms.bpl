//-
//- Copyright (c) Microsoft Corporation.  All rights reserved.
//-

//// REVIEW: Why is the bound inclusive?
//axiom (forall i:int,size:int::{inRo(i,size)} ?RoBiosLo <= i && i + size <= ?RoBiosHi ==> inRo(i,size));
//
//axiom (forall ptr:int::{ByteSum(ptr, ptr)} ByteSum(ptr, ptr) == 0);
//axiom (forall ptr:int,end:int::{ByteSum(ptr, end)} ptr <= end ==> ByteSum(ptr, end + 1) == ByteSum(ptr, end) + roU8(end));
//
//axiom ?RsdpExists ==>
//    ?RsdtPtr == ro32(?RsdpPtr + 16)
// && inRo(?RsdtPtr + 4, 4)
// && 36 + 4 * ?RsdtCount == ro32(?RsdtPtr + 4)
// && ?RsdtCount >= 0
// && word(?RsdtPtr) && word(?RsdtPtr + 36 + 4 * ?RsdtCount)
// && (forall i:int::{TV(i)} TV(i) && 0 <= i && i < ?RsdtCount ==>
//         inRo(     ?RsdtPtr + 36 + 4 * i,  4)
//      && inRo(ro32(?RsdtPtr + 36 + 4 * i), 4));
//
//axiom ?DmarExists ==>
//    inRo(?DmarPtr + 4, 4)
// && ?DmarLen == ro32(?DmarPtr + 4)
// && ?DmarLen >= 48
// && word(?DmarPtr) && word(?DmarPtr + ?DmarLen)
// && MaybeDrhd(?DmarPtr + 48, 0);
//
////axiom word(?BYTE_VECTOR_VTABLE);
