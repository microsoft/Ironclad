include "../../../Dafny/Libraries/base.s.dfy"
static function{:imported} unroll_all(i:int):bool { true }
static function{:imported} INTERNAL_add_raw(x:int, y:int):int { x + y }
static function{:imported} INTERNAL_sub_raw(x:int, y:int):int { x + y }
type INTERNAL_AbsMem;
type INTERNAL_ArrayElems;
static function{:imported} INTERNAL_array_elems(a:array<int>):INTERNAL_ArrayElems
static function{:imported} INTERNAL_array_elems_index(a:INTERNAL_ArrayElems, k:int):int
static function{:imported} INTERNAL_array_elems_update(a:INTERNAL_ArrayElems, k:int, v:int):INTERNAL_ArrayElems
static function{:imported} INTERNAL_array_update(a:array<int>, k:int, v:int):INTERNAL_AbsMem


