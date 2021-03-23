include "AppInterface.i.dfy"

module Impl__AppInterfaceConcrete_i refines Impl__AppInterface_i {
export Spec
    provides Common__GenericMarshalling_i, AppInterface_i
    provides Key_grammar, Value_grammar
    provides parse_Key, parse_Value
    provides MarshallKey, MarshallValue, IsKeyValid, IsValueValid, IsKeyLt
    provides lemma_ValidKey_grammer, lemma_ValidValue_grammer
export All reveals *

function method Key_grammar() : G { GUint64 }  
function method Value_grammar() : G { GByteArray  }

function method parse_Key(val:V) : Key
{
    val.u
}

function method parse_Value(val:V) : Value
{
    val.b
}

method MarshallKey(c:Key) returns (val:V)
{
    val := VUint64(c);
}

method MarshallValue(c:Value) returns (val:V)
{
    val := VByteArray(c);
}

method IsKeyValid(key:Key) returns (b:bool)
{
    b := true;
}

method IsValueValid(val:Value) returns (b:bool)
{
    b := |val| < 1024;
}

method IsKeyLt(k:Key, k':Key) returns (b:bool)
{
    b := k < k';
}

lemma lemma_ValidKey_grammer()
{
}


lemma lemma_ValidValue_grammer()
{
}

//function method KeyRangeSize(kr:KeyRange) : uint64
//{
//    if KeyPlusLe(kr.khi, kr.klo) then 0
//    else
//        KeyPlusAntisymmetry(kr.khi, kr.klo);
//        assert !kr.khi.KeyZero?;
//        assert !kr.klo.KeyInf?;
//        var upper := if kr.khi.KeyInf? then 0xFFFF_FFFF_FFFF_FFFF else kr.khi.k;
//        var lower := if kr.klo.KeyZero? then 0 else kr.klo.k;
//        assert lower <= upper;
//        upper - lower
//}

}
