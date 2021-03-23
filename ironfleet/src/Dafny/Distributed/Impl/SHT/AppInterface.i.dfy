include "../Common/GenericMarshalling.i.dfy"
include "../../Protocol/SHT/Keys.i.dfy"

abstract module Impl__AppInterface_i {
import opened Common__GenericMarshalling_i
import opened SHT__Keys_i
import opened AppInterface_i`All

//////////////////////////////////////////////////////////////////////////////////
// The application's implementation supplies these functions, lemmas, etc.
//////////////////////////////////////////////////////////////////////////////////

function method Key_grammar() : G 
function method Value_grammar() : G 

function method parse_Key(val:V) : Key
    requires ValInGrammar(val, Key_grammar());

function method parse_Value(val:V) : Value
    requires ValInGrammar(val, Value_grammar());

method MarshallKey(c:Key) returns (val:V)
    requires ValidKey(c);
    ensures  ValInGrammar(val, Key_grammar());
    ensures  ValidVal(val);
    ensures  parse_Key(val) == c;
    ensures  0 <= SizeOfV(val) < 8 + max_key_len();

method MarshallValue(c:Value) returns (val:V)
    requires ValidValue(c);
    ensures  ValInGrammar(val, Value_grammar());
    ensures  ValidVal(val);
    ensures  parse_Value(val) == c;
    ensures  0 <= SizeOfV(val) < 8 + max_val_len();

method IsKeyValid(key:Key) returns (b:bool)
    ensures b == ValidKey(key);

method IsValueValid(val:Value) returns (b:bool)
    ensures b == ValidValue(val);

method IsKeyLt(k:Key, k':Key) returns (b:bool)
    ensures b == KeyLt(k, k');

lemma lemma_ValidKey_grammer()
    ensures ValidGrammar(Key_grammar());

lemma lemma_ValidValue_grammer()
    ensures ValidGrammar(Value_grammar());

//function method KeyRangeSize(kr:KeyRange) : uint64


}
