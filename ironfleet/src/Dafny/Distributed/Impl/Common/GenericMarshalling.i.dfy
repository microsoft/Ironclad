//include "../../../Libraries/Util/be_sequences.s.dfy"
include "../../Common/Native/NativeTypes.s.dfy"
include "../../Common/Collections/Maps.i.dfy"
include "../../Common/Collections/Seqs.i.dfy"
include "../../Common/Logic/Option.i.dfy"
include "Util.i.dfy"
include "MarshallInt.i.dfy"

module Common__GenericMarshalling_i {
//import opened Util__be_sequences_s
import opened Native__NativeTypes_s
import opened Collections__Maps_i
import opened Collections__Seqs_i 
import opened Logic__Option_i
import opened Common__Util_i
import opened Common__MarshallInt_i

datatype G = GUint64
           | GArray(elt:G)
           | GTuple(t:seq<G>)
           | GByteArray
           | GTaggedUnion(cases:seq<G>)

datatype V = VUint64(u:uint64)
           | VArray(a:seq<V>)
           | VTuple(t:seq<V>)
           | VByteArray(b:seq<byte>)
           | VCase(c:uint64, val:V)

predicate ValInGrammar(val:V, grammar:G)
{
    match val
        case VUint64(_) => grammar.GUint64?
        case VArray(a)  => grammar.GArray? && forall v :: v in a ==> ValInGrammar(v, grammar.elt)
        case VTuple(t)  => grammar.GTuple? && |t| == |grammar.t|
                              && forall i :: 0 <= i < |t| ==> ValInGrammar(t[i], grammar.t[i])
        case VByteArray(b) => grammar.GByteArray?
        case VCase(c, v) => grammar.GTaggedUnion? && int(c) < |grammar.cases| && ValInGrammar(v, grammar.cases[c])
}

// We only support reasonably sized grammars
predicate ValidGrammar(grammar:G) 
{
    match grammar
        case GUint64 => true
        case GArray(elt) => ValidGrammar(elt)
        case GTuple(t) => |t| < 0x1_0000_0000_0000_0000 && (forall g :: g in t ==> ValidGrammar(g))
        case GByteArray => true
        case GTaggedUnion(cases) => |cases| < 0x1_0000_0000_0000_0000 && (forall g :: g in cases ==> ValidGrammar(g))
}

// We can't encode values that are not valid
predicate ValidVal(val:V)
{
    match val
        case VUint64(_)    => true
        case VArray(a)     => |a| < 0x1_0000_0000_0000_0000 && forall v :: v in a ==> ValidVal(v)
        case VTuple(t)     => |t| < 0x1_0000_0000_0000_0000 && forall v :: v in t ==> ValidVal(v)
        case VByteArray(b) => |b| < 0x1_0000_0000_0000_0000
        case VCase(c, v) => ValidVal(v)

}

function {:opaque} SeqSum(t:seq<V>) : int
    ensures SeqSum(t) >= 0;
{
    if |t| == 0 then 0
    else SizeOfV(t[0]) + SeqSum(t[1..])
}

function SizeOfV(val:V) : int
    ensures SizeOfV(val) >= 0;
{
    match val
        case VUint64(_)     => 8
        case VArray(a)      => 8 + SeqSum(a)     // 8 bytes for length
        case VTuple(t)      => SeqSum(t)
        case VByteArray(b)  => 8 + |b|          // 8 bytes for a length field
        case VCase(c, v)  => 8 + SizeOfV(v)     // 8 bytes for the case identifier
}

function method parse_Uint64(data:seq<byte>) : (Option<V>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
{
    if uint64(|data|) >= Uint64Size() then
        (Some(VUint64(SeqByteToUint64(data[..Uint64Size()]))), data[Uint64Size()..])
    else
        (None, [])
}

method ParseUint64(data:array<byte>, index:uint64) returns (success:bool, v:V, rest_index:uint64)
    requires data != null;
    requires int(index) <= data.Length;
    requires data.Length < 0x1_0000_0000_0000_0000;
    ensures  int(rest_index) <= data.Length;
    ensures  var (v', rest') := parse_Uint64(data[index..]);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
{
    lemma_2toX();

    if uint64(data.Length) >= 8 && index <= uint64(data.Length) - 8 {
    // Avoids overflow and equvalent to: if index + 8 < uint64(data.Length) {
        var result := uint64(data[index + uint64(0)]) * 0x1_00_0000_0000_0000
                    + uint64(data[index + uint64(1)]) * 0x1_00_0000_0000_00
                    + uint64(data[index + uint64(2)]) * 0x1_00_0000_0000
                    + uint64(data[index + uint64(3)]) * 0x1_00_0000_00
                    + uint64(data[index + uint64(4)]) * 0x1_00_0000
                    + uint64(data[index + uint64(5)]) * 0x1_00_00
                    + uint64(data[index + uint64(6)]) * 0x1_00
                    + uint64(data[index + uint64(7)]);
        success := true;
        v := VUint64(result);
        rest_index := index + Uint64Size();
    } else {
        success := false;
        rest_index := uint64(data.Length);
    }
}

function method {:opaque} parse_Array_contents(data:seq<byte>, eltType:G, len:uint64) : (Option<seq<V>>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(eltType);
    decreases eltType, 1, len;
    ensures var (opt_seq, rest) := parse_Array_contents(data, eltType, len);
            |rest| <= |data| && (opt_seq.Some? ==> forall i :: 0 <= i < |opt_seq.v| ==> ValInGrammar(opt_seq.v[i], eltType));
{
   if len == 0 then
       (Some([]), data)
   else
       var (val, rest1) := parse_Val(data, eltType);
       var (others, rest2) := parse_Array_contents(rest1, eltType, len - 1);
       if !val.None? && !others.None? then
           (Some([val.v] + others.v), rest2)
       else
           (None, [])
}

datatype ContentsTraceStep = ContentsTraceStep(data:seq<byte>, val:Option<V>)

lemma lemma_ArrayContents_helper(data:seq<byte>, eltType:G, len:uint64, v:seq<V>, trace:seq<ContentsTraceStep>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(eltType);
    requires |trace| == int(len) + 1;
    requires |v| == int(len);
    requires forall j :: 0 <= j < |trace| ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
    requires trace[0].data == data;
    requires forall j :: 0 < j < int(len)+1 ==> 
                    trace[j].val  == parse_Val(trace[j-1].data, eltType).0
                 && trace[j].data == parse_Val(trace[j-1].data, eltType).1;
    requires forall j :: 0 < j < |trace| ==> trace[j].val.Some?;
    requires forall j :: 0 < j < |trace| ==> v[j-1] == trace[j].val.v;
    //requires v == ExtractValues(trace[1..]);
    decreases len;
    ensures  var (v', rest') := parse_Array_contents(data, eltType, len);
             var v_opt := Some(v);
             v_opt == v' && trace[|trace|-1].data == rest';
{
    reveal_parse_Array_contents();
    if len == 0 {
    } else {
        var tuple := parse_Val(data, eltType);
        var val, rest1 := tuple.0, tuple.1;
        assert trace[1].data == rest1;
        assert val.Some?;
        assert trace[1].val == val;
        lemma_ArrayContents_helper(rest1, eltType, len-1, v[1..], trace[1..]);
        var tuple'' := parse_Array_contents(rest1, eltType, len-1);
        var v'', rest'' := tuple''.0, tuple''.1;
        var v_opt'' := Some(v[1..]);
        assert v_opt'' == v'' && trace[1..][|trace[1..]|-1].data == rest'';

        var tuple' := parse_Array_contents(data, eltType, len);
        var v', rest' := tuple'.0, tuple'.1;
        calc { 
            v'; 
            Some([val.v] + v''.v);
            Some([val.v] + v[1..]);
            Some([v[0]] + v[1..]);
                { assert v == [v[0]] + v[1..]; }
            Some(v);
        }
        assert rest' == rest'';
    }
}

lemma lemma_ArrayContents_helper_bailout(data:seq<byte>, eltType:G, len:uint64, trace:seq<ContentsTraceStep>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(eltType);
    requires 1 < |trace| <= int(len) + 1;
    //requires |v| == int(len);
    requires forall j :: 0 <= j < |trace| ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
    requires trace[0].data == data;
    requires forall j :: 0 < j < |trace| ==> 
                    trace[j].val  == parse_Val(trace[j-1].data, eltType).0
                 && trace[j].data == parse_Val(trace[j-1].data, eltType).1;
    requires forall j :: 0 < j < |trace| - 1 ==> trace[j].val.Some?;
    //requires forall j :: 0 < j < |trace| - 1 ==> v[j-1] == trace[j].val.v;
    requires trace[|trace|-1].val.None?;
    //requires v == ExtractValues(trace[1..]);
    decreases len;
    ensures  var (v', rest') := parse_Array_contents(data, eltType, len);
             v'.None? && rest' == [];
{
    reveal_parse_Array_contents();
    
    var tuple := parse_Val(data, eltType);
    var val, rest1 := tuple.0, tuple.1;
    if |trace| == 2 {
        assert val.None?;
        var tuple' := parse_Array_contents(data, eltType, len);
        var v', rest' := tuple'.0, tuple'.1;
        assert v'.None?;
        assert rest' == [];
    } else {
        lemma_ArrayContents_helper_bailout(rest1, eltType, len-1, trace[1..]);
    }
}

method{:timeLimitMultiplier 2} ParseArrayContents(data:array<byte>, index:uint64, eltType:G, len:uint64) 
       returns (success:bool, v:seq<V>, rest_index:uint64)
    requires data != null;
    requires int(index) <= data.Length;
    requires data.Length < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(eltType);
    decreases eltType, 1, len;
    ensures  int(rest_index) <= data.Length;
    ensures  var (v', rest') := parse_Array_contents(data[index..], eltType, len);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
    ensures  success ==> ValidVal(VArray(v));
{
    reveal_parse_Array_contents();
    var vArr := new V[len];
    ghost var g_v := [];
    success := true;
    var i:uint64 := 0;
    var next_val_index:uint64 := index;
    ghost var trace := [ContentsTraceStep(data[index..], None())];

    while i < len
        invariant 0 <= i <= len;
        invariant index <= next_val_index <= uint64(data.Length);
        invariant |trace| == int(i) + 1;
        invariant |g_v| == int(i);
        invariant vArr[..i] == g_v;
        invariant trace[0].data == data[index..];
        invariant forall j :: 0 <= j < int(i)+1 ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
        invariant trace[i].data == data[next_val_index..];
        invariant forall j :: 0 < j <= i ==> trace[j].val.Some?;
        invariant forall j :: 0 < j <= i ==> g_v[j-1] == trace[j].val.v;
        invariant forall j :: 0 < j < int(i)+1 ==> 
            trace[j].val  == parse_Val(trace[j-1].data, eltType).0
         && trace[j].data == parse_Val(trace[j-1].data, eltType).1
        invariant ValidVal(VArray(vArr[..i]));
    {
        var some1, val, rest1 := ParseVal(data, next_val_index, eltType);
        ghost var step := ContentsTraceStep(data[rest1..], if some1 then Some(val) else None());
        ghost var old_trace := trace;
        trace := trace + [step];
        if !some1 {
            success := false;
            rest_index := uint64(data.Length);
            lemma_ArrayContents_helper_bailout(data[index..], eltType, len, trace);
            return;
        }
        g_v := g_v + [val];
        vArr[i] := val;
        next_val_index := rest1;

        i := i + 1;
    }

    success := true;
    rest_index := next_val_index;
    v := vArr[..];               
    lemma_ArrayContents_helper(data[index..], eltType, len, v, trace);
}

function method parse_Array(data:seq<byte>, eltType:G) : (Option<V>, seq<byte>)
    requires ValidGrammar(eltType);
    requires |data| < 0x1_0000_0000_0000_0000;
    decreases eltType;
    ensures var (opt_val, rest) := parse_Array(data, eltType);
            |rest| <= |data| && (opt_val.Some? ==> ValInGrammar(opt_val.v, GArray(eltType)));
{
    var (len, rest) := parse_Uint64(data);
    if !len.None? then
        var (contents, remainder) := parse_Array_contents(rest, eltType, len.v.u);
        if !contents.None? then
            (Some(VArray(contents.v)), remainder)
        else
            (None, [])
    else
        (None, [])
}

method ParseArray(data:array<byte>, index:uint64, eltType:G) returns (success:bool, v:V, rest_index:uint64)
    requires data != null;
    requires int(index) <= data.Length;
    requires data.Length < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(eltType);
    decreases eltType;
    ensures  int(rest_index) <= data.Length;
    ensures  var (v', rest') := parse_Array(data[index..], eltType);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
    ensures  success ==> ValidVal(v);
{
    var some1, len, rest := ParseUint64(data, index);
    if some1 {
        var some2, contents, remainder := ParseArrayContents(data, rest, eltType, len.u);
        if some2 {
            success := true;
            v := VArray(contents);
            rest_index := remainder;
        } else {
            success := false;
            rest_index := uint64(data.Length);
        }
    } else {
        success := false;
        rest_index := uint64(data.Length);
    }
}


function method {:opaque} parse_Tuple_contents(data:seq<byte>, eltTypes:seq<G>) : (Option<seq<V>>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |eltTypes| < 0x1_0000_0000_0000_0000;
    requires forall elt :: elt in eltTypes ==> ValidGrammar(elt);
    decreases eltTypes, 0;
    ensures var (opt_val, rest) := parse_Tuple_contents(data, eltTypes);
            |rest| <= |data| &&
            (opt_val.Some? ==> (|opt_val.v| == |eltTypes|
                              && forall i :: 0 <= i < |opt_val.v| ==> ValInGrammar(opt_val.v[i], eltTypes[i])));
{
    if eltTypes == [] then
        (Some([]), data)
    else
        var (val, rest1) := parse_Val(data, eltTypes[uint64(0)]);
        assert |rest1| <= |data|;
        var (contents, rest2) := parse_Tuple_contents(rest1, eltTypes[uint64(1)..]);
        if !val.None? && !contents.None? then
            (Some([val.v] + contents.v), rest2)
        else
            (None, [])
}


lemma lemma_TupleContents_helper(data:seq<byte>, eltTypes:seq<G>, v:seq<V>, trace:seq<ContentsTraceStep>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |eltTypes| < 0x1_0000_0000_0000_0000;
    requires forall elt :: elt in eltTypes ==> ValidGrammar(elt);
    requires |trace| == |eltTypes| + 1;
    requires |v| == int(|eltTypes|);
    requires forall j :: 0 <= j < |trace| ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
    requires trace[0].data == data;
    requires forall j :: 0 < j < int(|eltTypes|)+1 ==> 
                    trace[j].val  == parse_Val(trace[j-1].data, eltTypes[j-1]).0
                 && trace[j].data == parse_Val(trace[j-1].data, eltTypes[j-1]).1;
    requires forall j :: 0 < j < |trace| ==> trace[j].val.Some?;
    requires forall j :: 0 < j < |trace| ==> v[j-1] == trace[j].val.v;
    //requires v == ExtractValues(trace[1..]);
    decreases |eltTypes|;
    ensures  var (v', rest') := parse_Tuple_contents(data, eltTypes);
             var v_opt := Some(v);
             v_opt == v' && trace[|trace|-1].data == rest';
{
    reveal_parse_Tuple_contents();
    if |eltTypes| == 0 {
    } else {
        var tuple := parse_Val(data, eltTypes[0]);
        var val, rest1 := tuple.0, tuple.1;
        assert trace[1].data == rest1;
        assert val.Some?;
        assert trace[1].val == val;
        lemma_TupleContents_helper(rest1, eltTypes[1..], v[1..], trace[1..]);
        var tuple'' := parse_Tuple_contents(rest1, eltTypes[1..]);
        var v'', rest'' := tuple''.0, tuple''.1;
        var v_opt'' := Some(v[1..]);
        assert v_opt'' == v'' && trace[1..][|trace[1..]|-1].data == rest'';

        var tuple' := parse_Tuple_contents(data, eltTypes);
        var v', rest' := tuple'.0, tuple'.1;
        calc { 
            v'; 
            Some([val.v] + v''.v);
            Some([val.v] + v[1..]);
            Some([v[0]] + v[1..]);
                { assert v == [v[0]] + v[1..]; }
            Some(v);
        }
        assert rest' == rest'';
    }
}

lemma lemma_TupleContents_helper_bailout(data:seq<byte>, eltTypes:seq<G>, trace:seq<ContentsTraceStep>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |eltTypes| < 0x1_0000_0000_0000_0000;
    requires forall elt :: elt in eltTypes ==> ValidGrammar(elt);
    requires 1 < |trace| <= int(|eltTypes|) + 1;
    requires forall j :: 0 <= j < |trace| ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
    requires trace[0].data == data;
    requires forall j :: 0 < j < |trace| ==> 
                    trace[j].val  == parse_Val(trace[j-1].data, eltTypes[j-1]).0
                 && trace[j].data == parse_Val(trace[j-1].data, eltTypes[j-1]).1;
    requires forall j :: 0 < j < |trace| - 1 ==> trace[j].val.Some?;
    //requires forall j :: 0 < j < |trace| - 1 ==> v[j-1] == trace[j].val.v;
    requires trace[|trace|-1].val.None?;
    //requires v == ExtractValues(trace[1..]);
    decreases |eltTypes|;
    ensures  var (v', rest') := parse_Tuple_contents(data, eltTypes);
             v'.None? && rest' == [];
{
    reveal_parse_Tuple_contents();
    
    var tuple := parse_Val(data, eltTypes[0]);
    var val, rest1 := tuple.0, tuple.1;
    if |trace| == 2 {
        assert val.None?;
        var tuple' := parse_Tuple_contents(data, eltTypes);
        var v', rest' := tuple'.0, tuple'.1;
        assert v'.None?;
        assert rest' == [];
    } else {
        lemma_TupleContents_helper_bailout(rest1, eltTypes[1..], trace[1..]);
    }
}

method{:timeLimitMultiplier 2} ParseTupleContents(data:array<byte>, index:uint64, eltTypes:seq<G>) 
       returns (success:bool, v:seq<V>, rest_index:uint64)
    requires data != null;
    requires int(index) <= data.Length;
    requires data.Length < 0x1_0000_0000_0000_0000;
    requires |eltTypes| < 0x1_0000_0000_0000_0000;
    requires forall elt :: elt in eltTypes ==> ValidGrammar(elt);
    decreases eltTypes, 0;
    ensures  int(rest_index) <= data.Length;
    ensures  var (v', rest') := parse_Tuple_contents(data[index..], eltTypes);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
    ensures  success ==> ValidVal(VTuple(v));
{
    reveal_parse_Tuple_contents();
    var vArr := new V[uint64(|eltTypes|)];
    ghost var g_v := [];
    success := true;
    var i:uint64 := 0;
    var next_val_index:uint64 := index;
    ghost var trace := [ContentsTraceStep(data[index..], None())];

    while i < uint64(|eltTypes|) 
        invariant 0 <= int(i) <= |eltTypes|;
        invariant index <= next_val_index <= uint64(data.Length);
        invariant |trace| == int(i) + 1;
        invariant |g_v| == int(i);
        invariant vArr[..i] == g_v;
        invariant trace[0].data == data[index..];
        invariant forall j :: 0 <= j < int(i)+1 ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
        invariant trace[i].data == data[next_val_index..];
        invariant forall j :: 0 < j <= i ==> trace[j].val.Some?;
        invariant forall j :: 0 < j <= i ==> g_v[j-1] == trace[j].val.v;
        invariant forall j :: 0 < j < int(i)+1 ==> 
            trace[j].val  == parse_Val(trace[j-1].data, eltTypes[j-1]).0
         && trace[j].data == parse_Val(trace[j-1].data, eltTypes[j-1]).1
        invariant ValidVal(VTuple(vArr[..i]));
    {
        var some1, val, rest1 := ParseVal(data, next_val_index, eltTypes[i]);
        ghost var step := ContentsTraceStep(data[rest1..], if some1 then Some(val) else None());
        ghost var old_trace := trace;
        trace := trace + [step];
        if !some1 {
            success := false;
            rest_index := uint64(data.Length);
            lemma_TupleContents_helper_bailout(data[index..], eltTypes, trace);
            return;
        }
        g_v := g_v + [val];
        vArr[i] := val;
        next_val_index := rest1;

        i := i + 1;
    }

    success := true;
    rest_index := next_val_index;
    v := vArr[..];               
    lemma_TupleContents_helper(data[index..], eltTypes, v, trace);
}

function method parse_Tuple(data:seq<byte>, eltTypes:seq<G>) : (Option<V>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |eltTypes| < 0x1_0000_0000_0000_0000;
    requires forall elt :: elt in eltTypes ==> ValidGrammar(elt);
    decreases eltTypes, 1;
    ensures var (opt_val, rest) := parse_Tuple(data, eltTypes);
            |rest| <= |data| && (opt_val.Some? ==> ValInGrammar(opt_val.v, GTuple(eltTypes)));
{
    var (contents, rest) := parse_Tuple_contents(data, eltTypes);
    if !contents.None? then
        (Some(VTuple(contents.v)), rest)
    else
        (None, [])
}


method ParseTuple(data:array<byte>, index:uint64, eltTypes:seq<G>) returns (success:bool, v:V, rest_index:uint64)
    requires data != null;
    requires int(index) <= data.Length;
    requires data.Length < 0x1_0000_0000_0000_0000;
    requires |eltTypes| < 0x1_0000_0000_0000_0000;
    requires forall elt :: elt in eltTypes ==> ValidGrammar(elt);
    decreases eltTypes, 1;
    ensures  int(rest_index) <= data.Length;
    ensures  var (v', rest') := parse_Tuple(data[index..], eltTypes);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
    ensures  success ==> ValidVal(v);
{
    var some, contents, rest := ParseTupleContents(data, index, eltTypes);
    if some {
        success := true;
        v := VTuple(contents);
        rest_index := rest;
    } else {
        success := false;
        rest_index := uint64(data.Length);
    }
}

function method parse_ByteArray(data:seq<byte>) : (Option<V>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
{
    var (len, rest) := parse_Uint64(data);
    if !len.None? && len.v.u <= uint64(|rest|) then
        (Some(VByteArray(rest[uint64(0)..len.v.u])), rest[len.v.u..])
    else
        (None, [])
}

method ParseByteArray(data:array<byte>, index:uint64) returns (success:bool, v:V, rest_index:uint64)
    requires data != null;
    requires int(index) <= data.Length;
    requires data.Length < 0x1_0000_0000_0000_0000;
    ensures  int(rest_index) <= data.Length;
    ensures  var (v', rest') := parse_ByteArray(data[index..]);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
{
    var some, len, rest := ParseUint64(data, index);
    if some && len.u <= uint64(data.Length) - rest {
        var rest_seq := data[rest..];
        assert len.u <= uint64(|rest_seq|);
        calc {
            rest_seq[0..len.u];
            data[rest..rest + len.u];
        }
        success := true;
        v := VByteArray(data[rest..rest + len.u]);
        rest_index := rest + len.u;
    } else {
        success := false;
        rest_index := uint64(data.Length);
    }
}

function method parse_Case(data:seq<byte>, cases:seq<G>) : (Option<V>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |cases| < 0x1_0000_0000_0000_0000;
    requires forall elt :: elt in cases ==> ValidGrammar(elt);
    decreases cases;
    ensures var (opt_val, rest) := parse_Case(data, cases);
            |rest| <= |data| && (opt_val.Some? ==> ValInGrammar(opt_val.v, GTaggedUnion(cases)));
{
    var (caseID, rest1) := parse_Uint64(data);

    if !caseID.None? && caseID.v.u < uint64(|cases|) then
        var (val, rest2) := parse_Val(rest1, cases[caseID.v.u]);
        if !val.None? then
            (Some(VCase(caseID.v.u, val.v)), rest2)
        else
            (None, [])
    else
        (None, [])
}

method ParseCase(data:array<byte>, index:uint64, cases:seq<G>) returns (success:bool, v:V, rest_index:uint64)
    requires data != null;
    requires int(index) <= data.Length;
    requires data.Length < 0x1_0000_0000_0000_0000;
    requires |cases| < 0x1_0000_0000_0000_0000;
    requires forall elt :: elt in cases ==> ValidGrammar(elt);
    decreases cases;
    ensures  int(rest_index) <= data.Length;
    ensures  var (v', rest') := parse_Case(data[index..], cases);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
    ensures  success ==> ValidVal(v);
{
    var some1, caseID, rest1 := ParseUint64(data, index);

    if some1 && caseID.u < uint64(|cases|) {
        var some2, val, rest2 := ParseVal(data, rest1, cases[caseID.u]);
        if some2 {
            success := true;
            v := VCase(caseID.u, val);
            rest_index := rest2;
        } else {
            success := false;
            rest_index := uint64(data.Length);
        }
    } else {
        success := false;
        rest_index := uint64(data.Length);
    }
}

function method {:opaque} parse_Val(data:seq<byte>, grammar:G) : (Option<V>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(grammar);
    decreases grammar, 0;
    ensures  var (val, rest) := parse_Val(data, grammar);
             |rest| <= |data| && (!val.None? ==> ValInGrammar(val.v, grammar));
{
    match grammar
        case GUint64             => parse_Uint64(data)
        case GArray(elt)         => parse_Array(data, elt)
        case GTuple(t)           => parse_Tuple(data, t)
        case GByteArray          => parse_ByteArray(data)
        case GTaggedUnion(cases) => parse_Case(data, cases)
}

method ParseVal(data:array<byte>, index:uint64, grammar:G) returns (success:bool, v:V, rest_index:uint64)
    requires data != null;
    requires int(index) <= data.Length;
    requires data.Length < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(grammar);
    decreases grammar, 0;
    ensures  int(rest_index) <= data.Length;
    ensures  var (v', rest') := parse_Val(data[index..], grammar);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
    ensures  success ==> ValidVal(v);
{
    reveal_parse_Val();

    match grammar {
        case GUint64             => success, v, rest_index := ParseUint64(data, index);
        case GArray(elt)         => success, v, rest_index := ParseArray(data, index, elt);
        case GTuple(t)           => success, v, rest_index := ParseTuple(data, index, t);
        case GByteArray          => success, v, rest_index := ParseByteArray(data, index);
        case GTaggedUnion(cases) => success, v, rest_index := ParseCase(data, index, cases);
    }
}

predicate Demarshallable(data:seq<byte>, grammar:G)
{
       |data| < 0x1_0000_0000_0000_0000
    && ValidGrammar(grammar)
    && !parse_Val(data, grammar).0.None?
    && ValidVal(parse_Val(data, grammar).0.v)
    && parse_Val(data, grammar).1 == []
}

function DemarshallFunc(data:seq<byte>, grammar:G) : V
    requires Demarshallable(data, grammar);
    decreases grammar, 0;
    ensures  var (val, rest) := parse_Val(data, grammar);
             !val.None? && ValInGrammar(val.v, grammar);
{
    parse_Val(data, grammar).0.v
}

method Demarshall(data:array<byte>, grammar:G) returns (success:bool, v:V)
    requires data != null;
    requires data.Length < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(grammar);
    ensures  success == Demarshallable(data[..], grammar);
    ensures  success ==> v == DemarshallFunc(data[..], grammar);
{
    var rest:uint64;
    success, v, rest := ParseVal(data, 0, grammar);
    if success && rest == uint64(data.Length) {
        assert v == parse_Val(data[..], grammar).0.v;
        assert Demarshallable(data[..], grammar);
        assert v == DemarshallFunc(data[..], grammar);
    } else {
        success := false;
        assert !Demarshallable(data[..], grammar);
    }
}


lemma lemma_parse_Val_view_ByteArray(data:seq<byte>, v:V, grammar:G, index:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires grammar.GByteArray?;
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    ensures  forall bound :: Trigger(bound) ==> (index+SizeOfV(v) <= bound <= |data| ==>
             ((parse_ByteArray(data[index..bound]).0 == Some(v)) <==> (parse_ByteArray(data[index..index+SizeOfV(v)]).0 == Some(v))));
    ensures  forall bound :: index+SizeOfV(v) <= bound <= |data| ==>
             parse_ByteArray(data[index..bound]).0 == Some(v) ==> parse_ByteArray(data[index..bound]).1 == data[index+SizeOfV(v)..bound];
{
    forall bound {:trigger Trigger(bound)} | Trigger(bound)
        ensures index+SizeOfV(v) <= bound <= |data| ==> ((parse_ByteArray(data[index..bound]).0 == Some(v)) <==> (parse_ByteArray(data[index..index+SizeOfV(v)]).0 == Some(v)));
    {
        if index+SizeOfV(v) <= bound <= |data| {
            var narrow_tuple := parse_ByteArray(data[index..index+SizeOfV(v)]);
            var bound_tuple := parse_ByteArray(data[index..bound]);
            var narrow_len_tuple := parse_Uint64(data[index..index+SizeOfV(v)]);
            var bound_len_tuple := parse_Uint64(data[index..bound]);
            assert narrow_len_tuple.0 == bound_len_tuple.0;

            if bound_tuple.0 == Some(v) {
                assert bound_len_tuple.1[0..bound_len_tuple.0.v.u] == narrow_len_tuple.1[0..bound_len_tuple.0.v.u];     // OBSERVE
            }

            if narrow_tuple.0 == Some(v) {
                assert bound_len_tuple.1[0..bound_len_tuple.0.v.u] == narrow_len_tuple.1[0..bound_len_tuple.0.v.u];       // OBSERVE
            }
            assert ((parse_ByteArray(data[index..bound]).0 == Some(v)) <==> (parse_ByteArray(data[index..index+SizeOfV(v)]).0 == Some(v)));
        }
        assert index+SizeOfV(v) <= bound <= |data| ==> ((parse_ByteArray(data[index..bound]).0 == Some(v)) <==> (parse_ByteArray(data[index..index+SizeOfV(v)]).0 == Some(v)));
    }
    assert forall bound :: Trigger(bound) ==> (index+SizeOfV(v) <= bound <= |data| ==>
             ((parse_ByteArray(data[index..bound]).0 == Some(v)) <==> (parse_ByteArray(data[index..index+SizeOfV(v)]).0 == Some(v))));
    assert forall bound :: index+SizeOfV(v) <= bound <= |data| ==>
             parse_ByteArray(data[index..bound]).0 == Some(v) ==> parse_ByteArray(data[index..bound]).1 == data[index+SizeOfV(v)..bound];
}

lemma lemma_SeqSum_prefix(s:seq<V>, v:V)
    ensures SeqSum(s + [v]) == SeqSum(s) + SizeOfV(v);
{
    reveal_SeqSum();
    if |s| == 0 {
    } else {
        calc {
            SeqSum(s + [v]);
                { assert (s + [v])[0] == s[0];  
                  assert (s + [v])[1..] == s[1..]+[v]; }
            SizeOfV(s[0]) + SeqSum(s[1..] + [v]);
                { lemma_SeqSum_prefix(s[1..], v); }
            SizeOfV(s[0]) + SeqSum(s[1..]) + SizeOfV(v);
            SeqSum(s) + SizeOfV(v);
        }
    }
}

lemma lemma_SeqSum_bound(s:seq<V>, bound:int)
    requires SeqSum(s) < bound;
    ensures  forall v :: v in s ==> SizeOfV(v) < bound;
{
    reveal_SeqSum();
    if |s| == 0 {
    } else {
        assert SizeOfV(s[0]) + SeqSum(s[1..]) < bound;
        assert SizeOfV(s[0]) < bound;
        lemma_SeqSum_bound(s[1..], bound);
    }
}

lemma lemma_SeqSum_bound_prefix(s:seq<V>, prefix:seq<V>, index:int)
    requires 0 <= index <= |s|;
    requires prefix == s[..index];
    ensures  SeqSum(prefix) <= SeqSum(s);
{
    reveal_SeqSum();
    if |prefix| == 0 {
    } else {
        lemma_SeqSum_bound_prefix(s[1..], prefix[1..], index - 1);
    }
}

lemma lemma_parse_Array_contents_len(data:seq<byte>, eltType:G, len:uint64)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(eltType);
    requires len >= 0;
    requires !parse_Array_contents(data, eltType, len).0.None?;
    decreases len;
    ensures  int(len) == |parse_Array_contents(data, eltType, len).0.v|;
{
    reveal_parse_Array_contents();
    if len == 0 {
    } else {
       var tuple1 := parse_Val(data, eltType);
       var val   := tuple1.0;
       var rest1 := tuple1.1;
       var tuple2 := parse_Array_contents(rest1, eltType, len - 1);
       var others := tuple2.0;
       var rest2  := tuple2.1;
       assert !val.None? && !others.None?;
       lemma_parse_Array_contents_len(rest1, eltType, len - 1);
    }
}

lemma lemma_parse_Val_view_Array_contents(data:seq<byte>, vs:seq<V>, grammar:G, index:int, bound:int, len:uint64)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires forall v :: v in vs ==> ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires int(len) == |vs|;
    requires 0 <= index <= |data|;
    requires 0 <= index + SeqSum(vs) <= |data|;
    requires index+SeqSum(vs) <= bound <= |data|;
    decreases grammar, 1, len;
    //decreases |vs|;
    ensures  (parse_Array_contents(data[index..bound], grammar, len).0 == Some(vs)) <==> (parse_Array_contents(data[index..index+SeqSum(vs)], grammar, len).0 == Some(vs));
    ensures  parse_Array_contents(data[index..bound], grammar, len).0 == Some(vs) ==> parse_Array_contents(data[index..bound], grammar, len).1 == data[index+SeqSum(vs)..bound];
{
    reveal_parse_Array_contents();
    if len == 0 {
        reveal_SeqSum();
    } else {
        var narrow_tuple := parse_Array_contents(data[index..index+SeqSum(vs)], grammar, len);
        var bound_tuple := parse_Array_contents(data[index..bound], grammar, len);
        var narrow_val_tuple := parse_Val(data[index..index+SeqSum(vs)], grammar);
        var bound_val_tuple := parse_Val(data[index..bound], grammar);
        var narrow_contents_tuple := parse_Array_contents(narrow_val_tuple.1, grammar, len - 1);
        var bound_contents_tuple := parse_Array_contents(bound_val_tuple.1, grammar, len - 1);


        if narrow_tuple.0 == Some(vs) {
            assert !narrow_val_tuple.0.None? && !narrow_contents_tuple.0.None?;
            calc {
                index + SeqSum(vs) <= |data|;
                SeqSum(vs) <= |data| - index;
                SeqSum(vs) < |data| - index + 1;
            }
            lemma_SeqSum_bound(vs, |data| - index + 1);
            lemma_parse_Val_view(data, vs[0], grammar, index);

            lemma_SeqSum_bound(vs, SeqSum(vs) + 1);
            assert index+SizeOfV(vs[0]) <= bound <= |data|;
            assert (parse_Val(data[index..index+SeqSum(vs)], grammar).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar).0 == Some(vs[0]));
            lemma_SeqSum_bound(vs, bound - index + 1);
            assert index+SizeOfV(vs[0]) <= bound <= |data|;     // OBSERVE (trigger on forall?)
            assert (parse_Val(data[index..bound], grammar).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar).0 == Some(vs[0]));
            assert narrow_val_tuple.0.v == vs[0] == bound_val_tuple.0.v;

            var new_index := index + SizeOfV(narrow_val_tuple.0.v);
            calc {
                SizeOfV(narrow_val_tuple.0.v) + SeqSum(vs[1..]);
                    { reveal_SeqSum(); }
                SeqSum(vs);
            }
            assert new_index+SeqSum(vs[1..]) <= bound;

            lemma_parse_Val_view_Array_contents(data, vs[1..], grammar, new_index, bound, len - 1);

            assert (parse_Array_contents(data[new_index..bound], grammar, len - 1).0 == Some(vs[1..])) <==> (parse_Array_contents(data[new_index..new_index+SeqSum(vs[1..])], grammar, len - 1).0 == Some(vs[1..]));
            assert data[new_index..new_index+SeqSum(vs[1..])] == narrow_val_tuple.1;
            assert data[new_index..bound] == bound_val_tuple.1;

            assert bound_tuple.0 == Some([vs[0]] + vs[1..]) == Some(vs);
        } else if bound_tuple.0 == Some(vs) {
            assert !bound_val_tuple.0.None? && !bound_contents_tuple.0.None?;

            lemma_SeqSum_bound(vs, |data| - index + 1);
            lemma_parse_Val_view(data, vs[0], grammar, index);
            // This is exactly the ensures of the lemma above
            assert forall bound' :: index+SizeOfV(vs[0]) <= bound' <= |data| ==>
                   ((parse_Val(data[index..bound'], grammar).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar).0 == Some(vs[0])));

            lemma_SeqSum_bound(vs, bound - index + 1);
            lemma_SeqSum_bound(vs, SeqSum(vs) + 1);
            assert index+SizeOfV(vs[0]) <= index+SeqSum(vs) <= |data|;
            assert (parse_Val(data[index..index+SeqSum(vs)], grammar).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar).0 == Some(vs[0]));
            assert (parse_Val(data[index..bound], grammar).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar).0 == Some(vs[0]));
            assert narrow_val_tuple.0.v == vs[0] == bound_val_tuple.0.v;

            var new_index := index + SizeOfV(narrow_val_tuple.0.v);
            calc {
                SizeOfV(narrow_val_tuple.0.v) + SeqSum(vs[1..]);
                    { reveal_SeqSum(); }
                SeqSum(vs);
            }
            assert new_index+SeqSum(vs[1..]) <= bound;

            lemma_parse_Val_view_Array_contents(data, vs[1..], grammar, new_index, bound, len - 1);

            assert (parse_Array_contents(data[new_index..bound], grammar, len - 1).0 == Some(vs[1..])) <==> (parse_Array_contents(data[new_index..new_index+SeqSum(vs[1..])], grammar, len - 1).0 == Some(vs[1..]));
            assert data[new_index..new_index+SeqSum(vs[1..])] == narrow_val_tuple.1;
            assert data[new_index..bound] == bound_val_tuple.1;

            assert narrow_tuple.0 == Some([vs[0]] + vs[1..]) == Some(vs);
        } else {
            // Doesn't matter for our ensures clause
        }
    }
}

lemma lemma_parse_Val_view_Array(data:seq<byte>, v:V, grammar:G, index:int, bound:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires grammar.GArray?;
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    requires index+SizeOfV(v) <= bound <= |data|;
    decreases grammar, -1;
    ensures  (parse_Array(data[index..bound], grammar.elt).0 == Some(v)) <==> (parse_Array(data[index..index+SizeOfV(v)], grammar.elt).0 == Some(v));
    ensures  parse_Array(data[index..bound], grammar.elt).0 == Some(v) ==> parse_Array(data[index..bound], grammar.elt).1 == data[index+SizeOfV(v)..bound];
{
    var narrow_tuple := parse_Array(data[index..index+SizeOfV(v)], grammar.elt);
    var bound_tuple := parse_Array(data[index..bound], grammar.elt);
    var narrow_len_tuple := parse_Uint64(data[index..index+SizeOfV(v)]);
    var bound_len_tuple := parse_Uint64(data[index..bound]);
    var narrow_contents_tuple := parse_Array_contents(narrow_len_tuple.1, grammar.elt, narrow_len_tuple.0.v.u);
    var bound_contents_tuple := parse_Array_contents(bound_len_tuple.1, grammar.elt, bound_len_tuple.0.v.u);

    assert narrow_len_tuple.0 == bound_len_tuple.0;

    if bound_tuple.0 == Some(v) {
        assert parse_Array_contents(bound_len_tuple.1, grammar.elt, bound_len_tuple.0.v.u).0 == Some(v.a);   // OBSERVE
        lemma_parse_Array_contents_len(bound_len_tuple.1, grammar.elt, narrow_len_tuple.0.v.u);
        lemma_parse_Val_view_Array_contents(data, v.a, grammar.elt, index+8, bound, narrow_len_tuple.0.v.u);
    }

    if narrow_tuple.0 == Some(v) {
        assert parse_Array_contents(narrow_len_tuple.1, grammar.elt, narrow_len_tuple.0.v.u).0 == Some(v.a);   // OBSERVE
        lemma_parse_Array_contents_len(narrow_len_tuple.1, grammar.elt, narrow_len_tuple.0.v.u);
        lemma_parse_Val_view_Array_contents(data, v.a, grammar.elt, index+8, bound, narrow_len_tuple.0.v.u);
    }
}

lemma lemma_parse_Val_view_Tuple_contents(data:seq<byte>, vs:seq<V>, grammar:seq<G>, index:int, bound:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |vs| == |grammar|;
    requires forall i :: 0 <= i < |vs| ==> ValInGrammar(vs[i], grammar[i]);
    requires |grammar| < 0x1_0000_0000_0000_0000;
    requires forall g :: g in grammar ==> ValidGrammar(g);
    requires 0 <= index <= |data|;
    requires 0 <= index + SeqSum(vs) <= |data|;
    requires index+SeqSum(vs) <= bound <= |data|;
    decreases grammar, -1, vs;
    ensures  (parse_Tuple_contents(data[index..bound], grammar).0 == Some(vs)) <==> (parse_Tuple_contents(data[index..index+SeqSum(vs)], grammar).0 == Some(vs));
    ensures  parse_Tuple_contents(data[index..bound], grammar).0 == Some(vs) ==> parse_Tuple_contents(data[index..bound], grammar).1 == data[index+SeqSum(vs)..bound];
{
    reveal_parse_Tuple_contents();
    if grammar == [] {
        reveal_SeqSum();
    } else {
        var narrow_tuple := parse_Tuple_contents(data[index..index+SeqSum(vs)], grammar);
        var bound_tuple := parse_Tuple_contents(data[index..bound], grammar);
        var narrow_val_tuple := parse_Val(data[index..index+SeqSum(vs)], grammar[0]);
        var bound_val_tuple := parse_Val(data[index..bound], grammar[0]);
        var narrow_contents_tuple := parse_Tuple_contents(narrow_val_tuple.1, grammar[1..]);
        var bound_contents_tuple := parse_Tuple_contents(bound_val_tuple.1, grammar[1..]);


        if narrow_tuple.0 == Some(vs) {
            assert !narrow_val_tuple.0.None? && !narrow_contents_tuple.0.None?;
            calc {
                index + SeqSum(vs) <= |data|;
                SeqSum(vs) <= |data| - index;
                SeqSum(vs) < |data| - index + 1;
            }
            lemma_SeqSum_bound(vs, |data| - index + 1);
            lemma_parse_Val_view(data, vs[0], grammar[0], index);
            lemma_SeqSum_bound(vs, SeqSum(vs) + 1);
            assert index+SizeOfV(vs[0]) <= bound <= |data|;
            assert (parse_Val(data[index..index+SeqSum(vs)], grammar[0]).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar[0]).0 == Some(vs[0]));
            lemma_SeqSum_bound(vs, bound - index + 1);
            assert index+SizeOfV(vs[0]) <= bound <= |data|;     // OBSERVE (trigger on forall?)
            assert (parse_Val(data[index..bound], grammar[0]).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar[0]).0 == Some(vs[0]));
            assert narrow_val_tuple.0.v == vs[0] == bound_val_tuple.0.v;

            var new_index := index + SizeOfV(narrow_val_tuple.0.v);
            calc {
                SizeOfV(narrow_val_tuple.0.v) + SeqSum(vs[1..]);
                    { reveal_SeqSum(); }
                SeqSum(vs);
            }
            assert new_index+SeqSum(vs[1..]) <= bound;

            lemma_parse_Val_view_Tuple_contents(data, vs[1..], grammar[1..], new_index, bound);

            assert (parse_Tuple_contents(data[new_index..bound], grammar[1..]).0 == Some(vs[1..])) <==> (parse_Tuple_contents(data[new_index..new_index+SeqSum(vs[1..])], grammar[1..]).0 == Some(vs[1..]));
            assert data[new_index..new_index+SeqSum(vs[1..])] == narrow_val_tuple.1;
            assert data[new_index..bound] == bound_val_tuple.1;

            assert bound_tuple.0 == Some([vs[0]] + vs[1..]) == Some(vs);
        } else if bound_tuple.0 == Some(vs) {
            assert !bound_val_tuple.0.None? && !bound_contents_tuple.0.None?;

            lemma_SeqSum_bound(vs, |data| - index + 1);
            lemma_parse_Val_view(data, vs[0], grammar[0], index);
            // This is exactly the ensures of the lemma above
            assert forall bound' :: index+SizeOfV(vs[0]) <= bound' <= |data| ==>
                   ((parse_Val(data[index..bound'], grammar[0]).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar[0]).0 == Some(vs[0])));

            lemma_SeqSum_bound(vs, bound - index + 1);
            lemma_SeqSum_bound(vs, SeqSum(vs) + 1);
            assert index+SizeOfV(vs[0]) <= index+SeqSum(vs) <= |data|;
            assert (parse_Val(data[index..index+SeqSum(vs)], grammar[0]).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar[0]).0 == Some(vs[0]));
            assert (parse_Val(data[index..bound], grammar[0]).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar[0]).0 == Some(vs[0]));
            assert narrow_val_tuple.0.v == vs[0] == bound_val_tuple.0.v;

            var new_index := index + SizeOfV(narrow_val_tuple.0.v);
            calc {
                SizeOfV(narrow_val_tuple.0.v) + SeqSum(vs[1..]);
                    { reveal_SeqSum(); }
                SeqSum(vs);
            }
            assert new_index+SeqSum(vs[1..]) <= bound;

            lemma_parse_Val_view_Tuple_contents(data, vs[1..], grammar[1..], new_index, bound);

            assert (parse_Tuple_contents(data[new_index..bound], grammar[1..]).0 == Some(vs[1..])) <==> (parse_Tuple_contents(data[new_index..new_index+SeqSum(vs[1..])], grammar[1..]).0 == Some(vs[1..]));
            assert data[new_index..new_index+SeqSum(vs[1..])] == narrow_val_tuple.1;
            assert data[new_index..bound] == bound_val_tuple.1;

            assert narrow_tuple.0 == Some([vs[0]] + vs[1..]) == Some(vs);
        } else {
            // Doesn't matter for our ensures clause
        }
    }

}

lemma lemma_parse_Val_view_Tuple(data:seq<byte>, v:V, grammar:seq<G>, index:int, bound:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires v.VTuple?;
    requires |v.t| == |grammar|
    requires forall i :: 0 <= i < |v.t| ==> ValInGrammar(v.t[i], grammar[i]);
    requires |grammar| < 0x1_0000_0000_0000_0000;
    requires forall g :: g in grammar ==> ValidGrammar(g);
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    requires index+SizeOfV(v) <= bound <= |data|;
    decreases grammar, -1, v;
    ensures  (parse_Tuple(data[index..bound], grammar).0 == Some(v)) <==> (parse_Tuple(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
    ensures  parse_Tuple(data[index..bound], grammar).0 == Some(v) ==> parse_Tuple(data[index..bound], grammar).1 == data[index+SizeOfV(v)..bound];
{
    var bound_tuple := parse_Tuple(data[index..bound], grammar);
    var bound_contents := bound_tuple.0;
    var bound_rest := bound_tuple.1;
    var narrow_tuple := parse_Tuple(data[index..index+SizeOfV(v)], grammar);
    var narrow_contents := narrow_tuple.0;
    var narrow_rest := narrow_tuple.1;

    if parse_Tuple(data[index..bound], grammar).0 == Some(v) {
        assert !bound_contents.None?;
        lemma_parse_Val_view_Tuple_contents(data, v.t, grammar, index, bound);
        assert (parse_Tuple_contents(data[index..bound], grammar).0 == Some(v.t)) <==> (parse_Tuple_contents(data[index..index+SeqSum(v.t)], grammar).0 == Some(v.t)); // OBSERVE
    } else if parse_Tuple(data[index..index+SizeOfV(v)], grammar).0 == Some(v) {
        assert !narrow_contents.None?;
        lemma_parse_Val_view_Tuple_contents(data, v.t, grammar, index, bound);
        assert (parse_Tuple_contents(data[index..bound], grammar).0 == Some(v.t)) <==> (parse_Tuple_contents(data[index..index+SeqSum(v.t)], grammar).0 == Some(v.t)); // OBSERVE
    } else {
        // Don't care
    }
}

lemma lemma_parse_Val_view_Union(data:seq<byte>, v:V, grammar:G, index:int, bound:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires grammar.GTaggedUnion?;
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    requires index+SizeOfV(v) <= bound <= |data|;
    decreases grammar, -1;
    ensures  (parse_Case(data[index..bound], grammar.cases).0 == Some(v)) <==> (parse_Case(data[index..index+SizeOfV(v)], grammar.cases).0 == Some(v));
    ensures  parse_Case(data[index..bound], grammar.cases).0 == Some(v) ==> parse_Case(data[index..bound], grammar.cases).1 == data[index+SizeOfV(v)..bound];
{
    var narrow_tuple := parse_Case(data[index..index+SizeOfV(v)], grammar.cases);
    var bound_tuple := parse_Case(data[index..bound], grammar.cases);
    var narrow_caseID_tuple := parse_Uint64(data[index..index+SizeOfV(v)]);
    var bound_caseID_tuple := parse_Uint64(data[index..bound]);
    assert narrow_caseID_tuple.0.v == bound_caseID_tuple.0.v;

    if parse_Case(data[index..bound], grammar.cases).0 == Some(v) {
        var narrow_val_tuple := parse_Val(narrow_caseID_tuple.1, grammar.cases[narrow_caseID_tuple.0.v.u]);
        var bound_val_tuple := parse_Val(bound_caseID_tuple.1, grammar.cases[bound_caseID_tuple.0.v.u]);

        lemma_parse_Val_view(data, v.val, grammar.cases[narrow_caseID_tuple.0.v.u], index + 8);
        assert index+SizeOfV(v.val) <= bound <= |data|;
        assert (parse_Val(data[index+8..bound], grammar.cases[narrow_caseID_tuple.0.v.u]).0 == Some(v.val)) <==> (parse_Val(data[index+8..index+8+SizeOfV(v.val)], grammar.cases[narrow_caseID_tuple.0.v.u]).0 == Some(v.val));
    } else if parse_Case(data[index..index+SizeOfV(v)], grammar.cases).0 == Some(v) {
        var narrow_val_tuple := parse_Val(narrow_caseID_tuple.1, grammar.cases[narrow_caseID_tuple.0.v.u]);
        var bound_val_tuple := parse_Val(bound_caseID_tuple.1, grammar.cases[bound_caseID_tuple.0.v.u]);

        lemma_parse_Val_view(data, v.val, grammar.cases[narrow_caseID_tuple.0.v.u], index + 8);
        assert (parse_Val(data[index+8..bound], grammar.cases[narrow_caseID_tuple.0.v.u]).0 == Some(v.val)) <==> (parse_Val(data[index+8..index+8+SizeOfV(v.val)], grammar.cases[narrow_caseID_tuple.0.v.u]).0 == Some(v.val));
    } else {
        // Doesn't matter
    }
}

lemma lemma_parse_Val_view(data:seq<byte>, v:V, grammar:G, index:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    decreases grammar, 0;
    ensures  forall bound :: index+SizeOfV(v) <= bound <= |data| ==>
             ((parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v)));
    ensures  forall bound :: index+SizeOfV(v) <= bound <= |data| ==>
             (parse_Val(data[index..bound], grammar).0 == Some(v)) ==> parse_Val(data[index..bound], grammar).1 == data[index+SizeOfV(v)..bound];
{
    forall bound | index+SizeOfV(v) <= bound <= |data|
         ensures (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
         ensures (parse_Val(data[index..bound], grammar).0 == Some(v)) ==> parse_Val(data[index..bound], grammar).1 == data[index+SizeOfV(v)..bound];
    {
        reveal_parse_Val();
        match grammar
            case GUint64             => assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
            case GArray(elt)         => lemma_parse_Val_view_Array(data, v, grammar, index, bound);
                                        assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
            case GTuple(t)           => lemma_parse_Val_view_Tuple(data, v, t, index, bound); assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
            case GByteArray          => lemma_parse_Val_view_ByteArray(data, v, grammar, index); assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
            case GTaggedUnion(cases) => lemma_parse_Val_view_Union(data, v, grammar, index, bound); assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));

    }
}


lemma lemma_parse_Val_view_specific(data:seq<byte>, v:V, grammar:G, index:int, bound:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    requires index+SizeOfV(v) <= bound <= |data|; 
    requires parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v)
    decreases grammar, 0;
    ensures  parse_Val(data[index..bound], grammar).0 == Some(v);
    ensures  parse_Val(data[index..bound], grammar).1 == data[index+SizeOfV(v)..bound];
{
    lemma_parse_Val_view(data, v, grammar, index);
}

lemma lemma_parse_Val_view_specific_size(data:seq<byte>, v:V, grammar:G, index:int, bound:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    requires index+SizeOfV(v) <= bound <= |data|; 
    requires parse_Val(data[index..bound], grammar).0 == Some(v)
    decreases grammar, 0;
    ensures  parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v);
    ensures  parse_Val(data[index..bound], grammar).1 == data[index+SizeOfV(v)..bound];
{
    lemma_parse_Val_view(data, v, grammar, index);
}

method ComputeSeqSum(s:seq<V>) returns (size:uint64)
    requires |s| < 0x1_0000_0000_0000_0000;
    requires 0 <= SeqSum(s) < 0x1_0000_0000_0000_0000;
    requires forall v :: v in s ==> ValidVal(v);
    ensures int(size) == SeqSum(s);
{
    reveal_SeqSum();
    if uint64(|s|) == 0 {
        size := 0;
    } else {
        var v_size := ComputeSizeOf(s[uint64(0)]);
        var rest_size := ComputeSeqSum(s[uint64(1)..]);
        size := v_size + rest_size;
    }
}

method ComputeSizeOf(val:V) returns (size:uint64)
    requires 0 <= SizeOfV(val) < 0x1_0000_0000_0000_0000;
    requires ValidVal(val);
    ensures int(size) == SizeOfV(val);
{
    match val
        case VUint64(_)     => size := 8;
        case VArray(a)      => var v := ComputeSeqSum(a);
                               if v == 0 {
                                   size := 8;
                               } else {
                                   size := 8 + v;
                               }
        case VTuple(t)      => size := ComputeSeqSum(t);
        case VByteArray(b)  => size := 8 + uint64(|b|);
        case VCase(c, v)    => var vs := ComputeSizeOf(v);
                               size := 8 + vs;
}

method MarshallUint64(n:uint64, data:array<byte>, index:uint64)
    requires data != null;
    requires int(index) + int(Uint64Size()) <= data.Length;
    requires 0 <= int(index) + int(Uint64Size()) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    ensures  SeqByteToUint64(data[index..index+uint64(Uint64Size())]) == n;
    ensures  !parse_Uint64(data[index .. index+uint64(Uint64Size())]).0.None?;
    ensures  !parse_Uint64(data[index .. ]).0.None?;
    ensures  var tuple := parse_Uint64(data[index .. index+uint64(Uint64Size())]);
             tuple.0.v.u == n && tuple.1 == [];
    ensures  var tuple := parse_Uint64(data[index .. ]);
             tuple.0.v.u == n && tuple.1 == data[index+uint64(Uint64Size())..];
    ensures  data[0..index] == old(data[0..index]);
    ensures  data[index+uint64(Uint64Size())..] == old(data[index+uint64(Uint64Size())..]);
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: int(index) + int(Uint64Size()) <= i < data.Length ==> data[i] == old(data[i]);
{
    MarshallUint64_guts(n, data, index);
}

lemma lemma_marshall_array_contents(contents:seq<V>, eltType:G, marshalled_bytes:seq<byte>, trace:seq<seq<byte>>)
    requires forall v :: v in contents ==> ValInGrammar(v, eltType);
    requires forall v :: v in contents ==> ValidVal(v);
    requires ValidGrammar(eltType);
    requires |marshalled_bytes| < 0x1_0000_0000_0000_0000;
    requires |contents| < 0x1_0000_0000_0000_0000;
    requires |contents| == |trace|;
    requires |marshalled_bytes| == SeqSum(contents);
    requires marshalled_bytes == SeqCatRev(trace);
    requires forall j :: 0 <= j < |trace| ==> SizeOfV(contents[j]) == |trace[j]| < 0x1_0000_0000_0000_0000;
    requires forall j :: 0 <= j < |trace| ==> var (val, rest) := parse_Val(trace[j], eltType); val.Some? && val.v == contents[j]; 

    ensures  parse_Array_contents(marshalled_bytes, eltType, uint64(|contents|)).0.Some?;
    ensures  parse_Array_contents(marshalled_bytes, eltType, uint64(|contents|)).0.v == contents;
{
    if |contents| == 0 {
        reveal_parse_Array_contents();
    } else {
        var val_tuple := parse_Val(marshalled_bytes, eltType);
        var val, rest1 := val_tuple.0, val_tuple.1;
        var rest_tuple := parse_Array_contents(rest1, eltType, uint64(|contents|)-1);
        var others, rest2 := rest_tuple.0, rest_tuple.1;
        var target := parse_Array_contents(marshalled_bytes, eltType, uint64(|contents|)).0;
        calc {
            target;
                { reveal_parse_Array_contents(); }
            if !val.None? && !others.None? then Some([val.v] + others.v) else None;
        }

        calc {
            SeqCatRev(trace);
                { lemma_SeqCat_equivalent(trace); }
            SeqCat(trace);
        }

        assert marshalled_bytes[0..SizeOfV(contents[0])] == trace[0];
        assert parse_Val(trace[0], eltType).0.Some?;
        assert parse_Val(trace[0], eltType).0.v == contents[0];
        lemma_parse_Val_view_specific(marshalled_bytes, contents[0], eltType, 0, |marshalled_bytes|);
        assert parse_Val(marshalled_bytes[0..|marshalled_bytes|], eltType).0 == Some(contents[0]);
        assert marshalled_bytes[0..|marshalled_bytes|] == marshalled_bytes;     // OBSERVE
        assert val.Some? && val.v == contents[0];
        assert rest1 == marshalled_bytes[SizeOfV(contents[0])..];

        // Prove a requires for the recursive call
        calc {
            marshalled_bytes[SizeOfV(contents[0])..];
                calc {
                    marshalled_bytes;
                    SeqCatRev(trace);
                        { lemma_SeqCat_equivalent(trace); }
                    SeqCat(trace);
                    trace[0] + SeqCat(trace[1..]);
                        { lemma_SeqCat_equivalent(trace[1..]); }
                    trace[0] + SeqCatRev(trace[1..]);
                }
            (trace[0] + SeqCatRev(trace[1..]))[SizeOfV(contents[0])..];
                { assert |trace[0]| == SizeOfV(contents[0]); }
            SeqCatRev(trace[1..]);
        }

        // Prove a requires for the recursive call
        calc {
            SeqSum(contents);
                { reveal_SeqSum(); }
            SizeOfV(contents[0]) + SeqSum(contents[1..]);
        }
        lemma_marshall_array_contents(contents[1..], eltType, marshalled_bytes[SizeOfV(contents[0])..], trace[1..]);
        assert others.Some?;
        assert others.v == contents[1..];
        assert contents == [contents[0]] + contents[1..];
       
    }
}

method{:timeLimitMultiplier 4} MarshallArrayContents(contents:seq<V>, eltType:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires data != null;
    requires forall v :: v in contents ==> ValInGrammar(v, eltType);
    requires forall v :: v in contents ==> ValidVal(v);
    requires ValidGrammar(eltType);
    requires int(index) + SeqSum(contents) <= data.Length;
    requires 0 <= int(index) + SeqSum(contents) < 0x1_0000_0000_0000_0000;
    requires data.Length < 0x1_0000_0000_0000_0000;
    requires |contents| < 0x1_0000_0000_0000_0000;
    decreases eltType, 1, |contents|;
    modifies data;
    ensures  parse_Array_contents(data[index..int(index) + SeqSum(contents)], eltType, uint64(|contents|)).0.Some?;
    ensures  parse_Array_contents(data[index..int(index) + SeqSum(contents)], eltType, uint64(|contents|)).0.v == contents;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: int(index) + SeqSum(contents) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  int(size) == SeqSum(contents);
{
    var i:uint64 := 0;
    var cur_index := index;
    reveal_SeqSum();
    reveal_parse_Array_contents();

    ghost var trace := [];
    ghost var marshalled_bytes := [];

    while i < uint64(|contents|)
        invariant 0 <= int(i) <= |contents|;
        invariant 0 <= int(index) <= int(index) + SeqSum(contents[..i]) <= data.Length;
        invariant int(cur_index) == int(index) + SeqSum(contents[..i]);
        invariant forall j :: 0 <= j < index ==> data[j] == old(data[j]);
        invariant forall j :: int(index) + SeqSum(contents) <= j < data.Length ==> data[j] == old(data[j]);
        invariant marshalled_bytes == data[index..cur_index];
        invariant marshalled_bytes == SeqCatRev(trace);
        invariant |trace| == int(i);
        invariant forall j :: 0 <= j < |trace| ==> SizeOfV(contents[j]) == |trace[j]| < 0x1_0000_0000_0000_0000;
        invariant forall j :: 0 <= j < |trace| ==> 
                        var (val, rest) := parse_Val(trace[j], eltType); 
                        val.Some? && val.v == contents[j]; 
    {
        lemma_SeqSum_bound(contents, 0x1_0000_0000_0000_0000);

        // Prove we meet MarshallVal's length requirement
        calc <= {
            int(cur_index) + SizeOfV(contents[i]);
            int(index) + SeqSum(contents[..i]) + SizeOfV(contents[i]);
                { lemma_SeqSum_prefix(contents[..i], contents[i]); 
                  assert contents[..i] + [contents[i]] == contents[..i+1]; }
            int(index) + SeqSum(contents[..i+1]);
                { lemma_SeqSum_bound_prefix(contents, contents[..i+1], int(i)+1); }
                //{ lemma_SeqSum_bound(contents, data.Length - int(index) + 1); }
            int(index) + SeqSum(contents);
            //data.Length;
        }
        var item_size := MarshallVal(contents[i], eltType, data, cur_index);
        //var item_size := ComputeSizeOf(contents[uint64(i)]);

        ghost var fresh_bytes := data[cur_index..cur_index + item_size];
        marshalled_bytes := marshalled_bytes + fresh_bytes;
        forall () 
            ensures var (val, rest) := parse_Val(fresh_bytes, eltType);
                    val.Some? && val.v == contents[i];
        {
            assert SizeOfV(contents[i]) <= |fresh_bytes|;  // OBSERVE
            lemma_parse_Val_view(fresh_bytes, contents[i], eltType, 0);
        }

        ghost var old_trace := trace;
        trace := trace + [fresh_bytes];

        ghost var old_cur_index := cur_index;
        cur_index := cur_index + item_size;
        i := i + 1;

        // Prove the invariant that we stay within bounds
        calc <= {
            int(index) + SeqSum(contents[..i]);
            calc {
                SeqSum(contents[..i]);
                <=  { lemma_SeqSum_bound_prefix(contents, contents[..i], int(i)); }
                SeqSum(contents);
            }
            int(index) + SeqSum(contents);
            data.Length;
        }
        assert {:split_here} true;
        assert marshalled_bytes == data[index..cur_index];

        // Prove the invariant about our index tracking correctly
        calc {
            int(cur_index);
            int(old_cur_index) + SizeOfV(contents[i-1]);
            int(index) + SeqSum(contents[..i-1]) + SizeOfV(contents[i-1]);
                { lemma_SeqSum_prefix(contents[..i-1], contents[i-1]); 
                  assert contents[..i-1] + [contents[i-1]] == contents[..i]; }
            int(index) + SeqSum(contents[..i]);
        }
        assert int(cur_index) == int(index) + SeqSum(contents[..i]);
        assert marshalled_bytes == data[index..cur_index];
    }

    // Prove that parsing will produce the correct result

    // After the while loop, we know:
    assert contents[..i] == contents;   // OBSERVE
    assert int(cur_index) == int(index) + SeqSum(contents);
    assert marshalled_bytes == data[index..int(index)+SeqSum(contents)];
    //assert marshalled_bytes == SeqCatRev(trace);
    //assert |trace| == |contents|;
    lemma_marshall_array_contents(contents, eltType, marshalled_bytes, trace);
    size := cur_index - index;
}

method MarshallArray(val:V, grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires data != null;
    requires val.VArray?;
    requires ValInGrammar(val, grammar);
    requires ValidGrammar(grammar);
    requires ValidVal(val);
    requires int(index) + SizeOfV(val) <= data.Length;
    requires 0 <= int(index) + SizeOfV(val) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    decreases grammar, -1;
    ensures  parse_Val(data[index..int(index) + SizeOfV(val)], grammar).0.Some? &&
             parse_Val(data[index..int(index) + SizeOfV(val)], grammar).0.v == val;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: int(index) + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  int(size) == SizeOfV(val);
{
    //assert{:split_here} true;
    reveal_parse_Val();
    MarshallUint64(uint64(|val.a|), data, index);

    ghost var tuple := parse_Uint64(data[index..int(index) + SizeOfV(val)]);
    ghost var len := tuple.0;
    ghost var rest := tuple.1;
    assert !len.None?;
    var contents_size := MarshallArrayContents(val.a, grammar.elt, data, index + Uint64Size());
    tuple := parse_Uint64(data[index..int(index) + SizeOfV(val)]);
    assert {:split_here} true;
    len := tuple.0;
    rest := tuple.1;
    assert !len.None?;
    ghost var contents_tuple := parse_Array_contents(rest, grammar.elt, len.v.u);
    ghost var contents  := contents_tuple.0;
    ghost var remainder := contents_tuple.1;
    assert !contents.None?;
    size := 8 + contents_size;
}

lemma lemma_marshall_tuple_contents(contents:seq<V>, eltTypes:seq<G>, marshalled_bytes:seq<byte>, trace:seq<seq<byte>>)
    requires |contents| == |eltTypes|;
    requires forall i :: 0 <= i < |contents| ==> ValInGrammar(contents[i], eltTypes[i]);
    requires forall g :: g in eltTypes ==> ValidGrammar(g);
    requires |eltTypes| < 0x1_0000_0000_0000_0000;
    requires forall i :: 0 <= i < |contents| ==> ValidVal(contents[i]);
    requires |marshalled_bytes| < 0x1_0000_0000_0000_0000;
    requires |contents| < 0x1_0000_0000_0000_0000;
    requires |contents| == |trace|;
    requires |marshalled_bytes| == SeqSum(contents);
    requires marshalled_bytes == SeqCatRev(trace);
    requires forall j :: 0 <= j < |trace| ==> SizeOfV(contents[j]) == |trace[j]| < 0x1_0000_0000_0000_0000;
    requires forall j :: 0 <= j < |trace| ==> var (val, rest) := parse_Val(trace[j], eltTypes[j]); val.Some? && val.v == contents[j]; 

    ensures  parse_Tuple_contents(marshalled_bytes, eltTypes).0.Some?;
    ensures  parse_Tuple_contents(marshalled_bytes, eltTypes).0.v == contents;
{
    if |contents| == 0 {
        reveal_parse_Tuple_contents();
    } else {
        var val_tuple := parse_Val(marshalled_bytes, eltTypes[0]);
        var val, rest1 := val_tuple.0, val_tuple.1;
        var rest_tuple := parse_Tuple_contents(rest1, eltTypes[1..]);
        var others, rest2 := rest_tuple.0, rest_tuple.1;
        var target := parse_Tuple_contents(marshalled_bytes, eltTypes).0;
        calc {
            target;
                { reveal_parse_Tuple_contents(); }
            if !val.None? && !others.None? then Some([val.v] + others.v) else None;
        }

        calc {
            SeqCatRev(trace);
                { lemma_SeqCat_equivalent(trace); }
            SeqCat(trace);
        }

        assert marshalled_bytes[0..SizeOfV(contents[0])] == trace[0];
        assert parse_Val(trace[0], eltTypes[0]).0.Some?;
        assert parse_Val(trace[0], eltTypes[0]).0.v == contents[0];
        lemma_parse_Val_view_specific(marshalled_bytes, contents[0], eltTypes[0], 0, |marshalled_bytes|);
        assert parse_Val(marshalled_bytes[0..|marshalled_bytes|], eltTypes[0]).0 == Some(contents[0]);
        assert marshalled_bytes[0..|marshalled_bytes|] == marshalled_bytes;     // OBSERVE
        assert val.Some? && val.v == contents[0];
        assert rest1 == marshalled_bytes[SizeOfV(contents[0])..];

        // Prove a requires for the recursive call
        calc {
            marshalled_bytes[SizeOfV(contents[0])..];
                calc {
                    marshalled_bytes;
                    SeqCatRev(trace);
                        { lemma_SeqCat_equivalent(trace); }
                    SeqCat(trace);
                    trace[0] + SeqCat(trace[1..]);
                        { lemma_SeqCat_equivalent(trace[1..]); }
                    trace[0] + SeqCatRev(trace[1..]);
                }
            (trace[0] + SeqCatRev(trace[1..]))[SizeOfV(contents[0])..];
                { assert |trace[0]| == SizeOfV(contents[0]); }
            SeqCatRev(trace[1..]);
        }

        // Prove a requires for the recursive call
        calc {
            SeqSum(contents);
                { reveal_SeqSum(); }
            SizeOfV(contents[0]) + SeqSum(contents[1..]);
        }
        lemma_marshall_tuple_contents(contents[1..], eltTypes[1..], marshalled_bytes[SizeOfV(contents[0])..], trace[1..]);
        assert others.Some?;
        assert others.v == contents[1..];
        assert contents == [contents[0]] + contents[1..];
       
    }
}

method{:timeLimitMultiplier 2} MarshallTupleContents(contents:seq<V>, eltTypes:seq<G>, data:array<byte>, index:uint64) returns (size:uint64)
    requires data != null;
    requires |contents| == |eltTypes|;
    requires forall i :: 0 <= i < |contents| ==> ValInGrammar(contents[i], eltTypes[i]);
    requires forall g :: g in eltTypes ==> ValidGrammar(g);
    requires |eltTypes| < 0x1_0000_0000_0000_0000;
    requires forall i :: 0 <= i < |contents| ==> ValidVal(contents[i]);
    requires int(index) + SeqSum(contents) <= data.Length;
    requires 0 <= int(index) + SeqSum(contents) < 0x1_0000_0000_0000_0000;
    requires data.Length < 0x1_0000_0000_0000_0000;
    requires |contents| < 0x1_0000_0000_0000_0000;
    decreases eltTypes, 1, |contents|;
    modifies data;
    ensures  parse_Tuple_contents(data[index..int(index) + SeqSum(contents)], eltTypes).0.Some?;
    ensures  parse_Tuple_contents(data[index..int(index) + SeqSum(contents)], eltTypes).0.v == contents;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: int(index) + SeqSum(contents) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  int(size) == SeqSum(contents);
{
    var i:uint64 := 0;
    var cur_index := index;
    reveal_SeqSum();
    reveal_parse_Tuple_contents();

    ghost var trace := [];
    ghost var marshalled_bytes := [];

    while i < uint64(|contents|)
        invariant 0 <= int(i) <= |contents|;
        invariant 0 <= int(index) <= int(index) + SeqSum(contents[..i]) <= data.Length;
        invariant int(cur_index) == int(index) + SeqSum(contents[..i]);
        invariant forall j :: 0 <= j < index ==> data[j] == old(data[j]);
        invariant forall j :: int(index) + SeqSum(contents) <= j < data.Length ==> data[j] == old(data[j]);
        invariant marshalled_bytes == data[index..cur_index];
        invariant marshalled_bytes == SeqCatRev(trace);
        invariant |trace| == int(i);
        invariant forall j :: 0 <= j < |trace| ==> SizeOfV(contents[j]) == |trace[j]| < 0x1_0000_0000_0000_0000;
        invariant forall j :: 0 <= j < |trace| ==> 
                        var (val, rest) := parse_Val(trace[j], eltTypes[j]); 
                        val.Some? && val.v == contents[j]; 
    {
        lemma_SeqSum_bound(contents, 0x1_0000_0000_0000_0000);
        ghost var old_marshalled_bytes := marshalled_bytes;
        ghost var old_data := data[index..cur_index];
        assert old_marshalled_bytes == old_data;

        // Prove we meet MarshallVal's length requirement
        calc <= {
            int(cur_index) + SizeOfV(contents[i]);
            int(index) + SeqSum(contents[..i]) + SizeOfV(contents[i]);
                { lemma_SeqSum_prefix(contents[..i], contents[i]); 
                  assert contents[..i] + [contents[i]] == contents[..i+1]; }
            int(index) + SeqSum(contents[..i+1]);
                { lemma_SeqSum_bound_prefix(contents, contents[..i+1], int(i)+1); }
                //{ lemma_SeqSum_bound(contents, data.Length - int(index) + 1); }
            int(index) + SeqSum(contents);
            //data.Length;
        }
        var item_size := MarshallVal(contents[i], eltTypes[i], data, cur_index);
        //var item_size := ComputeSizeOf(contents[uint64(i)]);

        ghost var fresh_bytes := data[cur_index..cur_index + item_size];
        marshalled_bytes := marshalled_bytes + fresh_bytes;
        forall () 
            ensures var (val, rest) := parse_Val(fresh_bytes, eltTypes[i]);
                    val.Some? && val.v == contents[i];
        {
            assert SizeOfV(contents[i]) <= |fresh_bytes|;  // OBSERVE
            lemma_parse_Val_view(fresh_bytes, contents[i], eltTypes[i], 0);
        }

        ghost var old_trace := trace;
        trace := trace + [fresh_bytes];

        ghost var old_cur_index := cur_index;
        cur_index := cur_index + item_size;
        i := i + 1;
        
        assert {:split_here} true;

        // Prove the invariant about marshalled_bytes' contents
        calc {
            marshalled_bytes;
            old_marshalled_bytes + fresh_bytes;
            old_data + fresh_bytes;
            data[index..old_cur_index] + fresh_bytes;
            data[index..old_cur_index] + data[old_cur_index..cur_index];
            data[index..cur_index];
        }

        // Prove the invariant that we stay within bounds
        calc <= {
            int(index) + SeqSum(contents[..i]);
            calc {
                SeqSum(contents[..i]);
                <=  { lemma_SeqSum_bound_prefix(contents, contents[..i], int(i)); }
                SeqSum(contents);
            }
            int(index) + SeqSum(contents);
            data.Length;
        }

        // Prove the invariant about our index tracking correctly
        calc {
            int(cur_index);
            int(old_cur_index) + SizeOfV(contents[i-1]);
            int(index) + SeqSum(contents[..i-1]) + SizeOfV(contents[i-1]);
                { lemma_SeqSum_prefix(contents[..i-1], contents[i-1]); 
                  assert contents[..i-1] + [contents[i-1]] == contents[..i]; }
            int(index) + SeqSum(contents[..i]);
        }
        assert int(cur_index) == int(index) + SeqSum(contents[..i]);
    }

    // Prove that parsing will produce the correct result

    // After the while loop, we know:
    assert contents[..i] == contents;   // OBSERVE
    assert int(cur_index) == int(index) + SeqSum(contents);
    assert marshalled_bytes == data[index..int(index)+SeqSum(contents)];
    //assert marshalled_bytes == SeqCatRev(trace);
    //assert |trace| == |contents|;
    lemma_marshall_tuple_contents(contents, eltTypes, marshalled_bytes, trace);
    size := cur_index - index;
}

method MarshallTuple(val:V, grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires data != null;
    requires val.VTuple?;
    requires ValidVal(val);
    requires ValidGrammar(grammar);
    requires ValInGrammar(val, grammar);
    requires int(index) + SizeOfV(val) <= data.Length;
    requires 0 <= int(index) + SizeOfV(val) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    decreases grammar, -1;
    ensures  parse_Val(data[index..int(index) + SizeOfV(val)], grammar).0.Some? &&
             parse_Val(data[index..int(index) + SizeOfV(val)], grammar).0.v == val;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: int(index) + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  int(size) == SizeOfV(val);
{
    size := MarshallTupleContents(val.t, grammar.t, data, index);

    calc {
        parse_Val(data[index..int(index) + SizeOfV(val)], grammar);
            { reveal_parse_Val(); }
        parse_Tuple(data[index..int(index) + SizeOfV(val)], grammar.t);
    }
}

method MarshallBytes(bytes:seq<byte>, data:array<byte>, index:uint64)
    requires data != null;
    requires int(index) + |bytes| <= data.Length;
    requires 0 <= int(index) + |bytes| < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: int(index) <= i < int(index) + |bytes| ==> data[i] == bytes[i - int(index)];
    ensures  forall i :: int(index) + |bytes| <= i < data.Length ==> data[i] == old(data[i]);
{
    Arrays.CopySeqIntoArray(bytes, 0, data, index, uint64(|bytes|));

    /*
    var j:uint64 := 0;

    while (j < uint64(|bytes|))
        invariant 0 <= int(j) <= |bytes|;
        invariant forall i:int :: 0 <= i < int(index) ==> data[i] == old(data[i]);
        invariant forall i:int :: int(index) <= i < int(index) + int(j) ==> data[i] == bytes[i-int(index)];
        invariant forall i:int :: int(index) + |bytes| <= i < data.Length ==> data[i] == old(data[i]);
    {
        data[index + j] := bytes[j];
        j := j + 1;
    }
    */
}

method MarshallByteArray(val:V, grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires data != null;
    requires val.VByteArray?;
    requires ValidGrammar(grammar);
    requires ValInGrammar(val, grammar);
    requires ValidVal(val);
    requires int(index) + SizeOfV(val) <= data.Length;
    requires 0 <= int(index) + SizeOfV(val) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    decreases grammar;
    ensures  parse_Val(data[index..int(index) + SizeOfV(val)], grammar).0.Some? &&
             parse_Val(data[index..int(index) + SizeOfV(val)], grammar).0.v == val;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: int(index) + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  int(size) == SizeOfV(val);
{
    MarshallUint64(uint64(|val.b|), data, index);
    assert SeqByteToUint64(data[index..index+uint64(Uint64Size())]) == uint64(|val.b|);
    MarshallBytes(val.b, data, index + 8);

    calc {
        parse_Val(data[index..int(index) + SizeOfV(val)], grammar);
            { reveal_parse_Val(); }
        parse_ByteArray(data[index..int(index) + SizeOfV(val)]);
    }
    ghost var data_seq := data[index..int(index) + SizeOfV(val)];
    ghost var tuple := parse_Uint64(data_seq);
    ghost var len := tuple.0;
    ghost var rest := tuple.1;
    assert{:split_here} true;assert len.v.u == uint64(|val.b|);
    
    assert rest == data[index + 8..int(index) + SizeOfV(val)] == val.b;
    assert !len.None? && int(len.v.u) <= |rest|;
    assert rest[0..len.v.u] == val.b;       // OBSERVE
    size := 8 + uint64(|val.b|);
}

method MarshallCase(val:V, grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires data != null;
    requires val.VCase?;
    requires ValidGrammar(grammar);
    requires ValInGrammar(val, grammar);
    requires ValidVal(val);
    requires int(index) + SizeOfV(val) <= data.Length;
    requires 0 <= int(index) + SizeOfV(val) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    decreases grammar, -1;
    ensures  parse_Val(data[index..int(index) + SizeOfV(val)], grammar).0.Some? &&
             parse_Val(data[index..int(index) + SizeOfV(val)], grammar).0.v == val;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: int(index) + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  int(size) == SizeOfV(val);
{
    MarshallUint64(val.c, data, index);
    ghost var int_bytes := data[index..index+Uint64Size()];
    ghost var tuple0 := parse_Uint64(int_bytes);
    ghost var caseID0 := tuple0.0;
    ghost var rest10   := tuple0.1;
    assert !caseID0.None?;
    assert caseID0.v.u == val.c;

    var val_size := MarshallVal(val.val, grammar.cases[val.c], data, index + 8);

    ghost var new_int_bytes := data[index..index+Uint64Size()];
    assert forall i {:auto_trigger} :: 0 <= i < Uint64Size() ==> int_bytes[i] == new_int_bytes[i];
    assert int_bytes == new_int_bytes;

    assert val.VCase?; 
    assert grammar.GTaggedUnion?; 
    assert int(val.c) < |grammar.cases|;

    ghost var bytes := data[index..int(index) + SizeOfV(val)];
    assert bytes[..8] == new_int_bytes;
    calc {
        parse_Val(bytes, grammar);
            { reveal_parse_Val(); }
        parse_Case(bytes, grammar.cases);
    }

    assert{:split_here} true;
    ghost var tuple1 := parse_Uint64(bytes);
    ghost var caseID := tuple1.0;
    ghost var rest1   := tuple1.1;

    assert !caseID.None?;
    assert caseID.v.u == val.c;
    assert int(caseID.v.u) < |grammar.cases|;
    ghost var tuple2 := parse_Val(rest1, grammar.cases[caseID.v.u]);
    ghost var v:= tuple2.0;
    ghost var rest2 := tuple2.1;
    assert !v.None?;

    size := 8 + val_size;
}

method MarshallVUint64(val:V, grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires data != null;
    requires val.VUint64?;
    requires ValidGrammar(grammar);
    requires ValInGrammar(val, grammar);
    requires int(index) + SizeOfV(val) <= data.Length;
    requires 0 <= int(index) + SizeOfV(val) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    decreases grammar;
    ensures  parse_Val(data[index..int(index) + SizeOfV(val)], grammar).0.Some? &&
             parse_Val(data[index..int(index) + SizeOfV(val)], grammar).0.v == val;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: int(index) + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  int(size) == SizeOfV(val);
{
    MarshallUint64(val.u, data, index);
    calc {
        parse_Val(data[index..int(index) + SizeOfV(val)], grammar);
            { reveal_parse_Val(); }
        parse_Uint64(data[index..int(index) + SizeOfV(val)]);
    }
    return 8;
}

method MarshallVal(val:V, grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires ValidGrammar(grammar);
    requires ValInGrammar(val, grammar);
    requires ValidVal(val);
    requires 0 <= SizeOfV(val) < 0x1_0000_0000_0000_0000;
    requires data!=null;
    requires int(index) + SizeOfV(val) <= data.Length;
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    decreases grammar, 0;
    ensures  parse_Val(data[index..int(index) + SizeOfV(val)], grammar).0.Some? &&
             parse_Val(data[index..int(index) + SizeOfV(val)], grammar).0.v == val;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: int(index) + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  int(size) == SizeOfV(val);
{
    match val
        case VUint64(_)    => size := MarshallVUint64(val, grammar, data, index);
        case VArray(_)     => size := MarshallArray(val, grammar, data, index);
        case VTuple(_)     => size := MarshallTuple(val, grammar, data, index);
        case VByteArray(_) => size := MarshallByteArray(val, grammar, data, index);
        case VCase(_,_)    => size := MarshallCase(val, grammar, data, index);
}

method Marshall(val:V, grammar:G) returns (data:array<byte>)
    requires ValidGrammar(grammar);
    requires ValInGrammar(val, grammar);
    requires ValidVal(val);
    requires 0 <= SizeOfV(val) < 0x1_0000_0000_0000_0000;
    ensures data!=null;
    ensures fresh(data);
    ensures Demarshallable(data[..], grammar);
    ensures parse_Val(data[..], grammar).0.Some? && parse_Val(data[..], grammar).0.v == val;
    ensures parse_Val(data[..], grammar).1 == [];
    ensures |data[..]| == SizeOfV(val);
{
    var size := ComputeSizeOf(val);
    data := new byte[size];

    var computed_size := MarshallVal(val, grammar, data, 0);

    assert data[0..0 + SizeOfV(val)] == data[0..0 + size] == data[..];      // OBSERVE

    lemma_parse_Val_view_specific(data[..], val, grammar, 0, int(size));
}
} 
