include "../../Drivers/CPU/assembly.s.dfy"
include "Database.s.dfy"

//-/////////////////////////////////////////
//- Binary instructions
//-/////////////////////////////////////////

datatype BinaryInstruction = InstAdd | InstSub | InstMul | InstDiv | InstMod | InstGt | InstLt | InstEq | InstGe | InstLe

static function method BooleanToInt(b:bool):int
{
    if b then 1 else 0
}

static function{:opaque} Mod0x100000000(i:int):int { i % 0x100000000 }

static function{:opaque} ApplyBinaryInstruction(inst:BinaryInstruction, v1:int, v2:int):int
{
    match inst
        case InstAdd => Mod0x100000000(v1 + v2)
        case InstSub => Mod0x100000000(v1 - v2)
        case InstMul => Mod0x100000000(v1 * v2)
        case InstDiv => if v2 == 0 then 0 else Mod0x100000000(v1 / v2)
        case InstMod => if v2 == 0 then 0 else Mod0x100000000(v1 % v2)
        case InstGt => BooleanToInt(v1 > v2)
        case InstLt => BooleanToInt(v1 < v2)
        case InstEq => BooleanToInt(v1 == v2)
        case InstGe => BooleanToInt(v1 >= v2)
        case InstLe => BooleanToInt(v1 <= v2)
}

//-/////////////////////////////////////////
//- Expressions
//-/////////////////////////////////////////

datatype Expression = ExpInt(i:int)
                    | ExpColumn(col:Expression)
                    | ExpBinary(inst:BinaryInstruction, e1:Expression, e2:Expression)
                    | ExpIf(e_cond:Expression, e_true:Expression, e_false:Expression)

static predicate ExpressionValid(e:Expression)
{
    match e
        case ExpInt(i) => Word32(i)
        case ExpColumn(e1) => ExpressionValid(e1)
        case ExpBinary(inst, e1, e2) => ExpressionValid(e1) && ExpressionValid(e2)
        case ExpIf(e1, e2, e3) => ExpressionValid(e1) && ExpressionValid(e2) && ExpressionValid(e3)
}

static predicate ExpressionStackContainsOnlyWords(estack:seq<Expression>)
{
    forall i:int :: 0 <= i < |estack| ==> ExpressionValid(estack[i])
}

static function EvaluateExpression(e:Expression, row:Row):int
{
    match e
        case ExpInt(i) => i
        case ExpColumn(e1) => ExtractColumn(EvaluateExpression(e1, row), row)
        case ExpBinary(inst, e1, e2) => ApplyBinaryInstruction(inst, EvaluateExpression(e1, row), EvaluateExpression(e2, row))
        case ExpIf(e_cond, e_true, e_false) =>
            if EvaluateExpression(e_cond, row) != 0 then EvaluateExpression(e_true, row) else EvaluateExpression(e_false, row)
}

//-/////////////////////////////////////////
//- Operations
//-/////////////////////////////////////////

static function method ExtractColumn(column_index:int, row:Row):int
{
    if 0 <= column_index < |row.data| then row.data[column_index] else 0
}

datatype Operation = OperationPush(i:int)
                   | OperationColumn
                   | OperationBinary(inst:BinaryInstruction)
                   | OperationIf

static predicate OperationValid(op:Operation)
{
    if op.OperationPush? then Word32(op.i) else true
}

static function method StackSizeChangeFromOperation(t:Operation):int
{
    match t
        case OperationPush(_) => 1
        case OperationColumn => 0
        case OperationBinary(_) => -1
        case OperationIf => -2
}

///////////////////////////////////////////

///////////////////////////////////////////

static predicate ProgramContainsOnlyWords(program:seq<Operation>)
{
    forall k :: 0 <= k < |program| ==> OperationValid(program[k])
}

///////////////////////////////////////////

///////////////////////////////////////////

static function HowOperationChangesExpressionStack(op:Operation, estack:seq<Expression>):seq<Expression>
{
    match op
        case OperationPush(i) =>       estack + [ExpInt(i)]
        case OperationColumn =>        if |estack| >= 1 then estack[..|estack|-1] + [ExpColumn(estack[|estack|-1])] else []
        case OperationBinary(inst) =>  if |estack| >= 2 then estack[..|estack|-2] + [ExpBinary(inst, estack[|estack| - 2], estack[|estack| - 1])] else []
        case OperationIf =>            if |estack| >= 3 then estack[..|estack|-3] + [ExpIf(estack[|estack|-3], estack[|estack| - 2], estack[|estack| - 1])] else []
}

static function StackSizeAfterRunning(program:seq<Operation>):int
{
    if |program| == 0 then 0
    else StackSizeAfterRunning(program[..|program| - 1]) + StackSizeChangeFromOperation(program[|program| - 1])
}

static predicate ProgramPrefixValid(program:seq<Operation>)
{
    ProgramContainsOnlyWords(program) &&
    forall k :: 1 <= k <= |program| ==> StackSizeAfterRunning(program[..k]) >= 1
}

static predicate ProgramValid(program:seq<Operation>)
{
    ProgramPrefixValid(program) && StackSizeAfterRunning(program) == 1
}

static function {:opaque} ProgramPrefixToExpressionStack(program:seq<Operation>):seq<Expression>
{
    if |program| == 0 then
        []
    else
        HowOperationChangesExpressionStack(program[|program|-1], ProgramPrefixToExpressionStack(program[..|program|-1]))
}

static function ProgramToExpression(program:seq<Operation>):Expression
{
    var estack := ProgramPrefixToExpressionStack(program);
    if |estack| == 1 then estack[0] else ExpInt(0)
}

static function EvaluateProgram(program:seq<Operation>, row:Row):int
{
    EvaluateExpression(ProgramToExpression(program), row)
}

///////////////////////////////////////////

///////////////////////////////////////////

static function method WordToOperation(w:int):Operation
    requires Word32(w);
{
       if w == 2000000001 then OperationColumn
    else if w == 2000000002 then OperationIf
    else if w == 2000000003 then OperationBinary(InstAdd)
    else if w == 2000000004 then OperationBinary(InstSub)
    else if w == 2000000005 then OperationBinary(InstMul)
    else if w == 2000000006 then OperationBinary(InstDiv)
    else if w == 2000000007 then OperationBinary(InstMod)
    else if w == 2000000008 then OperationBinary(InstGt)
    else if w == 2000000009 then OperationBinary(InstLt)
    else if w == 2000000010 then OperationBinary(InstEq)
    else if w == 2000000011 then OperationBinary(InstGe)
    else if w == 2000000012 then OperationBinary(InstLe)
    else OperationPush(w)
}

static function MessageToProgram(message:seq<int>):seq<Operation>
    requires IsWordSeq(message);
{
    if |message| == 0 then [] else MessageToProgram(message[..|message|-1]) + [WordToOperation(message[|message|-1])]
}
