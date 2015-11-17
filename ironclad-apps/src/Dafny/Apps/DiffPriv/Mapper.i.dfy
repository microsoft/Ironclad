include "../../Libraries/Math/power2.i.dfy"
include "../../Drivers/CPU/assembly_premium.i.dfy"
include "Mapper.s.dfy"

static function method{:CompiledSpec} CompiledSpec_BooleanToInt(b:bool):int
static function method{:CompiledSpec} CompiledSpec_ExtractColumn(column_index:int, row:Row):int
//-static function method{:CompiledSpec} CompiledSpec_StackSizeChangeFromOperation(t:Operation):int
static function method{:CompiledSpec} CompiledSpec_WordToOperation(w:int):Operation

//-///////////////////////////////////////////////////
//- Premium versions of spec functions
//-///////////////////////////////////////////////////

static lemma Lemma_BooleanToInt_IsWord32(b:bool)
    ensures Word32(BooleanToInt(b));
{
    lemma_2toX();
}

static lemma Lemma_ApplyBinaryInstructionProducesWords(inst:BinaryInstruction, v1:int, v2:int)
    requires Word32(v1);
    requires Word32(v2);
    ensures Word32(ApplyBinaryInstruction(inst, v1, v2));
{
    lemma_2toX();
    reveal_Mod0x100000000();
    reveal_ApplyBinaryInstruction();

    if inst.InstAdd? {
        lemma_mod0x100000000(v1+v2);
    } else if inst.InstSub? {
        lemma_mod0x100000000(v1-v2);
    } else if inst.InstMul? {
        lemma_mod0x100000000(v1 * v2);
    } else if inst.InstDiv? {
        if (v2 != 0) {
            lemma_mod0x100000000(v1 / v2);
        }
    } else if inst.InstMod? {
        if (v2 != 0) {
            lemma_mod0x100000000(v1 % v2);
        }
    } else if inst.InstGt? {
        Lemma_BooleanToInt_IsWord32(v1 > v2);
    } else if inst.InstLt? {
        Lemma_BooleanToInt_IsWord32(v1 < v2);
    } else if inst.InstEq? {
        Lemma_BooleanToInt_IsWord32(v1 == v2);
    } else if inst.InstGe? {
        Lemma_BooleanToInt_IsWord32(v1 >= v2);
    } else if inst.InstLe? {
        Lemma_BooleanToInt_IsWord32(v1 <= v2);
    }
}

static method ApplyBinaryInstructionImpl(inst:BinaryInstruction, v1:int, v2:int) returns (result:int)
    requires Word32(v1);
    requires Word32(v2);
    ensures result == ApplyBinaryInstruction(inst, v1, v2);
    ensures Word32(result);
{
    lemma_2toX();
    reveal_Mod0x100000000();
    reveal_ApplyBinaryInstruction();

    if inst.InstAdd? {
        lemma_mod0x100000000(v1+v2);
        result := Asm_Add(v1, v2);
    } else if inst.InstSub? {
        lemma_mod0x100000000(v1-v2);
        result := Asm_Sub(v1, v2);
    } else if inst.InstMul? {
        lemma_mod0x100000000(v1 * v2);
        result := Asm_Mul(v1, v2);
    } else if inst.InstDiv? {
        if (v2 == 0) {
            result := 0;
        } else {
            lemma_mod0x100000000(v1 / v2);
            result := Asm_Div(v1, v2);
        }
    } else if inst.InstMod? {
        if (v2 == 0) {
            result := 0;
        } else {
            lemma_mod0x100000000(v1 % v2);
            result := Asm_Mod(v1, v2);
        }
    } else if inst.InstGt? {
        Lemma_BooleanToInt_IsWord32(v1 > v2);
        result := BooleanToInt(v1 > v2);
    } else if inst.InstLt? {
        Lemma_BooleanToInt_IsWord32(v1 < v2);
        result := BooleanToInt(v1 < v2);
    } else if inst.InstEq? {
        Lemma_BooleanToInt_IsWord32(v1 == v2);
        result := BooleanToInt(v1 == v2);
    } else if inst.InstGe? {
        Lemma_BooleanToInt_IsWord32(v1 >= v2);
        result := BooleanToInt(v1 >= v2);
    } else { assert inst.InstLe?;
        Lemma_BooleanToInt_IsWord32(v1 <= v2);
        result := BooleanToInt(v1 <= v2);
    }
}

static function HowOperationChangesExpressionStackWhenValid(op:Operation, estack:seq<Expression>):seq<Expression>
    requires |estack| + StackSizeChangeFromOperation(op) >= 1;
    ensures |HowOperationChangesExpressionStackWhenValid(op, estack)| == |estack| + StackSizeChangeFromOperation(op);
{
    match op
        case OperationPush(i) =>       estack + [ExpInt(i)]
        case OperationColumn =>        estack[..|estack|-1] + [ExpColumn(estack[|estack|-1])]
        case OperationBinary(inst) =>  estack[..|estack| - 2] + [ExpBinary(inst, estack[|estack| - 2], estack[|estack| - 1])]
        case OperationIf =>            estack[..|estack| - 3] + [ExpIf(estack[|estack|-3], estack[|estack| - 2], estack[|estack| - 1])]
}

static lemma Lemma_HowOperationChangesExpressionStackWhenValidEquivalent(op:Operation, estack:seq<Expression>)
    requires |estack| + StackSizeChangeFromOperation(op) >= 1;
    ensures HowOperationChangesExpressionStackWhenValid(op, estack) == HowOperationChangesExpressionStack(op, estack);
{
    if op.OperationPush? {
        assert StackSizeChangeFromOperation(op) == 1;
    } else if op.OperationColumn? {
        assert StackSizeChangeFromOperation(op) == 0;
    } else if op.OperationBinary? {
        assert StackSizeChangeFromOperation(op) == -1;
    } else if op.OperationIf? {
        assert StackSizeChangeFromOperation(op) == -2;
    }
}

static function HowOperationChangesExpressionStack_premium(op:Operation, estack:seq<Expression>):seq<Expression>
    requires |estack| + StackSizeChangeFromOperation(op) >= 1;
    ensures HowOperationChangesExpressionStack_premium(op, estack) == HowOperationChangesExpressionStack(op, estack);
{
    Lemma_HowOperationChangesExpressionStackWhenValidEquivalent(op, estack);
    HowOperationChangesExpressionStackWhenValid(op, estack)
}

static lemma Lemma_PrefixOfValidProgramPrefixIsValid(program:seq<Operation>, k:int)
    requires ProgramPrefixValid(program);
    requires 1 <= k <= |program|;
    ensures ProgramPrefixValid(program[..k]);
{
    var prefix := program[..k];
    assert forall i :: 1 <= i <= |prefix| ==> prefix[..i] == program[..i];
}

static lemma Lemma_PrefixesOfValidProgramPrefixesAreValid(program:seq<Operation>)
    requires ProgramPrefixValid(program);
    ensures forall k :: 1 <= k <= |program| ==> ProgramPrefixValid(program[..k]);
{
    forall k:int | 1 <= k <= |program|
        ensures ProgramPrefixValid(program[..k]);
    {
        Lemma_PrefixOfValidProgramPrefixIsValid(program, k);
    }
}

static lemma Lemma_StackSizeAfterRunningProgramPrefix(program:seq<Operation>)
    requires ProgramPrefixValid(program);
    ensures |ProgramPrefixToExpressionStack(program)| == StackSizeAfterRunning(program);
{
    reveal_ProgramPrefixToExpressionStack();
    Lemma_PrefixesOfValidProgramPrefixesAreValid(program);
    assert program[..|program|] == program;
    assert |program| == 1 ==> StackSizeAfterRunning(program[..0]) + StackSizeChangeFromOperation(program[|program|-1]) >= 1;
    assert |program| > 1 ==> StackSizeAfterRunning(program[..|program|-1]) + StackSizeChangeFromOperation(program[|program|-1]) >= 1;
    if |program| == 0 {
    }
    else if |program| == 1 {
    }
    else {
        calc {
            StackSizeAfterRunning(program);
            StackSizeAfterRunning(program[..|program| - 1]) + StackSizeChangeFromOperation(program[|program| - 1]);
            { Lemma_StackSizeAfterRunningProgramPrefix(program[..|program|-1]); }
            |ProgramPrefixToExpressionStack(program[..|program|-1])| + StackSizeChangeFromOperation(program[|program| - 1]);
        }

        calc {
            |ProgramPrefixToExpressionStack(program[..|program|-1])| + StackSizeChangeFromOperation(program[|program| - 1]);
            == StackSizeAfterRunning(program);
            >= 1;
        }

        calc {
            |ProgramPrefixToExpressionStack(program[..|program|-1])| + StackSizeChangeFromOperation(program[|program| - 1]);
            |HowOperationChangesExpressionStackWhenValid(program[|program|-1], ProgramPrefixToExpressionStack(program[..|program|-1]))|;
            { Lemma_HowOperationChangesExpressionStackWhenValidEquivalent(program[|program|-1], ProgramPrefixToExpressionStack(program[..|program|-1])); }
            |HowOperationChangesExpressionStack(program[|program|-1], ProgramPrefixToExpressionStack(program[..|program|-1]))|;
            |ProgramPrefixToExpressionStack(program)|;
        }
    }
}

static lemma Lemma_ProgramPrefixToExpressionStackContainsOnlyWords(program:seq<Operation>)
    requires ProgramPrefixValid(program);
    ensures ExpressionStackContainsOnlyWords(ProgramPrefixToExpressionStack(program));
{
    Lemma_PrefixesOfValidProgramPrefixesAreValid(program);
    assert program[..|program|] == program;
    assert |program| == 1 ==> StackSizeAfterRunning(program[..0]) + StackSizeChangeFromOperation(program[|program|-1]) >= 1;
    assert |program| > 1 ==> StackSizeAfterRunning(program[..|program|-1]) + StackSizeChangeFromOperation(program[|program|-1]) >= 1;
    reveal_ProgramPrefixToExpressionStack();
    if |program| == 0 {
    }
    else {
        Lemma_ProgramPrefixToExpressionStackContainsOnlyWords(program[..|program|-1]);
    }
}

static lemma Lemma_EvaluateExpressionProducesWord(e:Expression, row:Row)
    requires ExpressionValid(e);
    requires RowValid(row);
    ensures Word32(EvaluateExpression(e, row));
{
    if e.ExpInt? {
    }
    else if e.ExpColumn? {
        Lemma_EvaluateExpressionProducesWord(e.col, row);
    }
    else if e.ExpBinary? {
        Lemma_EvaluateExpressionProducesWord(e.e1, row);
        Lemma_EvaluateExpressionProducesWord(e.e2, row);
        Lemma_ApplyBinaryInstructionProducesWords(e.inst, EvaluateExpression(e.e1, row), EvaluateExpression(e.e2, row));
    }
    else if e.ExpIf? {
        Lemma_EvaluateExpressionProducesWord(e.e_cond, row);
        Lemma_EvaluateExpressionProducesWord(e.e_true, row);
        Lemma_EvaluateExpressionProducesWord(e.e_false, row);
    }
}

static function EvaluateExpression_premium(e:Expression, row:Row):int
    requires ExpressionValid(e);
    requires RowValid(row);
    ensures Word32(EvaluateExpression_premium(e, row));
    ensures EvaluateExpression_premium(e, row) == EvaluateExpression(e, row);
{
    Lemma_EvaluateExpressionProducesWord(e, row);
    EvaluateExpression(e, row)
}

static lemma Lemma_ProgramToExpressionYieldsValidExpression(program:seq<Operation>)
    requires ProgramValid(program);
    ensures ExpressionValid(ProgramToExpression(program));
{
    var estack := ProgramPrefixToExpressionStack(program);
    Lemma_StackSizeAfterRunningProgramPrefix(program);
    assert |estack| == 1;
    Lemma_ProgramPrefixToExpressionStackContainsOnlyWords(program);
}

static function ProgramToExpression_premium(program:seq<Operation>):Expression
    requires ProgramValid(program);
    ensures ExpressionValid(ProgramToExpression_premium(program));
    ensures ProgramToExpression_premium(program) == ProgramToExpression(program);
{
    Lemma_ProgramToExpressionYieldsValidExpression(program);
    ProgramToExpression(program)
}

static lemma Lemma_MessageToProgramCreatesProgramOfOnlyWords(message:seq<int>)
    requires forall i :: 0 <= i < |message| ==> Word32(message[i]);
    ensures ProgramContainsOnlyWords(MessageToProgram(message));
{
    if |message| == 0 {
    }
    else {
        Lemma_MessageToProgramCreatesProgramOfOnlyWords(message[..|message|-1]);
    }
}

static function MessageToProgram_premium(message:seq<int>):seq<Operation>
    requires forall i :: 0 <= i < |message| ==> Word32(message[i]);
    ensures ProgramContainsOnlyWords(MessageToProgram_premium(message));
    ensures MessageToProgram_premium(message) == MessageToProgram(message);
{
    Lemma_MessageToProgramCreatesProgramOfOnlyWords(message);
    MessageToProgram(message)
}

static lemma Lemma_EvaluateProgramProducesWord(program:seq<Operation>, row:Row)
    requires ProgramValid(program);
    requires RowValid(row);
    ensures Word32(EvaluateProgram(program, row));
{
    Lemma_ProgramToExpressionYieldsValidExpression(program);
    Lemma_EvaluateExpressionProducesWord(ProgramToExpression(program), row);
}

static function EvaluateProgram_premium(program:seq<Operation>, row:Row):int
    requires ProgramValid(program);
    requires RowValid(row);
    ensures Word32(EvaluateProgram_premium(program, row));
    ensures EvaluateProgram_premium(program, row) == EvaluateProgram(program, row);
{
    Lemma_EvaluateProgramProducesWord(program, row);
    EvaluateProgram(program, row)
}

//-//////////////////////////////////////////////////////////////////////
//- Methods
//-//////////////////////////////////////////////////////////////////////

static method DetermineIfProgramIsValid(program:seq<Operation>) returns (ret:bool)
    requires ProgramContainsOnlyWords(program);
    ensures ret == ProgramValid(program);
{
    var k := 0;
    var stack_size := 0;

    while k < |program|
        invariant 0 <= k <= |program|;
        invariant stack_size == StackSizeAfterRunning(program[..k]);
        invariant forall i :: 1 <= i <= k ==> StackSizeAfterRunning(program[..i]) >= 1;
    {
        //- stack_size := stack_size + StackSizeChangeFromOperation(program[k]); //- dafnycc TODO: signed arithmetic
        match program[k]
        {
            case OperationPush(i) => stack_size := stack_size + 1;
            case OperationColumn => {}
            case OperationBinary(inst) => stack_size := stack_size - 1;
            case OperationIf => stack_size := stack_size - 2;
        }
        assert program[..k] + [program[k]] == program[..k+1];
        k := k + 1;
        assert StackSizeAfterRunning(program[..k]) == stack_size;
        if stack_size < 1
        {
            return false;
        }
    }

    assert program[..k] == program;
    return stack_size == 1;
}

static method ConvertMessageToProgram(message:seq<int>) returns (ret:seq<Operation>)
    requires forall i :: 0 <= i < |message| ==> Word32(message[i]);
    ensures ProgramContainsOnlyWords(ret);
    ensures ret == MessageToProgram(message);
{
    var i := 0;
    ret := [];

    while i < |message|
        invariant 0 <= i <= |message|;
        invariant ProgramContainsOnlyWords(ret);
        invariant ret == MessageToProgram(message[..i]);
    {
        ret := ret + [WordToOperation(message[i])];
        assert message[..i] + [message[i]] == message[..i+1];
        i := i + 1;
    }

    assert message[..i] == message;
}

static method{:dafnycc_conservative_seq_triggers} RunOneInstructionPush(program:seq<Operation>, row:Row, k:int, stack:seq<int>, ghost estack:seq<Expression>, i:int)
                               returns (new_stack:seq<int>, ghost new_estack:seq<Expression>)
    requires ProgramValid(program);
    requires RowValid(row);
    requires 0 <= k < |program|;
    requires |stack| == StackSizeAfterRunning(program[..k]);
    requires |estack| == |stack|;
    requires estack == ProgramPrefixToExpressionStack(program[..k]);
    requires forall i :: 0 <= i < |stack| ==> Word32(stack[i]);
    requires forall i :: 0 <= i < |estack| ==> ExpressionValid(estack[i]);
    requires forall i :: 0 <= i < |stack| ==> stack[i] == EvaluateExpression_premium(estack[i], row);
    requires program[k] == OperationPush(i);

    ensures |new_stack| == StackSizeAfterRunning(program[..k+1]);
    ensures |new_estack| == |new_stack|;
    ensures new_estack == ProgramPrefixToExpressionStack(program[..k+1]);
    ensures forall i :: 0 <= i < |new_stack| ==> Word32(new_stack[i]);
    ensures forall i :: 0 <= i < |new_estack| ==> ExpressionValid(new_estack[i]);
    ensures forall i :: 0 <= i < |new_stack| ==> new_stack[i] == EvaluateExpression_premium(new_estack[i], row);
{
    assert program[..k+1] == program[..k] + [program[k]];

    new_estack := estack + [ExpInt(i)];
    new_stack := stack + [i];
    reveal_ProgramPrefixToExpressionStack();
}

static method{:dafnycc_conservative_seq_triggers} RunOneInstructionColumn(program:seq<Operation>, row:Row, k:int, stack:seq<int>, ghost estack:seq<Expression>)
                               returns (new_stack:seq<int>, ghost new_estack:seq<Expression>)
    requires ProgramValid(program);
    requires RowValid(row);
    requires 0 <= k < |program|;
    requires |stack| == StackSizeAfterRunning(program[..k]);
    requires |estack| == |stack|;
    requires estack == ProgramPrefixToExpressionStack(program[..k]);
    requires forall i :: 0 <= i < |stack| ==> Word32(stack[i]);
    requires forall i :: 0 <= i < |estack| ==> ExpressionValid(estack[i]);
    requires forall i :: 0 <= i < |stack| ==> stack[i] == EvaluateExpression_premium(estack[i], row);
    requires program[k] == OperationColumn;

    ensures |new_stack| == StackSizeAfterRunning(program[..k+1]);
    ensures |new_estack| == |new_stack|;
    ensures new_estack == ProgramPrefixToExpressionStack(program[..k+1]);
    ensures forall i :: 0 <= i < |new_stack| ==> Word32(new_stack[i]);
    ensures forall i :: 0 <= i < |new_estack| ==> ExpressionValid(new_estack[i]);
    ensures forall i :: 0 <= i < |new_stack| ==> new_stack[i] == EvaluateExpression_premium(new_estack[i], row);
{
    assert program[..k+1] == program[..k] + [program[k]];

    new_estack := estack[..|estack|-1] + [ExpColumn(estack[|estack|-1])];
    new_stack := stack[..|stack|-1] + [ExtractColumn(stack[|stack|-1], row)];
    reveal_ProgramPrefixToExpressionStack();
}

static method{:dafnycc_conservative_seq_triggers} RunOneInstructionBinary(program:seq<Operation>, row:Row, k:int, stack:seq<int>, ghost estack:seq<Expression>, inst:BinaryInstruction)
                               returns (new_stack:seq<int>, ghost new_estack:seq<Expression>)
    requires ProgramValid(program);
    requires RowValid(row);
    requires 0 <= k < |program|;
    requires |stack| == StackSizeAfterRunning(program[..k]);
    requires |estack| == |stack|;
    requires estack == ProgramPrefixToExpressionStack(program[..k]);
    requires forall i :: 0 <= i < |stack| ==> Word32(stack[i]);
    requires forall i :: 0 <= i < |estack| ==> ExpressionValid(estack[i]);
    requires forall i :: 0 <= i < |stack| ==> stack[i] == EvaluateExpression_premium(estack[i], row);
    requires program[k] == OperationBinary(inst);

    ensures |new_stack| == StackSizeAfterRunning(program[..k+1]);
    ensures |new_estack| == |new_stack|;
    ensures new_estack == ProgramPrefixToExpressionStack(program[..k+1]);
    ensures forall i :: 0 <= i < |new_stack| ==> Word32(new_stack[i]);
    ensures forall i :: 0 <= i < |new_estack| ==> ExpressionValid(new_estack[i]);
    ensures forall i :: 0 <= i < |new_stack| ==> new_stack[i] == EvaluateExpression_premium(new_estack[i], row);
{
    assert program[..k+1] == program[..k] + [program[k]];

    new_estack := estack[..|estack| - 2] + [ExpBinary(inst, estack[|estack| - 2], estack[|estack| - 1])];
    var result := ApplyBinaryInstructionImpl(inst, stack[|stack| - 2], stack[|stack| - 1]);
    new_stack := stack[..|stack| - 2] + [result];
    reveal_ProgramPrefixToExpressionStack();
}

static method{:dafnycc_conservative_seq_triggers} RunOneInstructionIf(program:seq<Operation>, row:Row, k:int, stack:seq<int>, ghost estack:seq<Expression>)
                               returns (new_stack:seq<int>, ghost new_estack:seq<Expression>)
    requires ProgramValid(program);
    requires RowValid(row);
    requires 0 <= k < |program|;
    requires |stack| == StackSizeAfterRunning(program[..k]);
    requires |estack| == |stack|;
    requires estack == ProgramPrefixToExpressionStack(program[..k]);
    requires forall i :: 0 <= i < |stack| ==> Word32(stack[i]);
    requires forall i :: 0 <= i < |estack| ==> ExpressionValid(estack[i]);
    requires forall i :: 0 <= i < |stack| ==> stack[i] == EvaluateExpression_premium(estack[i], row);
    requires program[k] == OperationIf;

    ensures |new_stack| == StackSizeAfterRunning(program[..k+1]);
    ensures |new_estack| == |new_stack|;
    ensures new_estack == ProgramPrefixToExpressionStack(program[..k+1]);
    ensures forall i :: 0 <= i < |new_stack| ==> Word32(new_stack[i]);
    ensures forall i :: 0 <= i < |new_estack| ==> ExpressionValid(new_estack[i]);
    ensures forall i :: 0 <= i < |new_stack| ==> new_stack[i] == EvaluateExpression_premium(new_estack[i], row);
{
    assert program[..k+1] == program[..k] + [program[k]];

    new_estack := estack[..|estack| - 3] + [ExpIf(estack[|estack|-3], estack[|estack| - 2], estack[|estack| - 1])];
    new_stack := stack[..|stack| - 3] + [if stack[|stack|-3] != 0 then stack[|stack| - 2] else stack[|stack| - 1]];
    reveal_ProgramPrefixToExpressionStack();
}

static method{:dafnycc_conservative_seq_triggers} RunOneInstruction(program:seq<Operation>, row:Row, k:int, stack:seq<int>, ghost estack:seq<Expression>)
                               returns (new_stack:seq<int>, ghost new_estack:seq<Expression>)
    requires ProgramValid(program);
    requires RowValid(row);
    requires 0 <= k < |program|;
    requires |stack| == StackSizeAfterRunning(program[..k]);
    requires |estack| == |stack|;
    requires estack == ProgramPrefixToExpressionStack(program[..k]);
    requires forall i :: 0 <= i < |stack| ==> Word32(stack[i]);
    requires forall i :: 0 <= i < |estack| ==> ExpressionValid(estack[i]);
    requires forall i :: 0 <= i < |stack| ==> stack[i] == EvaluateExpression_premium(estack[i], row);

    ensures |new_stack| == StackSizeAfterRunning(program[..k+1]);
    ensures |new_estack| == |new_stack|;
    ensures new_estack == ProgramPrefixToExpressionStack(program[..k+1]);
    ensures forall i :: 0 <= i < |new_stack| ==> Word32(new_stack[i]);
    ensures forall i :: 0 <= i < |new_estack| ==> ExpressionValid(new_estack[i]);
    ensures forall i :: 0 <= i < |new_stack| ==> new_stack[i] == EvaluateExpression_premium(new_estack[i], row);
{
    assert program[..k+1] == program[..k] + [program[k]];

    match program[k]
    {
        case OperationPush(i) =>
            new_stack, new_estack := RunOneInstructionPush(program, row, k, stack, estack, i);

        case OperationColumn =>
            new_stack, new_estack := RunOneInstructionColumn(program, row, k, stack, estack);

        case OperationBinary(inst) =>
            new_stack, new_estack := RunOneInstructionBinary(program, row, k, stack, estack, inst);

        case OperationIf =>
            new_stack, new_estack := RunOneInstructionIf(program, row, k, stack, estack);
    }
}

static lemma lemma_EmptyProgramPrefixToExpressionStack(program:seq<Operation>)
    ensures ProgramPrefixToExpressionStack(program[..0]) == [];
{
    reveal_ProgramPrefixToExpressionStack();
}

static method RunProgram(program:seq<Operation>, row:Row) returns(ret:int)
    requires ProgramValid(program);
    requires RowValid(row);
    ensures ret == EvaluateExpression_premium(ProgramToExpression_premium(program), row);
    ensures Word32(ret);
{
    var stack:seq<int> := [];
    var k:int := 0;

    ghost var estack:seq<Expression> := [];

    Lemma_PrefixesOfValidProgramPrefixesAreValid(program);
    lemma_EmptyProgramPrefixToExpressionStack(program);
    while (k < |program|)
        invariant 0 <= k <= |program|;
        invariant |stack| == StackSizeAfterRunning(program[..k]);
        invariant |estack| == |stack|;
        invariant estack == ProgramPrefixToExpressionStack(program[..k]);
        invariant forall i :: 0 <= i < |stack| ==> Word32(stack[i]);
        invariant forall i :: 0 <= i < |estack| ==> ExpressionValid(estack[i]);
        invariant forall i :: 0 <= i < |stack| ==> stack[i] == EvaluateExpression_premium(estack[i], row);
    {
        stack, estack := RunOneInstruction(program, row, k, stack, estack);
        k := k + 1;
    }

    assert program == program[..|program|];
    assert |stack| == 1;
    ret := stack[0];
}
