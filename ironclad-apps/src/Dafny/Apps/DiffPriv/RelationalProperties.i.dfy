include "SumReducer.i.dfy"

//////////////////////////////////////////////

//////////////////////////////////////////////

static lemma Lemma_SensitivityOfMapperSumSpecific(db1:seq<Row>, db2:seq<Row>, diff_row:int,
                                                  program:seq<Operation>, row_min:int, row_max:int)
    requires DatabaseValid(db1);
    requires DatabaseValid(db2);
    requires DatabasesIdenticalExceptForOneRow(db1, db2, diff_row);
    requires ProgramValid(program);
    requires row_min <= row_max;
    ensures row_min - row_max <= MapperSum(db1, program, row_min, row_max) - MapperSum(db2, program, row_min, row_max) <= row_max - row_min;
    decreases |db1|;
{
    if |db1| > 0
    {
        if diff_row == |db1| - 1
        {
            assert forall i:int :: 0 <= i < diff_row ==> db1[i] == db2[i];
            assert db1[..diff_row] == db2[..diff_row];
        }
        else
        {
             Lemma_SensitivityOfMapperSumSpecific(db1[..|db1|-1], db2[..|db2|-1], diff_row, program, row_min, row_max);
        }
    }
}

static lemma Lemma_SensitivityOfMapperSum(program:seq<Operation>, row_min:int, row_max:int)
    requires ProgramValid(program);
    requires row_min <= row_max;
    ensures forall db1:seq<Row>, db2:seq<Row> ::
        DatabaseValid(db1) && DatabaseValid(db2) && DatabasesSimilar(db1, db2) ==>
        row_min - row_max <= MapperSum(db1, program, row_min, row_max) - MapperSum(db2, program, row_min, row_max) <= row_max - row_min;
{
    forall db1:seq<Row>, db2:seq<Row>, diff_row:int |
           DatabaseValid(db1) && DatabaseValid(db2) && DatabasesIdenticalExceptForOneRow(db1, db2, diff_row)
        ensures row_min - row_max <= MapperSum(db1, program, row_min, row_max) - MapperSum(db2, program, row_min, row_max) <= row_max - row_min;
    {
        Lemma_SensitivityOfMapperSumSpecific(db1, db2, diff_row, program, row_min, row_max);
    }
}

static lemma Lemma_SensitivityOfComputeSumSpecific(db1:seq<Row>, db2:seq<Row>, diff_row:int, program:seq<Operation>,
                                                   row_min:int, row_max:int, answer_units:int, answer_min:int, answer_max:int, delta:int)
    requires DatabaseValid(db1);
    requires DatabaseValid(db2);
    requires DatabasesIdenticalExceptForOneRow(db1, db2, diff_row);
    requires ProgramValid(program);
    requires row_min <= row_max;
    requires answer_units > 0;
    requires answer_min <= answer_max;
    requires delta == DivideRoundingUp(row_max - row_min, answer_units);
    ensures  -delta <= Clip(Scale(MapperSum(db1, program, row_min, row_max), answer_units), answer_min, answer_max) -
                       Clip(Scale(MapperSum(db2, program, row_min, row_max), answer_units), answer_min, answer_max) <= delta;
    decreases |db1|;
{
    Lemma_SensitivityOfMapperSumSpecific(db1, db2, diff_row, program, row_min, row_max);
    assert -(row_max-row_min) <= MapperSum(db1, program, row_min, row_max) - MapperSum(db2, program, row_min, row_max) <= row_max - row_min;
    Lemma_EffectOfScaleOnDifference(MapperSum(db1, program, row_min, row_max), MapperSum(db2, program, row_min, row_max),
                                    row_max - row_min, answer_units, delta);
    assert -delta <= Scale(MapperSum(db1, program, row_min, row_max), answer_units) - Scale(MapperSum(db2, program, row_min, row_max), answer_units) <= delta;
    Lemma_EffectOfClipOnDifference(Scale(MapperSum(db1, program, row_min, row_max), answer_units),
                                   Scale(MapperSum(db2, program, row_min, row_max), answer_units),
                                   delta, answer_min, answer_max);
    assert -delta <= Clip(Scale(MapperSum(db1, program, row_min, row_max), answer_units), answer_min, answer_max) - Clip(Scale(MapperSum(db2, program, row_min, row_max), answer_units), answer_min, answer_max) <= delta;
}

static lemma Lemma_SensitivityOfComputeSum(program:seq<Operation>, row_min:int, row_max:int, answer_units:int, answer_min:int,
                                           answer_max:int, delta:int)
    requires ProgramValid(program);
    requires row_min <= row_max;
    requires answer_units > 0;
    requires answer_min <= answer_max;
    requires delta == DivideRoundingUp(row_max - row_min, answer_units);
    ensures forall db1:seq<Row>, db2:seq<Row> ::
        DatabaseValid(db1) && DatabaseValid(db2) && DatabasesSimilar(db1, db2) ==>
        -delta <= Clip(Scale(MapperSum(db1, program, row_min, row_max), answer_units), answer_min, answer_max) -
                  Clip(Scale(MapperSum(db2, program, row_min, row_max), answer_units), answer_min, answer_max) <= delta;
{
    forall db1:seq<Row>, db2:seq<Row>, diff_row:int |
           DatabaseValid(db1) && DatabaseValid(db2) && DatabasesIdenticalExceptForOneRow(db1, db2, diff_row)
        ensures -delta <= Clip(Scale(MapperSum(db1, program, row_min, row_max), answer_units), answer_min, answer_max) -
                          Clip(Scale(MapperSum(db2, program, row_min, row_max), answer_units), answer_min, answer_max) <= delta;
    {
        Lemma_SensitivityOfComputeSumSpecific(db1, db2, diff_row, program, row_min, row_max, answer_units, answer_min, answer_max, delta);
    }
}

static lemma Lemma_EffectOfScaleOnDifference (v1:int, v2:int, delta:int, d:int, scaled_delta:int)
    requires delta >= 0;
    requires d > 0;
    requires -delta <= v1 - v2 <= delta;
    requires scaled_delta == DivideRoundingUp(delta, d);
    ensures -scaled_delta <= Scale(v1, d) - Scale(v2, d) <= scaled_delta;
{
    var sv1 := Scale(v1, d);
    var sv2 := Scale(v2, d);

    Lemma_ScaledValueOffByNoMoreThanHalf(v1, d, sv1);
    Lemma_ScaledValueOffByNoMoreThanHalf(v2, d, sv2);
    Lemma_TwoThingsLessThanHalfDifferByLessThanWhole(d * sv1 - v1, d * sv2 - v2, d);
    assert -d < (d * sv1 - v1) - (d * sv2 - v2) < d;
    assert -d < (d * sv1) - (d * sv2) - (v1 - v2) < d;
    lemma_mul_is_distributive_sub(d, sv1, sv2);
    assert -d < d * (sv1 - sv2) - (v1 - v2) < d;
    assert -d + (v1 - v2) < d * (sv1 - sv2) < d + (v1 - v2);
    assert -(d+delta) < d * (sv1 - sv2) < d + delta;
    Lemma_ScalingDivision(sv1 - sv2, d, delta, scaled_delta);
}

static lemma Lemma_EffectOfClipOnDifference (v1:int, v2:int, delta:int, min:int, max:int)
    requires delta >= 0;
    requires -delta <= v1 - v2 <= delta;
    requires min <= max;
    ensures -delta <= Clip(v1, min, max) - Clip(v2, min, max) <= delta;
{
}

static lemma Lemma_ScaledValueOffByNoMoreThanHalf (x:int, d:int, sx:int)
    requires d > 0;
    requires sx == Scale(x, d);
    ensures -d < 2 * (d * sx - x) <= d;
{
    var q := x / d;
    var r := x % d;
    lemma_fundamental_div_mod(x, d);

    lemma_mod_remainder_specific(x, d);

    if r * 2 >= d {
        calc {
            2 * (d * sx - x);
            2 * (d * (q + 1) - x);
            { lemma_mul_is_distributive_add(d, q, 1); lemma_mul_is_mul_boogie(d, 1); }
            2 * (d * q + d * 1 - x);
            2 * (d * q + d - x);
            2 * (d * q + r + d - r - x);
            2 * (d - r);
        }
    }
}

static lemma Lemma_TwoThingsLessThanHalfDifferByLessThanWhole (x1:int, x2:int, y:int)
    requires -y < x1 * 2 <= y;
    requires -y < x2 * 2 <= y;
    ensures -y < x1 - x2 < y;
{
}

static lemma Lemma_ScalingDivision (x:int, d:int, delta:int, scaled_delta:int)
    requires delta >= 0;
    requires d > 0;
    requires -(d+delta) < d * x < d+delta;
    requires scaled_delta == DivideRoundingUp(delta, d);
    ensures -scaled_delta <= x <= scaled_delta;
{
    Lemma_DivideRoundingUpHasLimit(delta, d);
    assert delta <= d * scaled_delta < d + delta;
    lemma_mul_is_commutative_forall();

    if x > scaled_delta {
        calc ==> {
            true;
            x-1 >= scaled_delta;
            { lemma_mul_inequality(scaled_delta, x-1, d); }
            d * (x-1) >= d * scaled_delta;
            d * (x-1) >= delta;
            { lemma_mul_is_distributive_sub(d, x, 1); lemma_mul_is_mul_boogie(d, 1); }
            d * x - d >= delta;
            d * x >= delta + d;
            false;
        }
    }
    else if x < -scaled_delta {
        lemma_mul_is_mul_boogie(-1, scaled_delta);
        lemma_mul_is_mul_boogie(-1, d);
        lemma_mul_is_mul_boogie(-1, d * scaled_delta);
        lemma_mul_is_mul_boogie(d, -1);
        calc ==> {
            true;
            x+1 <= -scaled_delta;
            { lemma_mul_inequality(x+1, -scaled_delta, d); }
            d * (x+1) <= d * (-scaled_delta);
            d * (x+1) <= d * (-1 * scaled_delta);
            { lemma_mul_is_associative(d, -1, scaled_delta); }
            d * (x+1) <= (d * -1) * scaled_delta;
            d * (x+1) <= (-1 * d) * scaled_delta;
            { lemma_mul_is_associative(-1, d, scaled_delta); }
            d * (x+1) <= -1 * (d * scaled_delta);
            d * (x+1) <= -1 * delta;
            { lemma_mul_is_mul_boogie(-1, delta); }
            d * (x+1) <= -delta;
            { lemma_mul_is_distributive_add(d, x, 1); lemma_mul_is_mul_boogie(d, 1); }
            d * x + d <= -delta;
            d * x <= -(d+delta);
            false;
        }
    }
}

static lemma Lemma_DivideRoundingUpHasLimit (x:int, d:int)
    requires x >= 0;
    requires d > 0;
    ensures x <= d * DivideRoundingUp(x, d) < x + d;
{
    lemma_fundamental_div_mod(x, d);
    if x % d != 0 {
        calc {
            d * DivideRoundingUp(x, d);
            d * (x/d + 1);
            { lemma_mul_is_distributive_add(d, x/d, 1); lemma_mul_is_mul_boogie(d, 1); }
            d * (x/d) + d;
        }
        lemma_mod_remainder_specific(x, d);
    }
}
