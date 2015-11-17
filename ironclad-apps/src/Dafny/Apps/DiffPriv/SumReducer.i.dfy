include "SumReducer.s.dfy"
include "Mapper.i.dfy"

static method ComputeSum (db:seq<Row>, program:seq<Operation>, row_min:int, row_max:int,
                          answer_units:int, answer_min:int, answer_max:int) returns (answer:int, ghost sum:int)
    requires DatabaseValid(db);
    requires ProgramValid(program);
    requires Word32(row_min);
    requires Word32(row_max);
    requires Word32(answer_units);
    requires Word32(answer_min);
    requires Word32(answer_max);
    requires row_min <= row_max;
    requires answer_units > 0;
    requires Word32(answer_units * 2);
    requires answer_min <= answer_max;
    ensures sum == MapperSum(db, program, row_min, row_max);
    ensures Word32(answer);
    ensures answer == Clip(Scale(sum, answer_units), answer_min, answer_max);
{
    sum := 0;
    ghost var scaled_sum:int := 0;

    var clipped_scaled_sum:int := 0;
    var total_remainder:int := 0;

    lemma_mul_is_mul_boogie(answer_units, scaled_sum);

    var which_row := 0;
    while which_row < |db|
        invariant 0 <= which_row <= |db|;
        invariant Word32(clipped_scaled_sum);
        invariant sum == MapperSum(db[..which_row], program, row_min, row_max);
        invariant sum == answer_units * scaled_sum + total_remainder;
        invariant clipped_scaled_sum == (if scaled_sum < power2(32) then scaled_sum else power2(32) - 1);
        invariant 0 <= total_remainder < answer_units;
        invariant sum >= 0;
    {
        var row_value := RunProgram(program, db[which_row]);
        var clipped_value := ClipWord32(row_value, row_min, row_max);

        var scaled_value := clipped_value / answer_units;
        var scaling_remainder := clipped_value % answer_units;
        lemma_div_is_ordered_by_denominator(clipped_value, 1, answer_units);
        lemma_div_by_one_is_identity(clipped_value);
        lemma_div_pos_is_pos(clipped_value, answer_units);

        ghost var old_sum := sum;
        ghost var old_scaled_sum := scaled_sum;
        ghost var old_total_remainder := total_remainder;

        sum := sum + clipped_value;
        scaled_sum := scaled_sum + scaled_value;
        clipped_scaled_sum := SaturatingAdd(clipped_scaled_sum, scaled_value);

        lemma_mod_remainder_pos_specific(clipped_value, answer_units);
        assert 0 <= scaling_remainder < answer_units;
        assert Word32(total_remainder + scaling_remainder); //- so there's no need to use SaturatingAdd to add these
        total_remainder := total_remainder + scaling_remainder;

        calc {
            answer_units * scaled_sum + total_remainder;
            answer_units * (old_scaled_sum + scaled_value) + total_remainder;
            answer_units * (old_scaled_sum + scaled_value) + (old_total_remainder + scaling_remainder);
            { lemma_mul_is_distributive_add(answer_units, old_scaled_sum, scaled_value); }
            (answer_units * old_scaled_sum) + (answer_units * scaled_value) + (old_total_remainder + scaling_remainder);
            (answer_units * old_scaled_sum) + old_total_remainder + (answer_units * scaled_value) + scaling_remainder;
            old_sum + (answer_units * scaled_value) + scaling_remainder;
            { lemma_fundamental_div_mod(clipped_value, answer_units); }
            old_sum + clipped_value;
            sum;
        }

        if total_remainder >= answer_units {
            ghost var intermediate_scaled_sum := scaled_sum;
            ghost var intermediate_total_remainder := total_remainder;
            scaled_sum := scaled_sum + 1;
            clipped_scaled_sum := SaturatingAdd(clipped_scaled_sum, 1);
            total_remainder := total_remainder - answer_units;
            calc {
                answer_units * scaled_sum + total_remainder;
                answer_units * (intermediate_scaled_sum + 1) + total_remainder;
                { lemma_mul_is_distributive_add(answer_units, intermediate_scaled_sum, 1); lemma_mul_is_mul_boogie(answer_units, 1); }
                answer_units * intermediate_scaled_sum + answer_units * 1 + total_remainder;
                answer_units * intermediate_scaled_sum + answer_units + total_remainder;
                answer_units * intermediate_scaled_sum + answer_units + intermediate_total_remainder - answer_units;
                answer_units * intermediate_scaled_sum + intermediate_total_remainder;
                sum;
            }
        }

        which_row := which_row + 1;
        assert db[..which_row][..|db[..which_row]|-1] == db[..which_row-1];
    }

    var extra:int := (if total_remainder * 2 >= answer_units then 1 else 0);
    clipped_scaled_sum := SaturatingAdd(clipped_scaled_sum, extra);

    assert db[..which_row] == db;
    lemma_mul_is_commutative(answer_units, scaled_sum);
    lemma_fundamental_div_mod_converse(sum, answer_units, scaled_sum, total_remainder);
    assert sum / answer_units == scaled_sum;
    assert sum % answer_units == total_remainder;
    calc {
        Scale(MapperSum(db, program, row_min, row_max), answer_units);
        Scale(sum, answer_units);
        (sum / answer_units) + (if (sum % answer_units) * 2 >= answer_units then 1 else 0);
        (sum / answer_units) + extra;
        scaled_sum + extra;
    }

    assert db[..which_row] == db;
    answer := ClipWord32(clipped_scaled_sum, answer_min, answer_max);
}

//-////////////////////////////////////
//- Helpers
//-////////////////////////////////////

static function method SaturatingAdd(x:int, y:int):int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(SaturatingAdd(x, y));
    ensures SaturatingAdd(x, y) == if x + y < power2(32) then x + y else power2(32) - 1;
{
    lemma_2toX();
    if x + y <= 0xFFFFFFFF then x + y else 0xFFFFFFFF
}

static function method ClipWord32 (value:int, min:int, max:int) : int
    requires Word32(value);
    requires Word32(min);
    requires Word32(max);
    requires min <= max;
    ensures ClipWord32(value, min, max) == Clip(value, min, max);
{
    if value < min then min else if value > max then max else value
}
