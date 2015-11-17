include "Math.s.dfy"
include "Mapper.s.dfy"

static function MapperSum (db:seq<Row>, program:seq<Operation>, row_min:int, row_max:int) : int
    requires DatabaseValid(db);
    requires ProgramValid(program);
    requires row_min <= row_max;
{
    if |db| == 0 then
        0
    else
        MapperSum(db[..|db|-1], program, row_min, row_max) + Clip(EvaluateProgram(program, db[|db|-1]), row_min, row_max)
}
