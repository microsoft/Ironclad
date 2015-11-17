static function method Tally_TestDigits() : int { 1 }
static function method Tally_BigNatSub() : int { 2 }
static function method Tally_BigNatModExpCalls() : int { 3 }
static function method Tally_BigNatModExpWhileLoops() : int { 4 }
static function method Tally_BigNatDivCalls() : int { 5 }
static function method Tally_BigNatDivWhileLoops() : int { 6 }

static function method Tally_FatNatModExp() : int { 7 }
static function method Tally_FatNatMul() : int { 8 }
static function method Tally_FatNatMod() : int { 9 }
static function method Tally_MillerRabinTest() : int { 10 }

//- Mark these 'ghost' unless profiling to avoid creating runtime code
//- in real build.
static ghost method ResetTally() {}
static ghost method ProfileTally(category:int, value:int) {}
static ghost method DisplayTally() {}

