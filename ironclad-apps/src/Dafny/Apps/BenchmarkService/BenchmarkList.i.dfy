//-
//- List of benchmarks we support.
//-
static function method BenchmarkNothing():int { 0 }
static function method BenchmarkSha1():int { 1 }
static function method BenchmarkSha256():int { 2 }
static function method BenchmarkRsaKeyGen():int { 3 }
static function method BenchmarkRsaEncrypt():int { 4 }
static function method BenchmarkRsaDecrypt():int { 5 }
static function method BenchmarkRsaDigestedSign():int { 6 }
static function method BenchmarkRsaDigestedVerify():int { 7 }
static function method BenchmarkTpmExtractRandom():int { 8 }
static function method BenchmarkByteSeqToWordSeq():int { 9 }
static function method BenchmarkWordSeqToByteSeq():int { 10 }
static function method BenchmarkSha1Raw():int { 11 }
static function method BenchmarkSha256Raw():int { 12 }
static function method BenchmarkDuplicateArray():int { 13 }
static function method BenchmarkFatAdd():int { 14 }
static function method BenchmarkFatAddSlowly():int { 15 }
static function method BenchmarkMax():int { 16 }
