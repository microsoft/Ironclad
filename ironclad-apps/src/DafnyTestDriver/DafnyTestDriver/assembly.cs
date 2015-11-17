using System.Numerics;
using System.Diagnostics;
using System.Text;

    public partial class @__default
    {
        public static BigInteger @asm__BitwiseXor(BigInteger a, BigInteger b)
        {
            return a ^ b;
        }
        public static BigInteger @asm__BitwiseAnd(BigInteger a, BigInteger b)
        {
            return a & b;
        }
        public static BigInteger @asm__BitwiseOr(BigInteger a, BigInteger b)
        {
            return a | b;
        }
        public static BigInteger @asm__LeftShift(BigInteger a, BigInteger b)
        {
            BigInteger mask = 1;    
            mask = mask << 32;
            mask -= 1;
            return mask & (a << (int)b);
        }
        public static BigInteger @asm__RightShift(BigInteger a, BigInteger b)
        {
            return a >> (int)b;
        }
        public static BigInteger @asm__BitwiseNot(BigInteger a)
        {
            return ~a;
        }
        public static BigInteger @asm__RotateRight(BigInteger a, BigInteger b)
        {
            BigInteger mask = 1;    
            mask = mask << 32;
            mask -= 1;
            int amount = (int)b;
            return mask & ((a >> amount) | (a << (32 - amount)));
        }
        public static BigInteger @asm__RotateLeft(BigInteger a, BigInteger b)
        {
            BigInteger mask = 1;    
            mask = mask << 32;
            mask -= 1;
            int amount = (int)b;
            return mask & ((a << amount) | (a >> (32 - amount)));
        }

        static BigInteger two = 2;
        static BigInteger pow32 = BigInteger.Pow(two, 32);

        static void Word32(BigInteger a)
        {
            Debug.Assert(0 <= a);
            Debug.Assert(a < pow32);
        }
        public static BigInteger @asm__Add(BigInteger a, BigInteger b)
        {
            Word32(a);
            Word32(b);
            profiler.ProfileTally(1000, 1); 

            BigInteger result = (a + b) % pow32;
            Debug.Assert(((a + b) - (a+b >= pow32 ? pow32 : 0)).Equals(result));
            return result;
        }
        public static BigInteger @asm__Sub(BigInteger a, BigInteger b)
        {
            Word32(a);
            Word32(b);
            profiler.ProfileTally(1001, 1);
            BigInteger result = (a - b + pow32) % pow32;
            Debug.Assert((a - b + ((b>a) ? pow32 : 0)).Equals(result));
            return result;
        }
        public static void @method__Mul(BigInteger a, BigInteger b, out BigInteger hi, out BigInteger lo)
        {
            Word32(a);
            Word32(b);
            profiler.ProfileTally(1002, 1);
            @asm__Mul64(a, b, out hi, out lo);
        }
        public static void @asm__Mul64(BigInteger a, BigInteger b, out BigInteger hi, out BigInteger lo)
        {
            Word32(a);
            Word32(b);
            profiler.ProfileTally(1003, 1);
            BigInteger pow64 = 2;
            pow64 = BigInteger.Pow(pow64, 64);
            BigInteger product = (a * b) % pow64;
            hi = product / pow32;
            lo = product % pow32;
            Debug.Assert((hi * pow32 + lo).Equals(a * b));
        }
        public static BigInteger @asm__Mul(BigInteger a, BigInteger b)
        {
            Word32(a);
            Word32(b);
            profiler.ProfileTally(1004, 1);
            BigInteger hi, lo;
            @method__Mul(a, b, out hi, out lo);
            return lo;
        }
        public static BigInteger @asm__Div(BigInteger a, BigInteger b)
        {
            Word32(a);
            Word32(b);
            profiler.ProfileTally(1005, 1);
            return BigInteger.Divide(a,b);
        }
        public static BigInteger @asm__Mod(BigInteger a, BigInteger b)
        {
            Word32(a);
            Word32(b);
            profiler.ProfileTally(1006, 1);
            return BigInteger.Remainder(a,b);
        }
        public static void @method__DivMod(BigInteger zero/*?*/, BigInteger a, BigInteger b, out BigInteger div, out BigInteger mod)
        {
            Word32(a);
            Word32(b);
            div = BigInteger.DivRem(a, b, out mod);
            Debug.Assert((b * div + mod).Equals(a));
        }
        public static void @asm__Rdtsc(out BigInteger hi, out BigInteger lo)
        {
            
            hi = 0;
            lo = 0;
        }
        public void @asm__declassify__result(BigInteger @concrete, out BigInteger @pub__result)
        {
            @pub__result = @concrete;
        }
        public static void @GetBootloaderArgWord(BigInteger @index, out BigInteger @result)
        {
            @result = 0;
        }
        System.Random rng = new System.Random();

        public void display_seq(BigInteger[] x)
        {
            StringBuilder sb = new StringBuilder();

            foreach (BigInteger xs in x)
            {
                sb.Append(string.Format("{0,2:X2}", (int)xs));
            }
            System.Console.WriteLine(sb.ToString());
        }
        public void @get__random(BigInteger countb, out Dafny.Sequence<BigInteger> @result)
        {
            int counti = (int)countb;
            
            BigInteger[] bary = new BigInteger[counti];
            for (int i=0; i<counti; i++)
            {
                int rand = rng.Next() & 0xff;
                bary[i] = new BigInteger(rand);
            }
            @result = new Dafny.Sequence<BigInteger>(bary);
            display_seq(bary);
        }
        public static void InitK__SHA256__0__to__10(BigInteger[] @result)
        {
            Debug.Assert(false);
            @result = null;
        }
        public static void @ComputeWsForBlockStep2__SHA256(BigInteger[] @M, BigInteger @words, BigInteger[] @H, BigInteger[] @W, BigInteger[] @Ks, BigInteger @num__blocks, BigInteger @currentBlock)
        {
            Debug.Assert(false);
        }
        public static void debug__print(BigInteger m1, BigInteger m2)
        {
            System.Console.WriteLine(string.Format("debug_print {0,2:X} {1,8:X}", (int) m1, (int) m2));
        }
    }
