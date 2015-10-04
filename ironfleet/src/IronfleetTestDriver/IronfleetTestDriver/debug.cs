using System.Numerics;

public partial class @__default
{

    public static BigInteger BIFake(int val, int count)
    {
        if (count == 1)
        {
            return val;
        }
        else
        {
            return BIFake(val, count - 1) * BigInteger.Pow(2, 32) + val;
        }
    }

    //  public static void BITest(@BigNat ironB, @BigNat ironM, @BigNat ironR)
    //  {
    ////      BigInteger B = BIFake(C.bval, C.bcount);
    ////      BigInteger E = C.e;
    ////      BigInteger M = BIFake(C.mval, C.mcount);
    ////
    ////      System.Console.WriteLine("C# B: " + B);
    ////      System.Console.WriteLine("Iron B: " + TestDecode(ironB, 0));
    ////      BigInteger R = BigInteger.ModPow(B, E, M);
    ////      System.Console.WriteLine("C# ModExp: " + R);
    ////      System.Console.WriteLine("Iron ModExp: " + TestDecode(ironR, 0));
    ////
    ////      @BigNat ironMod; @BigNat ironDiv;
    ////      @__default.@BigNatDiv(ironB, @ironM, out ironDiv, out ironMod);
    ////      System.Console.WriteLine("  C# B % M: " + BigInteger.Remainder(B, M));
    ////      System.Console.WriteLine("Iron B % M: " + TestDecode(ironMod, 0));
    //  }

    //  public static BigInteger TestDecode(@BigNat bn, int skip)
    //  {
    //      if (bn.dtor_words.Elements.Length <= skip)
    //      {
    //          return 0;
    //      }
    //      else
    //      {
    //          return TestDecode(bn, skip + 1) * BigInteger.Pow(2, 32) + bn.dtor_words.Elements[skip];
    //      }
    //  }
    //  public class C
    //  {
    //      public const int bval = 15;
    //      public const int bcount = 63;
    //      public const int e = 65537;
    //      public const int mval = 220;
    //      public const int mcount = 64;
    //  }

}
