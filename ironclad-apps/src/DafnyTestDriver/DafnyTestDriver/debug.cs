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
          return BIFake(val, count - 1) * BigInteger.Pow(2,32) + val;
      }
  }



//
//
//
////
//
//
//
//
//
////
//
//
//
//






















}
